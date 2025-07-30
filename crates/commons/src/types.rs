use crate::types::ir::Type;
use cranelift_codegen::ir;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::collections::HashSet;
use std::fs;
use toml;

#[derive(Debug, Clone, Deserialize, PartialEq, Hash, Eq)]
#[serde(rename_all = "snake_case")]
pub enum ResultType {
    Same,
    Conditional,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Hash, Eq)]
#[serde(rename_all = "snake_case")]
pub enum OperandType {
    I8,
    I16,
    I32,
    I64,
    I128,
    F16,
    F32,
    F64,
    I8x16,
    I16x8,
    I32x4,
    I64x2,
    F16x8,
    F32x4,
    F64x2,
}

impl OperandType {
    pub fn to_cranelift_type(&self) -> Type {
        match self {
            OperandType::I8 => ir::types::I8,
            OperandType::I16 => ir::types::I16,
            OperandType::I32 => ir::types::I32,
            OperandType::I64 => ir::types::I64,
            OperandType::I128 => ir::types::I128,
            OperandType::F16 => ir::types::F16,
            OperandType::F32 => ir::types::F32,
            OperandType::F64 => ir::types::F64,
            OperandType::I8x16 => ir::types::I8X16,
            OperandType::I16x8 => ir::types::I16X8,
            OperandType::I32x4 => ir::types::I32X4,
            OperandType::I64x2 => ir::types::I64X2,
            OperandType::F16x8 => ir::types::F16X8,
            OperandType::F32x4 => ir::types::F32X4,
            OperandType::F64x2 => ir::types::F64X2,
        }
    }
}

#[derive(Debug, Deserialize, Clone)]
pub struct Instruction {
    pub name: String,
    pub modes: Option<Vec<Mode>>,
}

#[derive(Debug, Deserialize, Clone, Eq, Hash, PartialEq)]
pub struct Mode {
    pub name: String,
    pub operand_types: Option<Vec<OperandType>>,
    pub arg0_types: Option<Vec<OperandType>>,
    pub arg1_types: Option<Vec<OperandType>>,
    pub result_type: Option<ResultType>,
    pub memory: Option<bool>,
}

impl Mode {
    pub fn intersect(&self, other: &Mode) -> Option<Mode> {
        if self.name != other.name {
            return None;
        }

        let operand_types = intersect_optional_vec(&self.operand_types, &other.operand_types);

        let arg0_types = intersect_optional_vec(&self.arg0_types, &other.arg0_types);

        let arg1_types = intersect_optional_vec(&self.arg1_types, &other.arg1_types);

        let result_type = match (&self.result_type, &other.result_type) {
            (Some(a), Some(b)) if a == b => Some(a.clone()),
            (None, None) => None,
            _ => return None,
        };

        let memory = match (&self.memory, &other.memory) {
            (Some(a), Some(b)) if a == b => Some(*a),
            (None, None) => None,
            _ => return None,
        };

        Some(Mode {
            name: self.name.clone(),
            operand_types,
            arg0_types,
            arg1_types,
            result_type,
            memory,
        })
    }
}

fn intersect_optional_vec<T>(vec1: &Option<Vec<T>>, vec2: &Option<Vec<T>>) -> Option<Vec<T>>
where
    T: Clone + Eq + std::hash::Hash,
{
    match (vec1, vec2) {
        (Some(v1), Some(v2)) => {
            let set1: HashSet<_> = v1.iter().cloned().collect();
            let set2: HashSet<_> = v2.iter().cloned().collect();
            let intersection: Vec<T> = set1.intersection(&set2).cloned().collect();

            if intersection.is_empty() {
                None
            } else {
                Some(intersection)
            }
        }
        (None, None) => None,
        _ => None,
    }
}

#[derive(Debug, Deserialize, Clone, Default)]
pub struct ArchConfig {
    pub arch: String,
    pub operand_types: Vec<OperandType>,
    pub instructions: Vec<Instruction>,
    pub tests: Vec<String>,
    pub config_sets: HashMap<String, String>,
    pub target: Vec<String>,

    #[serde(skip)]
    pub instruction_map: HashMap<String, Instruction>,
}

impl ArchConfig {
    pub fn build_instruction_map(&mut self) {
        self.instruction_map = self
            .instructions
            .iter()
            .map(|instr| (instr.name.clone(), instr.clone()))
            .collect();
    }
}

pub fn config_intersection(config_paths: Vec<&str>) -> Result<ArchConfig, String> {
    let mut final_config = ArchConfig::default();

    let configs: Vec<ArchConfig> = config_paths
        .iter()
        .map(|&path| {
            let content = std::fs::read_to_string(path)
                .map_err(|e| format!("Failed to read config file {}: {}", path, e))?;
            toml::from_str(&content)
                .map_err(|e| format!("Failed to parse config file {}: {}", path, e))
        })
        .collect::<Result<Vec<ArchConfig>, String>>()?;

    final_config = configs[0].clone();

    for config in &configs[1..] {
        for instr in &mut final_config.instructions {
            if let Some(other_instr) = config.instructions.iter().find(|i| i.name == instr.name) {
                instr.modes = match (&instr.modes, &other_instr.modes) {
                    (Some(self_modes), Some(other_modes)) => {
                        let mut intersected_modes = Vec::new();

                        for self_mode in self_modes {
                            for other_mode in other_modes {
                                if let Some(intersected_mode) = self_mode.intersect(other_mode) {
                                    intersected_modes.push(intersected_mode);
                                }
                            }
                        }

                        if intersected_modes.is_empty() {
                            None
                        } else {
                            Some(intersected_modes)
                        }
                    }
                    _ => None,
                };
            } else {
                instr.modes = None;
            }
        }
    }

    Ok(final_config)
}

pub fn load_config(path: &str) -> ArchConfig {
    let content = fs::read_to_string(path).expect("Failed to read config file");
    toml::from_str(&content).expect("Failed to parse config")
}
