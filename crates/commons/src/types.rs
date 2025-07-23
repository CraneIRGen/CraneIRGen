use crate::types::ir::Type;
use cranelift_codegen::ir;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ResultType {
    Same,
    Conditional,
}

#[derive(Debug, Clone, Deserialize)]
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
    name: String,
    modes: Option<Vec<Mode>>,
}

#[derive(Debug, Deserialize, Clone)]
pub struct Mode {
    name: String,
    operand_types: Option<Vec<OperandType>>,
    arg0_types: Option<Vec<OperandType>>,
    arg1_types: Option<Vec<OperandType>>,
    result_type: Option<ResultType>,
    memory: Option<bool>,
}

#[derive(Debug, Deserialize)]
pub struct ArchConfig {
    instructions: Vec<Instruction>,
}

impl ArchConfig {
    fn build_instruction_map(&self) -> HashMap<String, Instruction> {
        let mut map = HashMap::new();
        for instr in &self.instructions {
            map.insert(instr.name.clone(), instr.clone());
        }
        map
    }
}
