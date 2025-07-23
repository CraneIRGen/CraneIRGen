use cranelift_codegen::cursor::FuncCursor;
use cranelift_codegen::entity::EntityRef;
use cranelift_codegen::ir;
use cranelift_codegen::ir::condcodes::{FloatCC, IntCC};
use cranelift_codegen::ir::immediates::{Ieee128, Ieee16, Ieee32, Ieee64, Imm64, Offset32, Uimm8};
use cranelift_codegen::ir::types::*;
use cranelift_codegen::ir::{
    types, AtomicRmwOp, Block, BlockCall, ConstantData, Endianness, Function, Immediate,
    InstBuilder, InstructionData, MemFlags, Opcode, TrapCode, Type, Value, ValueListPool,
};
use rand::prelude::{IndexedRandom, IteratorRandom};
use rand::{thread_rng, Rng};
use std::collections::{HashMap, HashSet};

#[derive(Hash, Eq, PartialEq, Debug, Clone)]
pub struct TypedValue {
    value: cranelift_codegen::ir::Value,
    value_type: ir::types::Type,
}

impl TypedValue {
    pub fn new(value: cranelift_codegen::ir::Value, value_type: types::Type) -> Self {
        TypedValue { value, value_type }
    }

    pub fn get_type(&self) -> ir::types::Type {
        self.value_type.clone()
    }

    pub fn get_value(&self) -> cranelift_codegen::ir::Value {
        self.value.clone()
    }
}

fn random_type(types: &[Type]) -> Type {
    let mut rng = thread_rng();

    *types.choose(&mut rng).unwrap()
}

fn random_intcc() -> IntCC {
    let conditions = [
        IntCC::Equal,
        IntCC::NotEqual,
        IntCC::SignedLessThan,
        IntCC::SignedGreaterThanOrEqual,
        IntCC::SignedGreaterThan,
        IntCC::SignedLessThanOrEqual,
        IntCC::UnsignedLessThan,
        IntCC::UnsignedGreaterThanOrEqual,
        IntCC::UnsignedGreaterThan,
        IntCC::UnsignedLessThanOrEqual,
    ];

    let mut rng = thread_rng();
    *conditions.choose(&mut rng).unwrap()
}

fn extract_vector_type(vector_type: Type) -> (Type, u8) {
    match vector_type {
        I8X16 => (I8, 16),
        I16X8 => (I16, 8),
        I32X4 => (I32, 4),
        I64X2 => (I64, 2),
        F16X8 => (F16, 8),
        F32X4 => (F32, 4),
        F64X2 => (F64, 2),
        _ => panic!("Unsupported vector type: {:?}", vector_type),
    }
}

fn bitcast_type_mapping(vector_type: Type) -> Type {
    match vector_type {
        I16 => F16,
        I32 => F32,
        I64 => F64,
        F16 => I16,
        F32 => I32,
        F64 => I64,
        I128 => random_type(&[I16X8, I32X4, I64X2, F32X4, F64X2]),
        I16X8 => random_type(&[I128]),
        I32X4 => random_type(&[F32X4, I128]),
        I64X2 => random_type(&[F64X2, I128]),
        F16X8 => random_type(&[I16X8, I128]),
        F32X4 => random_type(&[I32X4, I128]),
        F64X2 => random_type(&[I32X4, I128]),
        _ => panic!("Unsupported vector type: {:?}", vector_type),
    }
}

fn bitselect_type_mapping(vector_type: Type) -> Type {
    match vector_type {
        I8 => I8,
        I16 => random_type(&[I16]),
        I32 => random_type(&[F32, I32]),
        I64 => random_type(&[F64, I64]),
        F16 => random_type(&[I16, F16]),
        F32 => random_type(&[I32, F32]),
        F64 => random_type(&[I64, F64]),
        I128 => random_type(&[I16X8, I32X4, I64X2, F32X4, F64X2]),
        I8X16 => random_type(&[I16X8, I32X4, I64X2, F32X4, F64X2]),
        I16X8 => random_type(&[I16X8, I32X4, I64X2, F32X4, F64X2]),
        I32X4 => random_type(&[I16X8, I32X4, I64X2, F32X4, F64X2]),
        I64X2 => random_type(&[I16X8, I32X4, I64X2, F32X4, F64X2]),
        F16X8 => random_type(&[I16X8, I32X4, I64X2, F32X4, F64X2]),
        F32X4 => random_type(&[I16X8, I32X4, I64X2, F32X4, F64X2]),
        F64X2 => random_type(&[I16X8, I32X4, I64X2, F32X4, F64X2]),
        _ => panic!("Unsupported vector type: {:?}", vector_type),
    }
}

pub fn get_dominator_values_with_type(
    dominator_blocks: &HashSet<Block>,
    block_dominator_values: &HashMap<Block, HashSet<TypedValue>>,
    value_type: ir::types::Type,
) -> Vec<cranelift_codegen::ir::Value> {
    let mut values = vec![];

    for block in dominator_blocks.iter() {
        if let Some(type_values) = block_dominator_values.get(&block) {
            for value in type_values {
                if value.get_type() == value_type {
                    values.push(value.get_value());
                }
            }
        } else {
            continue;
        }
    }

    values.sort_by(|a, b| b.as_u32().cmp(&a.as_u32()));

    return values;
}

pub fn select_random_value<T>(vec: &Vec<T>, head_ratio: f32) -> Option<&T> {
    if vec.is_empty() {
        return None;
    }

    let mut rng = rand::thread_rng();

    let select_head = rng.gen_range(0.0..1.0) < head_ratio;

    if select_head {
        let head_count = (vec.len() as f32 * head_ratio).round() as usize;
        if head_count == 0 {
            return Some(&vec[0]);
        }
        let index = rng.gen_range(0..head_count.min(vec.len()));
        Some(&vec[index])
    } else {
        let index = rng.gen_range(0..vec.len());
        Some(&vec[index])
    }
}

pub fn get_random_cond_value(
    dominator_blocks: &HashSet<Block>,
    block_dominator_values: &HashMap<Block, HashSet<TypedValue>>,
) -> Value {
    let mut random_values_i32 =
        get_dominator_values_with_type(dominator_blocks, block_dominator_values, ir::types::I32);
    random_values_i32.sort_by(|a, b| b.as_u32().cmp(&a.as_u32()));

    for value in random_values_i32.iter() {
        println!("{}", value.as_u32());
    }
    let random_value = select_random_value(&random_values_i32, 0.4).unwrap();
    return *random_value;
}

pub fn populate_block_instructions(
    cur: &mut FuncCursor,
    instr_data: InstructionData,
    dominator_blocks: &HashSet<Block>,
    block_dominator_values: &HashMap<Block, HashSet<TypedValue>>,
) -> Option<(Option<TypedValue>, Option<Vec<TypedValue>>)> {
    fn instr_mutation() -> Opcode {
        let mut rng = thread_rng();
        let opcode = Opcode::all().choose(&mut rng).unwrap().clone();
        opcode
    }

    let mut rng = thread_rng();

    let all_types = [
        I8, I16, I32, I64, F16, F32, F64, I8X16, I16X8, F16X8, I32X4, F32X4, I64X2, F64X2,
    ];
    let scalar_types = [I8, I16, I32, I64];
    let integer_types = [I8, I16, I32, I64];
    let float_types = [F16, F32, F64];
    let vector_types = [I8X16, I16X8, F16X8, I32X4, F32X4, I64X2, F64X2];
    let vector_integer_types = [I8X16, I16X8, I32X4, I64X2];
    let vector_float_types = [F16X8, F32X4, F64X2];

    let instr_opcode = instr_mutation();

    match instr_opcode {
        Opcode::AtomicCas => {
            let random_stack_slot = cur
                .func
                .sized_stack_slots
                .iter()
                .choose(&mut rng)
                .unwrap()
                .0;
            let addr = cur.ins().stack_addr(
                ir::types::I64,
                random_stack_slot,
                Offset32::new(rng.gen_range(0..10)),
            );

            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let mut mem_flag_little = ir::MemFlags::new();
                    mem_flag_little.set_endianness(Endianness::Little);

                    let ref_value = random_values_with_same_type.get(0).unwrap();
                    let new_value =
                        cur.ins()
                            .atomic_cas(mem_flag_little, addr, *ref_value, *ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(*ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let mut mem_flag_little = ir::MemFlags::new();
                    mem_flag_little.set_endianness(Endianness::Little);
                    let new_value =
                        cur.ins()
                            .atomic_cas(mem_flag_little, addr, first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        Opcode::AtomicRmw => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };

            let atomic_op = [
                AtomicRmwOp::Add,
                AtomicRmwOp::Sub,
                AtomicRmwOp::And,
                AtomicRmwOp::Nand,
                AtomicRmwOp::Or,
                AtomicRmwOp::Xor,
                AtomicRmwOp::Xchg,
                AtomicRmwOp::Umin,
                AtomicRmwOp::Umax,
                AtomicRmwOp::Smin,
                AtomicRmwOp::Smax,
            ]
            .choose(&mut rng)
            .unwrap();

            let random_stack_slot = cur
                .func
                .sized_stack_slots
                .iter()
                .choose(&mut rng)
                .unwrap()
                .0;
            let addr = cur
                .ins()
                .stack_addr(ir::types::I64, random_stack_slot, Offset32::new(0));

            let mut mem_flag_little = ir::MemFlags::new();
            mem_flag_little.set_endianness(Endianness::Little);

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let operand_value = *select_random_value(&random_values_with_same_type, 0.4).unwrap();

            let new_value =
                cur.ins()
                    .atomic_rmw(value_type, mem_flag_little, *atomic_op, addr, operand_value);
            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(operand_value, value_type)]),
            ));
        }

        Opcode::Swizzle => {
            let mut random_values_with_same_type =
                get_dominator_values_with_type(dominator_blocks, block_dominator_values, I8X16);
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = random_values_with_same_type.pop().unwrap();
                    let new_value = cur.ins().swizzle(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, ir::types::I8X16)),
                        Some(vec![TypedValue::new(ref_value, ir::types::I8X16)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().swizzle(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, ir::types::I8X16)),
                        Some(vec![
                            TypedValue::new(first_value, ir::types::I8X16),
                            TypedValue::new(second_value, ir::types::I8X16),
                        ]),
                    ));
                }
            }
        }

        #[cfg(feature = "x86-64")]
        Opcode::X86Pshufb => {
            let mut random_values_with_same_type =
                get_dominator_values_with_type(dominator_blocks, block_dominator_values, I8X16);
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = random_values_with_same_type.pop().unwrap();
                    let new_value = cur.ins().x86_pshufb(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, I8X16)),
                        Some(vec![TypedValue::new(ref_value, I8X16)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().x86_pshufb(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, I8X16)),
                        Some(vec![
                            TypedValue::new(first_value, I8X16),
                            TypedValue::new(second_value, I8X16),
                        ]),
                    ));
                }
            }
        }

        Opcode::Smin => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64, I8X16, I16X8, I32X4, I64X2])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = random_values_with_same_type.get(0).unwrap();
                    let new_value = cur.ins().smin(*ref_value, *ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(*ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().smin(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }
        Opcode::Umin => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64, I8X16, I16X8, I32X4, I64X2])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = *random_values_with_same_type.get(0).unwrap();
                    let new_value = cur.ins().umin(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().umin(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }
        Opcode::Smax => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64, I8X16, I16X8, I32X4, I64X2])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = *random_values_with_same_type.get(0).unwrap();
                    let new_value = cur.ins().smax(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().smax(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }
        Opcode::Umax => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64, I8X16, I16X8, I32X4, I64X2])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = *random_values_with_same_type.get(0).unwrap();
                    let new_value = cur.ins().umax(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(new_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().umax(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        Opcode::AvgRound => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8X16, I16X8])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = random_values_with_same_type.pop().unwrap();
                    let new_value = cur.ins().avg_round(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(new_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().avg_round(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        Opcode::UaddSat => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8X16, I16X8])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = random_values_with_same_type.pop().unwrap();
                    let new_value = cur.ins().uadd_sat(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(new_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().uadd_sat(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        Opcode::SaddSat => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8X16, I16X8])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = random_values_with_same_type.pop().unwrap();
                    let new_value = cur.ins().sadd_sat(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(new_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().sadd_sat(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        Opcode::UsubSat => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8X16, I16X8])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = random_values_with_same_type.pop().unwrap();
                    let new_value = cur.ins().usub_sat(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(new_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().usub_sat(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        Opcode::SsubSat => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8X16, I16X8])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = random_values_with_same_type.pop().unwrap();
                    let new_value = cur.ins().ssub_sat(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(new_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().ssub_sat(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        Opcode::Iadd => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = *random_values_with_same_type.get(0).unwrap();
                    let new_value = cur.ins().iadd(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().iadd(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }
        Opcode::Isub => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = *random_values_with_same_type.get(0).unwrap();
                    let new_value = cur.ins().isub(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(new_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().isub(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }
        Opcode::Imul => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = *random_values_with_same_type.get(0).unwrap();
                    let new_value = cur.ins().imul(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().imul(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        Opcode::Umulhi => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64, I8X16, I16X8, I32X4, I64X2])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = *random_values_with_same_type.get(0).unwrap();
                    let new_value = cur.ins().umulhi(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(new_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().umulhi(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        Opcode::Smulhi => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64, I8X16, I16X8, I32X4, I64X2])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = *random_values_with_same_type.get(0).unwrap();
                    let new_value = cur.ins().smulhi(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().smulhi(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        Opcode::SqmulRoundSat => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I16X8])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I16X8])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I16X8])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I16X8])
                }
            };
            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = random_values_with_same_type.pop().unwrap();
                    let new_value = cur.ins().sqmul_round_sat(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(new_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().sqmul_round_sat(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        #[cfg(feature = "x86-64")]
        Opcode::X86Pmaddubsw => {
            let value_type = I8X16;

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = random_values_with_same_type.pop().unwrap();
                    let new_value = cur.ins().x86_pmaddubsw(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, I16X8)),
                        Some(vec![TypedValue::new(new_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().x86_pmaddubsw(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, I16X8)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        Opcode::Udiv => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = *random_values_with_same_type.get(0).unwrap();
                    let new_value = cur.ins().udiv(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().udiv(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        Opcode::Sdiv => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = *random_values_with_same_type.get(0).unwrap();
                    let new_value = cur.ins().sdiv(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().sdiv(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        Opcode::Urem => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = *random_values_with_same_type.get(0).unwrap();
                    let new_value = cur.ins().urem(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().urem(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        Opcode::Srem => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = *random_values_with_same_type.get(0).unwrap();
                    let new_value = cur.ins().srem(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().srem(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        #[cfg(not(any(feature = "riscv", feature = "s390x")))]
        Opcode::UaddOverflow => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = random_values_with_same_type.pop().unwrap();
                    let (new_value, _) = cur.ins().uadd_overflow(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let (new_value, _) = cur.ins().uadd_overflow(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        #[cfg(not(any(feature = "riscv", feature = "s390x")))]
        Opcode::SaddOverflow => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = random_values_with_same_type.pop().unwrap();
                    let (new_value, _) = cur.ins().sadd_overflow(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let (new_value, _) = cur.ins().sadd_overflow(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        #[cfg(not(any(feature = "riscv", feature = "s390x")))]
        Opcode::UsubOverflow => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = random_values_with_same_type.pop().unwrap();
                    let (new_value, _) = cur.ins().usub_overflow(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let (new_value, _) = cur.ins().usub_overflow(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        #[cfg(not(any(feature = "riscv", feature = "s390x")))]
        Opcode::SsubOverflow => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = random_values_with_same_type.pop().unwrap();
                    let (new_value, _) = cur.ins().ssub_overflow(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let (new_value, _) = cur.ins().ssub_overflow(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        #[cfg(not(any(feature = "riscv", feature = "s390x")))]
        Opcode::UmulOverflow => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = random_values_with_same_type.pop().unwrap();
                    let (new_value, _) = cur.ins().umul_overflow(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let (new_value, _) = cur.ins().umul_overflow(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        #[cfg(not(any(feature = "riscv", feature = "s390x")))]
        Opcode::SmulOverflow => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = random_values_with_same_type.pop().unwrap();
                    let (new_value, _) = cur.ins().smul_overflow(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let (new_value, _) = cur.ins().smul_overflow(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        Opcode::Band => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, F32, F64, I8X16, I16X8, I32X4, I64X2, F16X8,
                        F32X4, F64X2,
                    ])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, F16, F32, F64, I8X16, I16X8, I32X4, I64X2, F32X4,
                        F64X2,
                    ])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, F16, F32, F64, I8X16, I16X8, I32X4, I64X2, F32X4,
                        F64X2,
                    ])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = *random_values_with_same_type.get(0).unwrap();
                    let new_value = cur.ins().band(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().band(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        Opcode::Bor => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, F32, F64, I8X16, I16X8, I32X4, I64X2, F16X8,
                        F32X4, F64X2,
                    ])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, F16, F32, F64, I8X16, I16X8, I32X4, I64X2, F32X4,
                        F64X2,
                    ])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, F16, F32, F64, I8X16, I16X8, I32X4, I64X2, F32X4,
                    ])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = *random_values_with_same_type.get(0).unwrap();
                    let new_value = cur.ins().bor(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().bor(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        Opcode::Bxor => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, F32, F64, I8X16, I16X8, I32X4, I64X2, F16X8,
                        F32X4, F64X2,
                    ])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, F16, F32, F64, I8X16, I16X8, I32X4, I64X2, F32X4,
                        F64X2,
                    ])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, F16, F32, F64, I8X16, I16X8, I32X4, I64X2, F32X4,
                    ])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = *random_values_with_same_type.get(0).unwrap();
                    let new_value = cur.ins().bxor(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().bxor(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        Opcode::BandNot => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, F32, F64, I8X16, I16X8, I32X4, I64X2, F16X8,
                        F32X4, F64X2,
                    ])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, F16, F32, F64, I8X16, I16X8, I32X4, I64X2, F32X4,
                        F64X2,
                    ])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, F16, F32, F64, I8X16, I16X8, I32X4, I64X2, F32X4,
                    ])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = *random_values_with_same_type.get(0).unwrap();
                    let new_value = cur.ins().band_not(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().band_not(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        Opcode::BorNot => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, F32, F64, I8X16, I16X8, I32X4, I64X2, F16X8,
                        F32X4, F64X2,
                    ])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, F16, F32, F64, I8X16, I16X8, I32X4, I64X2, F32X4,
                        F64X2,
                    ])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, F16, F32, F64, I8X16, I16X8, I32X4, I64X2, F32X4,
                    ])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = *random_values_with_same_type.get(0).unwrap();
                    let new_value = cur.ins().bor_not(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().bor_not(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        Opcode::BxorNot => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, F32, F64, I8X16, I16X8, I32X4, I64X2, F16X8,
                        F32X4, F64X2,
                    ])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, F16, F32, F64, I8X16, I16X8, I32X4, I64X2, F32X4,
                        F64X2,
                    ])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, F16, F32, F64, I8X16, I16X8, I32X4, I64X2, F32X4,
                    ])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
            };

            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = *random_values_with_same_type.get(0).unwrap();
                    let new_value = cur.ins().bxor_not(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().bxor_not(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        Opcode::Rotl => {
            let arg0_value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
            };

            let arg1_value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };

            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                arg0_value_type,
            );
            let rotled_value = *select_random_value(&dominator_values, 0.4).unwrap();

            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                arg1_value_type,
            );
            let bits_num = *select_random_value(&dominator_values, 0.4).unwrap();

            let new_value = cur.ins().rotl(rotled_value, bits_num);
            return Some((
                Some(TypedValue::new(new_value, arg0_value_type)),
                Some(vec![
                    TypedValue::new(rotled_value, arg0_value_type),
                    TypedValue::new(bits_num, arg1_value_type),
                ]),
            ));
        }

        Opcode::Rotr => {
            let arg0_value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
            };

            let arg1_value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };

            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                arg0_value_type,
            );
            let rotred_value = *select_random_value(&dominator_values, 0.4).unwrap();

            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                arg1_value_type,
            );
            let bits_num = *select_random_value(&dominator_values, 0.4).unwrap();

            let new_value = cur.ins().rotr(rotred_value, bits_num);
            return Some((
                Some(TypedValue::new(new_value, arg0_value_type)),
                Some(vec![
                    TypedValue::new(rotred_value, arg0_value_type),
                    TypedValue::new(bits_num, arg1_value_type),
                ]),
            ));
        }

        Opcode::Ishl => {
            let arg0_value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2])
                }
            };

            let arg1_value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };

            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                arg0_value_type,
            );
            let ishled_value = *select_random_value(&dominator_values, 0.4).unwrap();

            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                arg1_value_type,
            );
            let bits_num = *select_random_value(&dominator_values, 0.4).unwrap();

            let new_value = cur.ins().ishl(ishled_value, bits_num);
            return Some((
                Some(TypedValue::new(new_value, arg0_value_type)),
                Some(vec![
                    TypedValue::new(ishled_value, arg0_value_type),
                    TypedValue::new(bits_num, arg1_value_type),
                ]),
            ));
        }

        Opcode::Ushr => {
            let arg0_value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2])
                }
            };

            let arg1_value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };

            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                arg0_value_type,
            );
            let ushred_value = *select_random_value(&dominator_values, 0.4).unwrap();

            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                arg1_value_type,
            );
            let bits_num = *select_random_value(&dominator_values, 0.4).unwrap();

            let new_value = cur.ins().ushr(ushred_value, bits_num);
            return Some((
                Some(TypedValue::new(new_value, arg0_value_type)),
                Some(vec![
                    TypedValue::new(ushred_value, arg0_value_type),
                    TypedValue::new(bits_num, arg1_value_type),
                ]),
            ));
        }

        Opcode::Sshr => {
            let arg0_value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2])
                }
            };

            let arg1_value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };

            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                arg0_value_type,
            );
            let sshred_value = *select_random_value(&dominator_values, 0.4).unwrap();

            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                arg1_value_type,
            );
            let bits_num = *select_random_value(&dominator_values, 0.4).unwrap();

            let new_value = cur.ins().sshr(sshred_value, bits_num);
            return Some((
                Some(TypedValue::new(new_value, arg0_value_type)),
                Some(vec![
                    TypedValue::new(sshred_value, arg0_value_type),
                    TypedValue::new(bits_num, arg1_value_type),
                ]),
            ));
        }

        Opcode::Fadd => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
            };
            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = random_values_with_same_type.pop().unwrap();
                    let new_value = cur.ins().fadd(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().fadd(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        Opcode::Fsub => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
            };
            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = random_values_with_same_type.pop().unwrap();
                    let new_value = cur.ins().fsub(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().fsub(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        Opcode::Fmul => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
            };
            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = random_values_with_same_type.pop().unwrap();
                    let new_value = cur.ins().fmul(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().fmul(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        Opcode::Fdiv => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
            };
            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = random_values_with_same_type.pop().unwrap();
                    let new_value = cur.ins().fdiv(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().fdiv(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        Opcode::Fcopysign => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[F32, F64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[F32, F64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[F32, F64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[F32, F64])
                }
            };
            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = random_values_with_same_type.pop().unwrap();
                    let new_value = cur.ins().fcopysign(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().fcopysign(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        Opcode::Fmin => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[F32, F64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[F32, F64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[F32, F64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[F32, F64])
                }
            };
            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = random_values_with_same_type.pop().unwrap();
                    let new_value = cur.ins().fmin(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().fmin(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        Opcode::Fmax => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[F32, F64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[F32, F64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[F32, F64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[F32, F64])
                }
            };
            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = random_values_with_same_type.pop().unwrap();
                    let new_value = cur.ins().fmax(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().fmax(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }

        Opcode::Snarrow => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I16X8, I32X4])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I16X8, I32X4])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I16X8, I32X4])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I16X8, I32X4])
                }
            };
            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );

            if random_values_with_same_type.len() >= 2 {
                let first_value = *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                let second_value =
                    *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                let new_value = cur.ins().snarrow(first_value, second_value);
                match value_type {
                    I16X8 => {
                        return Some((
                            Some(TypedValue::new(new_value, I8X16)),
                            Some(vec![
                                TypedValue::new(first_value, value_type),
                                TypedValue::new(second_value, value_type),
                            ]),
                        ));
                    }
                    I32X4 => {
                        return Some((
                            Some(TypedValue::new(new_value, I16X8)),
                            Some(vec![
                                TypedValue::new(first_value, value_type),
                                TypedValue::new(second_value, value_type),
                            ]),
                        ));
                    }
                    I64X2 => {
                        return Some((
                            Some(TypedValue::new(new_value, I32X4)),
                            Some(vec![
                                TypedValue::new(first_value, value_type),
                                TypedValue::new(second_value, value_type),
                            ]),
                        ));
                    }
                    _ => {
                        panic!("error value type")
                    }
                }
            } else if random_values_with_same_type.len() == 1 {
                let ref_value = random_values_with_same_type.pop().unwrap();
                let new_value = cur.ins().snarrow(ref_value, ref_value);
                match value_type {
                    I16X8 => {
                        return Some((
                            Some(TypedValue::new(new_value, I8X16)),
                            Some(vec![TypedValue::new(ref_value, value_type)]),
                        ));
                    }
                    I32X4 => {
                        return Some((
                            Some(TypedValue::new(new_value, I16X8)),
                            Some(vec![TypedValue::new(ref_value, value_type)]),
                        ));
                    }
                    I64X2 => {
                        return Some((
                            Some(TypedValue::new(new_value, I32X4)),
                            Some(vec![TypedValue::new(ref_value, value_type)]),
                        ));
                    }
                    _ => {
                        panic!("error value type")
                    }
                }
            }
        }

        Opcode::Unarrow => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I16X8, I32X4])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I16X8, I32X4])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I16X8, I32X4])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I16X8, I32X4])
                }
            };
            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );

            if random_values_with_same_type.len() >= 2 {
                let first_value = *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                let second_value =
                    *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                let new_value = cur.ins().unarrow(first_value, second_value);

                match value_type {
                    I16X8 => {
                        return Some((
                            Some(TypedValue::new(new_value, I8X16)),
                            Some(vec![
                                TypedValue::new(first_value, value_type),
                                TypedValue::new(second_value, value_type),
                            ]),
                        ));
                    }
                    I32X4 => {
                        return Some((
                            Some(TypedValue::new(new_value, I16X8)),
                            Some(vec![
                                TypedValue::new(first_value, value_type),
                                TypedValue::new(second_value, value_type),
                            ]),
                        ));
                    }
                    _ => {
                        panic!("error value type")
                    }
                }
            } else if random_values_with_same_type.len() == 1 {
                let ref_value = random_values_with_same_type.pop().unwrap();
                let new_value = cur.ins().unarrow(ref_value, ref_value);
                match value_type {
                    I16X8 => {
                        return Some((
                            Some(TypedValue::new(new_value, I8X16)),
                            Some(vec![TypedValue::new(ref_value, value_type)]),
                        ));
                    }
                    I32X4 => {
                        return Some((
                            Some(TypedValue::new(new_value, I16X8)),
                            Some(vec![TypedValue::new(ref_value, value_type)]),
                        ));
                    }
                    _ => {
                        panic!("error value type")
                    }
                }
            }
        }

        Opcode::Uunarrow => {
            let substitute_types = [I16X8, I32X4, I64X2];
            let value_type = *substitute_types.choose(&mut rng).unwrap();
            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );

            if random_values_with_same_type.len() >= 2 {
                let first_value = *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                let second_value =
                    *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                let new_value = cur.ins().uunarrow(first_value, second_value);
                match value_type {
                    I16X8 => {
                        return Some((
                            Some(TypedValue::new(new_value, I8X16)),
                            Some(vec![
                                TypedValue::new(first_value, value_type),
                                TypedValue::new(second_value, value_type),
                            ]),
                        ));
                    }
                    I32X4 => {
                        return Some((
                            Some(TypedValue::new(new_value, I16X8)),
                            Some(vec![
                                TypedValue::new(first_value, value_type),
                                TypedValue::new(second_value, value_type),
                            ]),
                        ));
                    }
                    I64X2 => {
                        return Some((
                            Some(TypedValue::new(new_value, I32X4)),
                            Some(vec![
                                TypedValue::new(first_value, value_type),
                                TypedValue::new(second_value, value_type),
                            ]),
                        ));
                    }
                    _ => {
                        panic!("error value type")
                    }
                }
            } else if random_values_with_same_type.len() == 1 {
                let ref_value = random_values_with_same_type.pop().unwrap();
                let new_value = cur.ins().uunarrow(ref_value, ref_value);

                match value_type {
                    I16X8 => {
                        return Some((
                            Some(TypedValue::new(new_value, I8X16)),
                            Some(vec![TypedValue::new(ref_value, value_type)]),
                        ));
                    }
                    I32X4 => {
                        return Some((
                            Some(TypedValue::new(new_value, I16X8)),
                            Some(vec![TypedValue::new(ref_value, value_type)]),
                        ));
                    }
                    I64X2 => {
                        return Some((
                            Some(TypedValue::new(new_value, I32X4)),
                            Some(vec![TypedValue::new(ref_value, value_type)]),
                        ));
                    }
                    _ => {
                        panic!("error value type")
                    }
                }
            }
        }

        Opcode::IaddPairwise => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8X16, I16X8, I32X4])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8X16, I16X8, I32X4])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8X16, I16X8, I32X4])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8X16, I16X8, I32X4])
                }
            };
            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            if random_values_with_same_type.len() == 0 {
                return None;
            }
            if random_values_with_same_type.len() >= 2 {
                let first_value = *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                let second_value =
                    *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                let new_value = cur.ins().iadd_pairwise(first_value, second_value);
                return Some((
                    Some(TypedValue::new(new_value, value_type)),
                    Some(vec![
                        TypedValue::new(first_value, value_type),
                        TypedValue::new(second_value, value_type),
                    ]),
                ));
            } else if random_values_with_same_type.len() == 1 {
                let ref_value = random_values_with_same_type.pop().unwrap();
                let new_value = cur.ins().iadd_pairwise(ref_value, ref_value);
                return Some((
                    Some(TypedValue::new(new_value, value_type)),
                    Some(vec![TypedValue::new(ref_value, value_type)]),
                ));
            }
        }

        Opcode::Iconcat => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I64])
                }
            };
            let mut iconcated_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            if iconcated_values.len() >= 2 {
                let first_value = *select_random_value(&iconcated_values, 0.4).unwrap();
                let second_value = *select_random_value(&iconcated_values, 0.4).unwrap();

                let new_value = cur.ins().iconcat(first_value, second_value);

                match value_type {
                    I64 => {
                        return Some((
                            Some(TypedValue::new(new_value, I128)),
                            Some(vec![
                                TypedValue::new(first_value, value_type),
                                TypedValue::new(second_value, value_type),
                            ]),
                        ));
                    }
                    _ => {
                        panic!("error value type")
                    }
                }
            } else if iconcated_values.len() == 1 {
                let ref_value = iconcated_values.pop().unwrap();
                let new_value = cur.ins().iconcat(ref_value, ref_value);
                match value_type {
                    I64 => {
                        return Some((
                            Some(TypedValue::new(new_value, I128)),
                            Some(vec![TypedValue::new(ref_value, value_type)]),
                        ));
                    }
                    _ => {
                        panic!("error value type")
                    }
                }
            }
        }

        Opcode::IaddImm => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let iadd_immed_values = *select_random_value(&dominator_values, 0.4).unwrap();

            let new_value = cur.ins().iadd_imm(
                iadd_immed_values,
                Imm64::new(rng.gen_range(i64::MIN..=i64::MAX)),
            );
            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(iadd_immed_values, value_type)]),
            ));
        }

        Opcode::ImulImm => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let imul_immed_values = *select_random_value(&dominator_values, 0.4).unwrap();

            let new_value = cur.ins().imul_imm(
                imul_immed_values,
                Imm64::new(rng.gen_range(i64::MIN..=i64::MAX)),
            );
            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(imul_immed_values, value_type)]),
            ));
        }

        Opcode::UdivImm => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };

            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let udiv_immed_values = *select_random_value(&dominator_values, 0.4).unwrap();

            let new_value = cur.ins().udiv_imm(
                udiv_immed_values,
                Imm64::new(rng.gen_range(i64::MIN..=i64::MAX)),
            );
            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(udiv_immed_values, value_type)]),
            ));
        }

        Opcode::SdivImm => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let sdiv_immed_values = *select_random_value(&dominator_values, 0.4).unwrap();

            let new_value = cur.ins().sdiv_imm(
                sdiv_immed_values,
                Imm64::new(rng.gen_range(i64::MIN..=i64::MAX)),
            );
            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(sdiv_immed_values, value_type)]),
            ));
        }

        Opcode::UremImm => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let urem_immed_values = *select_random_value(&dominator_values, 0.4).unwrap();

            let new_value = cur.ins().urem_imm(
                urem_immed_values,
                Imm64::new(rng.gen_range(i64::MIN..=i64::MAX)),
            );
            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(urem_immed_values, value_type)]),
            ));
        }
        Opcode::SremImm => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let srem_immed_values = *select_random_value(&dominator_values, 0.4).unwrap();

            let new_value = cur.ins().srem_imm(
                srem_immed_values,
                Imm64::new(rng.gen_range(i64::MIN..=i64::MAX)),
            );
            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(srem_immed_values, value_type)]),
            ));
        }

        Opcode::IrsubImm => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let irsub_immed_values = *select_random_value(&dominator_values, 0.4).unwrap();

            let new_value = cur.ins().irsub_imm(
                irsub_immed_values,
                Imm64::new(rng.gen_range(i64::MIN..=i64::MAX)),
            );
            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(irsub_immed_values, value_type)]),
            ));
        }

        Opcode::BandImm => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let band_immed_values = *select_random_value(&dominator_values, 0.4).unwrap();

            let new_value = cur.ins().band_imm(
                band_immed_values,
                Imm64::new(rng.gen_range(i64::MIN..=i64::MAX)),
            );
            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(band_immed_values, value_type)]),
            ));
        }

        Opcode::BorImm => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let bor_immed_values = *select_random_value(&dominator_values, 0.4).unwrap();

            let new_value = cur.ins().bor_imm(
                bor_immed_values,
                Imm64::new(rng.gen_range(i64::MIN..=i64::MAX)),
            );
            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(bor_immed_values, value_type)]),
            ));
        }

        Opcode::BxorImm => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let bxor_immed_values = *select_random_value(&dominator_values, 0.4).unwrap();

            let new_value = cur.ins().bxor_imm(
                bxor_immed_values,
                Imm64::new(rng.gen_range(i64::MIN..=i64::MAX)),
            );
            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(bxor_immed_values, value_type)]),
            ));
        }

        Opcode::RotlImm => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let rotl_immed_values = *select_random_value(&dominator_values, 0.4).unwrap();

            let new_value = cur.ins().rotl_imm(
                rotl_immed_values,
                Imm64::new(rng.gen_range(i64::MIN..=i64::MAX)),
            );
            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(rotl_immed_values, value_type)]),
            ));
        }

        Opcode::RotrImm => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let rotr_immed_values = *select_random_value(&dominator_values, 0.4).unwrap();

            let new_value = cur.ins().rotr_imm(
                rotr_immed_values,
                Imm64::new(rng.gen_range(i64::MIN..=i64::MAX)),
            );
            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(rotr_immed_values, value_type)]),
            ));
        }

        Opcode::IshlImm => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let ishl_immed_values = *select_random_value(&dominator_values, 0.4).unwrap();

            let new_value = cur.ins().ishl_imm(
                ishl_immed_values,
                Imm64::new(rng.gen_range(i64::MIN..=i64::MAX)),
            );
            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(ishl_immed_values, value_type)]),
            ));
        }

        Opcode::UshrImm => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let ushr_immed_values = *select_random_value(&dominator_values, 0.4).unwrap();

            let new_value = cur.ins().ushr_imm(
                ushr_immed_values,
                Imm64::new(rng.gen_range(i64::MIN..=i64::MAX)),
            );
            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(ushr_immed_values, value_type)]),
            ));
        }

        Opcode::SshrImm => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let sshr_immed_values = *select_random_value(&dominator_values, 0.4).unwrap();

            let new_value = cur.ins().sshr_imm(
                sshr_immed_values,
                Imm64::new(rng.gen_range(i64::MIN..=i64::MAX)),
            );
            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(sshr_immed_values, value_type)]),
            ));
        }

        Opcode::Extractlane => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2, F32X4, F64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2, F32X4, F64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2, F32X4, F64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2, F32X4, F64X2])
                }
            };
            let (result_type, max_lane) = extract_vector_type(value_type);
            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                _ => {
                    let ref_value = *random_values_with_same_type.choose(&mut rng).unwrap();
                    let new_value = cur
                        .ins()
                        .extractlane(ref_value, Uimm8::from(rng.gen_range(0..=max_lane - 1)));
                    return Some((
                        Some(TypedValue::new(new_value, result_type)),
                        Some(vec![TypedValue::new(ref_value, value_type)]),
                    ));
                }
            }
        }

        /*
          dss0 = explicit_dynamic_slot dt0
            block0:
              v0 = dynamic_stack_load.dt0 dss0
              v1 = extract_vector.dt0 v0, 0
              return v1
            }
        */
        Opcode::ExtractVector => {
            return None;
        }

        Opcode::BrTable => {
            return None;
        }
        Opcode::Brif => {
            return None;
        }
        Opcode::Call => {
            return None;
        }
        Opcode::CallIndirect => {
            return None;
        }
        Opcode::ReturnCallIndirect => {
            return None;
        }

        Opcode::Trapz => {
            return None;

            let value_type = random_type(&scalar_types);
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let controlling_value = *select_random_value(&dominator_values, 0.4).unwrap();
            cur.ins().trapz(controlling_value, TrapCode::StackOverflow);
        }

        Opcode::Trapnz => {
            return None;
            let value_type = random_type(&scalar_types);
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let controlling_value = *select_random_value(&dominator_values, 0.4).unwrap();
            cur.ins().trapnz(controlling_value, TrapCode::StackOverflow);
        }

        Opcode::DynamicStackLoad => {
            return None;
        }

        Opcode::DynamicStackAddr => {
            return None;
        }

        Opcode::DynamicStackStore => {
            return None;
        }

        Opcode::Fcmp => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
            };
            let mut fcmped_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );

            let fcmp_cond = loop {
                let &cc = FloatCC::all().choose(&mut rng).unwrap();

                #[cfg(feature = "aarch64")]
                if matches!(
                    cc,
                    FloatCC::UnorderedOrLessThan
                        | FloatCC::UnorderedOrLessThanOrEqual
                        | FloatCC::UnorderedOrGreaterThan
                        | FloatCC::UnorderedOrGreaterThanOrEqual
                        | FloatCC::OrderedNotEqual
                        | FloatCC::UnorderedOrEqual
                ) {
                    continue;
                }

                break cc;
            };

            if fcmped_values.len() >= 2 {
                let first_value = *select_random_value(&fcmped_values, 0.4).unwrap();
                let second_value = *select_random_value(&fcmped_values, 0.4).unwrap();

                let new_value = cur.ins().fcmp(fcmp_cond, first_value, second_value);
                match value_type {
                    F16X8 => {
                        return Some((
                            Some(TypedValue::new(new_value, I16X8)),
                            Some(vec![
                                TypedValue::new(first_value, value_type),
                                TypedValue::new(second_value, value_type),
                            ]),
                        ));
                    }
                    F32X4 => {
                        return Some((
                            Some(TypedValue::new(new_value, I32X4)),
                            Some(vec![
                                TypedValue::new(first_value, value_type),
                                TypedValue::new(second_value, value_type),
                            ]),
                        ));
                    }
                    F64X2 => {
                        return Some((
                            Some(TypedValue::new(new_value, I64X2)),
                            Some(vec![
                                TypedValue::new(first_value, value_type),
                                TypedValue::new(second_value, value_type),
                            ]),
                        ));
                    }
                    _ => {
                        return Some((
                            Some(TypedValue::new(new_value, I8)),
                            Some(vec![
                                TypedValue::new(first_value, value_type),
                                TypedValue::new(second_value, value_type),
                            ]),
                        ));
                    }
                }
            } else if fcmped_values.len() == 1 {
                let ref_value = fcmped_values.pop().unwrap();
                let new_value = cur.ins().fcmp(fcmp_cond, ref_value, ref_value);

                match value_type {
                    F16X8 => {
                        return Some((
                            Some(TypedValue::new(new_value, I16X8)),
                            Some(vec![TypedValue::new(ref_value, value_type)]),
                        ));
                    }
                    F32X4 => {
                        return Some((
                            Some(TypedValue::new(new_value, I32X4)),
                            Some(vec![TypedValue::new(ref_value, value_type)]),
                        ));
                    }
                    F64X2 => {
                        return Some((
                            Some(TypedValue::new(new_value, I64X2)),
                            Some(vec![TypedValue::new(ref_value, value_type)]),
                        ));
                    }
                    _ => {
                        return Some((
                            Some(TypedValue::new(new_value, I8)),
                            Some(vec![TypedValue::new(ref_value, value_type)]),
                        ));
                    }
                }
            }
        }

        Opcode::FuncAddr => {
            return None;
        }

        Opcode::UaddOverflowTrap => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I32, I64])
                }
            };
            let mut uadded_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            if uadded_values.len() >= 2 {
                let first_value = *select_random_value(&uadded_values, 0.4).unwrap();
                let second_value = *select_random_value(&uadded_values, 0.4).unwrap();

                let trap_code = TrapCode::StackOverflow;

                let new_value = cur
                    .ins()
                    .uadd_overflow_trap(first_value, second_value, trap_code);
                return Some((
                    Some(TypedValue::new(new_value, value_type)),
                    Some(vec![
                        TypedValue::new(first_value, value_type),
                        TypedValue::new(second_value, value_type),
                    ]),
                ));
            } else if uadded_values.len() == 1 {
                let ref_value = uadded_values.pop().unwrap();
                let trap_code = TrapCode::StackOverflow;

                let new_value = cur
                    .ins()
                    .uadd_overflow_trap(ref_value, ref_value, trap_code);
                return Some((
                    Some(TypedValue::new(new_value, value_type)),
                    Some(vec![TypedValue::new(ref_value, value_type)]),
                ));
            }
        }

        Opcode::Icmp => {
            /*








            */
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I16X8, I32X4, I64X2])
                }
            };
            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            if random_values_with_same_type.len() == 0 {
                return None;
            }
            if random_values_with_same_type.len() >= 2 {
                let first_value = *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                let second_value =
                    *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                let new_value = cur.ins().icmp(random_intcc(), first_value, second_value);

                match value_type {
                    I16X8 => {
                        return Some((
                            Some(TypedValue::new(new_value, I16X8)),
                            Some(vec![
                                TypedValue::new(first_value, value_type),
                                TypedValue::new(second_value, value_type),
                            ]),
                        ));
                    }
                    I32X4 => {
                        return Some((
                            Some(TypedValue::new(new_value, I32X4)),
                            Some(vec![
                                TypedValue::new(first_value, value_type),
                                TypedValue::new(second_value, value_type),
                            ]),
                        ));
                    }
                    I64X2 => {
                        return Some((
                            Some(TypedValue::new(new_value, I64X2)),
                            Some(vec![
                                TypedValue::new(first_value, value_type),
                                TypedValue::new(second_value, value_type),
                            ]),
                        ));
                    }
                    _ => {
                        return Some((
                            Some(TypedValue::new(new_value, I8)),
                            Some(vec![
                                TypedValue::new(first_value, value_type),
                                TypedValue::new(second_value, value_type),
                            ]),
                        ));
                    }
                }
            } else if random_values_with_same_type.len() == 1 {
                let ref_value = random_values_with_same_type.pop().unwrap();
                let new_value = cur.ins().icmp(random_intcc(), ref_value, ref_value);

                match value_type {
                    I16X8 => {
                        return Some((
                            Some(TypedValue::new(new_value, I16X8)),
                            Some(vec![TypedValue::new(ref_value, value_type)]),
                        ));
                    }
                    I32X4 => {
                        return Some((
                            Some(TypedValue::new(new_value, I32X4)),
                            Some(vec![TypedValue::new(ref_value, value_type)]),
                        ));
                    }
                    I64X2 => {
                        return Some((
                            Some(TypedValue::new(new_value, I64X2)),
                            Some(vec![TypedValue::new(ref_value, value_type)]),
                        ));
                    }
                    _ => {
                        return Some((
                            Some(TypedValue::new(new_value, I8)),
                            Some(vec![TypedValue::new(ref_value, value_type)]),
                        ));
                    }
                }
            }
        }

        Opcode::IcmpImm => {
            let cond_all = IntCC::all();
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };
            let random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let random_i64_value = Imm64::new(rng.gen_range(i64::MIN..=i64::MAX) as i64);

            let first_value = *select_random_value(&random_values_with_same_type, 0.4).unwrap();

            let new_value = cur.ins().icmp_imm(
                *cond_all.choose(&mut rng).unwrap(),
                first_value,
                random_i64_value,
            );
            return Some((
                Some(TypedValue::new(new_value, I8)),
                Some(vec![TypedValue::new(first_value, value_type)]),
            ));
        }
        Opcode::Jump => {
            return None;
        }

        Opcode::Load => {
            let random_stack_slot = cur
                .func
                .sized_stack_slots
                .iter()
                .choose(&mut rng)
                .unwrap()
                .0;
            let addr = cur
                .ins()
                .stack_addr(ir::types::I64, random_stack_slot, Offset32::new(0));

            let mut mem_flag_little = ir::MemFlags::new();
            mem_flag_little.set_endianness(Endianness::Little);

            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, F16, F32, F64, I8X16, I16X8, I32X4, I64X2, F16X8,
                        F32X4, F64X2,
                    ])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, F16, F32, F64, I8X16, I16X8, I32X4, I64X2, F32X4,
                        F64X2,
                    ])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, F16, F32, F64, I8X16, I16X8, I32X4, I64X2, F32X4,
                        F64X2,
                    ])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, F32, F64, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
            };

            let new_value = cur.ins().load(
                value_type,
                mem_flag_little,
                addr,
                Offset32::new(rng.gen_range(0..10)),
            );
            return Some((Some(TypedValue::new(new_value, value_type)), None));
        }

        Opcode::Uload8 => {
            let random_stack_slot = cur
                .func
                .sized_stack_slots
                .iter()
                .choose(&mut rng)
                .unwrap()
                .0;
            let addr = cur
                .ins()
                .stack_addr(I64, random_stack_slot, Offset32::new(0));

            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I16, I32, I64])
                }
            };
            let mut mem_flag_little = ir::MemFlags::new();
            mem_flag_little.set_endianness(Endianness::Little);
            let new_value = cur.ins().uload8(
                value_type,
                mem_flag_little,
                addr,
                Offset32::new(rng.gen_range(0..10)),
            );
            return Some((Some(TypedValue::new(new_value, value_type)), None));
        }
        Opcode::Sload8 => {
            let random_stack_slot = cur
                .func
                .sized_stack_slots
                .iter()
                .choose(&mut rng)
                .unwrap()
                .0;
            let addr = cur
                .ins()
                .stack_addr(I64, random_stack_slot, Offset32::new(0));

            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I16, I32, I64])
                }
            };
            let mut mem_flag_little = ir::MemFlags::new();
            mem_flag_little.set_endianness(Endianness::Little);
            let new_value = cur.ins().sload8(
                value_type,
                mem_flag_little,
                addr,
                Offset32::new(rng.gen_range(0..10)),
            );
            return Some((Some(TypedValue::new(new_value, value_type)), None));
        }
        Opcode::Uload16 => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I32, I64])
                }
            };

            let random_stack_slot = cur
                .func
                .sized_stack_slots
                .iter()
                .choose(&mut rng)
                .unwrap()
                .0;
            let addr = cur
                .ins()
                .stack_addr(I64, random_stack_slot, Offset32::new(0));
            let mut mem_flag_little = ir::MemFlags::new();
            mem_flag_little.set_endianness(Endianness::Little);
            let new_value = cur.ins().uload16(
                value_type,
                mem_flag_little,
                addr,
                Offset32::new(rng.gen_range(0..10)),
            );
            return Some((Some(TypedValue::new(new_value, value_type)), None));
        }
        Opcode::Sload16 => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I32, I64])
                }
            };
            let random_stack_slot = cur
                .func
                .sized_stack_slots
                .iter()
                .choose(&mut rng)
                .unwrap()
                .0;
            let addr = cur
                .ins()
                .stack_addr(ir::types::I64, random_stack_slot, Offset32::new(0));
            let mut mem_flag_little = ir::MemFlags::new();
            mem_flag_little.set_endianness(Endianness::Little);
            let new_value = cur.ins().sload16(
                value_type,
                mem_flag_little,
                addr,
                Offset32::new(rng.gen_range(0..10)),
            );
            return Some((Some(TypedValue::new(new_value, value_type)), None));
        }
        Opcode::Uload32 => {
            let random_stack_slot = cur
                .func
                .sized_stack_slots
                .iter()
                .choose(&mut rng)
                .unwrap()
                .0;
            let addr = cur
                .ins()
                .stack_addr(ir::types::I64, random_stack_slot, Offset32::new(0));
            let mut mem_flag_little = ir::MemFlags::new();
            mem_flag_little.set_endianness(Endianness::Little);
            let new_value =
                cur.ins()
                    .uload32(mem_flag_little, addr, Offset32::new(rng.gen_range(0..10)));
            return Some((Some(TypedValue::new(new_value, I64)), None));
        }
        Opcode::Sload32 => {
            let random_stack_slot = cur
                .func
                .sized_stack_slots
                .iter()
                .choose(&mut rng)
                .unwrap()
                .0;
            let addr = cur
                .ins()
                .stack_addr(ir::types::I64, random_stack_slot, Offset32::new(0));
            let mut mem_flag_little = ir::MemFlags::new();
            mem_flag_little.set_endianness(Endianness::Little);
            let new_value =
                cur.ins()
                    .sload32(mem_flag_little, addr, Offset32::new(rng.gen_range(0..10)));
            return Some((Some(TypedValue::new(new_value, I64)), None));
        }
        Opcode::Uload8x8 => {
            return None;
            let random_stack_slot = cur
                .func
                .sized_stack_slots
                .iter()
                .choose(&mut rng)
                .unwrap()
                .0;
            let addr = cur
                .ins()
                .stack_addr(ir::types::I64, random_stack_slot, Offset32::new(0));
            let mut mem_flag_little = ir::MemFlags::new();
            mem_flag_little.set_endianness(Endianness::Little);
            let new_value =
                cur.ins()
                    .uload8x8(mem_flag_little, addr, Offset32::new(rng.gen_range(0..10)));
            return Some((Some(TypedValue::new(new_value, I16X8)), None));
        }
        Opcode::Sload8x8 => {
            return None;
            let random_stack_slot = cur
                .func
                .sized_stack_slots
                .iter()
                .choose(&mut rng)
                .unwrap()
                .0;
            let addr = cur
                .ins()
                .stack_addr(ir::types::I64, random_stack_slot, Offset32::new(0));
            let mut mem_flag_little = ir::MemFlags::new();
            mem_flag_little.set_endianness(Endianness::Little);
            let new_value =
                cur.ins()
                    .sload8x8(mem_flag_little, addr, Offset32::new(rng.gen_range(0..10)));
            return Some((Some(TypedValue::new(new_value, I16X8)), None));
        }
        Opcode::Uload16x4 => {
            return None;
            let random_stack_slot = cur
                .func
                .sized_stack_slots
                .iter()
                .choose(&mut rng)
                .unwrap()
                .0;
            let addr = cur
                .ins()
                .stack_addr(ir::types::I64, random_stack_slot, Offset32::new(0));
            let mut mem_flag_little = ir::MemFlags::new();
            mem_flag_little.set_endianness(Endianness::Little);
            let new_value =
                cur.ins()
                    .uload16x4(mem_flag_little, addr, Offset32::new(rng.gen_range(0..10)));
            return Some((Some(TypedValue::new(new_value, I32X4)), None));
        }
        Opcode::Sload16x4 => {
            return None;
            let random_stack_slot = cur
                .func
                .sized_stack_slots
                .iter()
                .choose(&mut rng)
                .unwrap()
                .0;
            let addr = cur
                .ins()
                .stack_addr(ir::types::I64, random_stack_slot, Offset32::new(0));
            let mut mem_flag_little = ir::MemFlags::new();
            mem_flag_little.set_endianness(Endianness::Little);
            let new_value =
                cur.ins()
                    .sload16x4(mem_flag_little, addr, Offset32::new(rng.gen_range(0..10)));
            return Some((Some(TypedValue::new(new_value, I32X4)), None));
        }

        Opcode::Uload32x2 => {
            return None;
            let random_stack_slot = cur
                .func
                .sized_stack_slots
                .iter()
                .choose(&mut rng)
                .unwrap()
                .0;
            let addr = cur
                .ins()
                .stack_addr(ir::types::I64, random_stack_slot, Offset32::new(0));
            let mut mem_flag_little = ir::MemFlags::new();
            mem_flag_little.set_endianness(Endianness::Little);
            let new_value =
                cur.ins()
                    .uload32x2(mem_flag_little, addr, Offset32::new(rng.gen_range(0..10)));
            return Some((Some(TypedValue::new(new_value, I64X2)), None));
        }

        Opcode::Sload32x2 => {
            return None;
            let random_stack_slot = cur
                .func
                .sized_stack_slots
                .iter()
                .choose(&mut rng)
                .unwrap()
                .0;
            let addr = cur
                .ins()
                .stack_addr(ir::types::I64, random_stack_slot, Offset32::new(0));
            let mut mem_flag_little = ir::MemFlags::new();
            mem_flag_little.set_endianness(Endianness::Little);
            let new_value =
                cur.ins()
                    .sload32x2(mem_flag_little, addr, Offset32::new(rng.gen_range(0..10)));
            return Some((Some(TypedValue::new(new_value, I64X2)), None));
        }

        Opcode::Bitcast => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I32, I64, F32, F64, I16X8, I32X4, I64X2, F16X8, F32X4, F64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I32, I64, F32, F64, I16X8, I32X4, I64X2, F32X4, F64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I32, I64, F32, F64, I16X8, I32X4, I64X2, F32X4, F64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I32, I64, F32, F64, I128, I16X8, I32X4, I64X2, F32X4, F64X2])
                }
            };
            let candidate_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let casted_value = *select_random_value(&candidate_values, 0.4).unwrap();
            let cast_type = bitcast_type_mapping(value_type);

            let mut mem_flag_little = ir::MemFlags::new();
            mem_flag_little.set_endianness(Endianness::Little);
            let new_value = cur.ins().bitcast(cast_type, mem_flag_little, casted_value);
            return Some((
                Some(TypedValue::new(new_value, cast_type)),
                Some(vec![TypedValue::new(casted_value, value_type)]),
            ));
        }

        Opcode::AtomicLoad => {
            let random_stack_slot = cur
                .func
                .sized_stack_slots
                .iter()
                .choose(&mut rng)
                .unwrap()
                .0;
            let addr = cur
                .ins()
                .stack_addr(I64, random_stack_slot, Offset32::new(0));
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };
            let mut mem_flag_little = ir::MemFlags::new();
            mem_flag_little.set_endianness(Endianness::Little);
            let new_value = cur.ins().atomic_load(value_type, mem_flag_little, addr);
            return Some((Some(TypedValue::new(new_value, value_type)), None));
        }

        Opcode::Return => {
            return None;
        }

        Opcode::Debugtrap => {
            return None;
            cur.ins().debugtrap();
            return None;
        }

        Opcode::GetFramePointer => {
            return None;
        }

        Opcode::GetStackPointer => {
            return None;
        }

        Opcode::GetReturnAddress => {
            return None;
        }

        Opcode::Nop => {
            cur.ins().nop();
            return None;
        }

        Opcode::Fence => {
            return None;
            cur.ins().fence();
        }

        Opcode::Shuffle => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8X16])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8X16])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8X16])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8X16])
                }
            };
            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            if random_values_with_same_type.len() == 0 {
                return None;
            }
            let mask_imm = {
                let mut lanes = [0u8; 16];
                for lane in lanes.iter_mut() {
                    *lane = rng.gen_range(0..=31);
                }
                let lanes = ConstantData::from(lanes.as_ref());
                cur.func.dfg.immediates.push(lanes)
            };

            if random_values_with_same_type.len() >= 2 {
                let first_value = *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                let second_value =
                    *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                let new_value = cur.ins().shuffle(first_value, second_value, mask_imm);

                return Some((
                    Some(TypedValue::new(new_value, I8X16)),
                    Some(vec![
                        TypedValue::new(first_value, value_type),
                        TypedValue::new(second_value, value_type),
                    ]),
                ));
            } else if random_values_with_same_type.len() == 1 {
                let ref_value = random_values_with_same_type.pop().unwrap();

                let new_value = cur.ins().shuffle(ref_value, ref_value, mask_imm);
                return Some((
                    Some(TypedValue::new(new_value, I8X16)),
                    Some(vec![TypedValue::new(ref_value, value_type)]),
                ));
            }
        }

        Opcode::StackLoad => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2, F16X8, F32X4, F64X2,
                    ])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
            };
            let random_stack_slot = cur
                .func
                .sized_stack_slots
                .iter()
                .choose(&mut rng)
                .unwrap()
                .0;

            let new_value = cur
                .ins()
                .stack_load(value_type, random_stack_slot, Offset32::new(0));

            return Some((Some(TypedValue::new(new_value, value_type)), None));
        }

        Opcode::StackAddr => {
            let random_stack_slot = cur
                .func
                .sized_stack_slots
                .iter()
                .choose(&mut rng)
                .unwrap()
                .0;
            let new_value = cur
                .ins()
                .stack_addr(I64, random_stack_slot, Offset32::new(0));

            return None;
        }

        #[cfg(not(feature = "s390x"))]
        Opcode::StackStore => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
            };
            let random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            if random_values_with_same_type.len() == 0 {
                return None;
            }
            let ref_value = *select_random_value(&random_values_with_same_type, 0.4).unwrap();

            let random_stack_slot = cur
                .func
                .sized_stack_slots
                .iter()
                .choose(&mut rng)
                .unwrap()
                .0;
            cur.ins()
                .stack_store(ref_value, random_stack_slot, Offset32::new(0));

            return Some((None, Some(vec![TypedValue::new(ref_value, value_type)])));
        }
        Opcode::Store => {
            let random_stack_slot = cur
                .func
                .sized_stack_slots
                .iter()
                .choose(&mut rng)
                .unwrap()
                .0;
            let addr = cur
                .ins()
                .stack_addr(I64, random_stack_slot, Offset32::new(0));

            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
            };
            let random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            if random_values_with_same_type.len() == 0 {
                return None;
            }
            let ref_value = *select_random_value(&random_values_with_same_type, 0.4).unwrap();
            let mut mem_flag_little = ir::MemFlags::new();
            mem_flag_little.set_endianness(Endianness::Little);
            cur.ins()
                .store(mem_flag_little, ref_value, addr, Offset32::new(0));

            return Some((None, Some(vec![TypedValue::new(ref_value, value_type)])));
        }
        Opcode::Istore8 => {
            let random_stack_slot = cur
                .func
                .sized_stack_slots
                .iter()
                .choose(&mut rng)
                .unwrap()
                .0;
            let addr = cur
                .ins()
                .stack_addr(ir::types::I64, random_stack_slot, Offset32::new(0));

            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I16, I32, I64])
                }
            };
            let random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let ref_value = *select_random_value(&random_values_with_same_type, 0.4).unwrap();
            let mut mem_flag_little = ir::MemFlags::new();
            mem_flag_little.set_endianness(Endianness::Little);
            cur.ins()
                .istore8(mem_flag_little, ref_value, addr, Offset32::new(0));

            return Some((None, Some(vec![TypedValue::new(ref_value, value_type)])));
        }
        Opcode::Istore16 => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I32, I64])
                }
            };

            let random_stack_slot = cur
                .func
                .sized_stack_slots
                .iter()
                .choose(&mut rng)
                .unwrap()
                .0;
            let addr = cur
                .ins()
                .stack_addr(ir::types::I64, random_stack_slot, Offset32::new(0));

            let random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let ref_value = *select_random_value(&random_values_with_same_type, 0.4).unwrap();
            let mut mem_flag_little = ir::MemFlags::new();
            mem_flag_little.set_endianness(Endianness::Little);
            cur.ins()
                .istore16(mem_flag_little, ref_value, addr, Offset32::new(0));

            return Some((None, Some(vec![TypedValue::new(ref_value, value_type)])));
        }
        Opcode::Istore32 => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I64])
                }
            };

            let random_stack_slot = cur
                .func
                .sized_stack_slots
                .iter()
                .choose(&mut rng)
                .unwrap()
                .0;
            let addr = cur
                .ins()
                .stack_addr(I64, random_stack_slot, Offset32::new(0));

            let random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let ref_value = *select_random_value(&random_values_with_same_type, 0.4).unwrap();
            let mut mem_flag_little = ir::MemFlags::new();
            mem_flag_little.set_endianness(Endianness::Little);
            cur.ins()
                .istore32(mem_flag_little, ref_value, addr, Offset32::new(0));

            return Some((None, Some(vec![TypedValue::new(ref_value, value_type)])));
        }
        Opcode::AtomicStore => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };

            let random_stack_slot = cur
                .func
                .sized_stack_slots
                .iter()
                .choose(&mut rng)
                .unwrap()
                .0;
            let addr = cur
                .ins()
                .stack_addr(I64, random_stack_slot, Offset32::new(0));

            let random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let ref_value = *select_random_value(&random_values_with_same_type, 0.4).unwrap();
            let mut mem_flag_little = ir::MemFlags::new();
            mem_flag_little.set_endianness(Endianness::Little);
            cur.ins().atomic_store(mem_flag_little, ref_value, addr);
            return Some((None, Some(vec![TypedValue::new(ref_value, value_type)])));
        }
        Opcode::StackSwitch => {
            return None;
        }
        Opcode::Select => {
            let control_value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };
            let control_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                control_value_type,
            );
            let control_value = *select_random_value(&control_values_with_same_type, 0.4).unwrap();
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[
                        I8, I16, I32, I64, F32, F64, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[
                        I8, I16, I32, I64, F32, F64, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[
                        I8, I16, I32, I64, F32, F64, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[
                        I8, I16, I32, I64, F32, F64, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
            };
            let ref_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let ref_value1 = *select_random_value(&ref_values_with_same_type, 0.4).unwrap();
            let ref_value2 = *select_random_value(&ref_values_with_same_type, 0.4).unwrap();
            let new_value = cur.ins().select(control_value, ref_value1, ref_value2);
            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![
                    TypedValue::new(control_value, control_value_type),
                    TypedValue::new(ref_value1, value_type),
                    TypedValue::new(ref_value2, value_type),
                ]),
            ));
        }
        Opcode::SelectSpectreGuard => {
            let control_value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64])
                }
            };
            let control_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                control_value_type,
            );
            let control_value = *select_random_value(&control_values_with_same_type, 0.4).unwrap();
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[
                        I8, I16, I32, I64, F32, F64, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[
                        I8, I16, I32, I64, F32, F64, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[
                        I8, I16, I32, I64, F32, F64, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[
                        I8, I16, I32, I64, F32, F64, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
            };
            let ref_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let ref_value1 = *select_random_value(&ref_values_with_same_type, 0.4).unwrap();
            let ref_value2 = *select_random_value(&ref_values_with_same_type, 0.4).unwrap();
            let new_value = cur
                .ins()
                .select_spectre_guard(control_value, ref_value1, ref_value2);
            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![
                    TypedValue::new(control_value, control_value_type),
                    TypedValue::new(ref_value1, value_type),
                    TypedValue::new(ref_value2, value_type),
                ]),
            ));
        }
        Opcode::Bitselect => {
            let control_value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[
                        I8, I16, I32, I64, F32, F64, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[
                        I8, I16, I32, I64, F32, F64, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
            };
            let control_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                control_value_type,
            );
            let control_value = *select_random_value(&control_values_with_same_type, 0.4).unwrap();
            let ref_value1 = *select_random_value(&control_values_with_same_type, 0.4).unwrap();
            let ref_value2 = *select_random_value(&control_values_with_same_type, 0.4).unwrap();
            let new_value = cur.ins().bitselect(control_value, ref_value1, ref_value2);
            return Some((
                Some(TypedValue::new(new_value, control_value_type)),
                Some(vec![
                    TypedValue::new(control_value, control_value_type),
                    TypedValue::new(ref_value1, control_value_type),
                    TypedValue::new(ref_value2, control_value_type),
                ]),
            ));
        }
        Opcode::X86Blendv => {
            return None;
        }
        Opcode::Fma => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
            };
            let random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );

            match random_values_with_same_type.len() {
                0 => return None,
                _ => {
                    let ref_value1 = *random_values_with_same_type.choose(&mut rng).unwrap();
                    let ref_value2 = *random_values_with_same_type.choose(&mut rng).unwrap();
                    let ref_value3 = *random_values_with_same_type.choose(&mut rng).unwrap();

                    let new_value = cur.ins().fma(ref_value1, ref_value2, ref_value3);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(ref_value1, value_type),
                            TypedValue::new(ref_value2, value_type),
                            TypedValue::new(ref_value3, value_type),
                        ]),
                    ));
                }
            }
        }
        Opcode::Insertlane => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2, F32X4, F64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2, F32X4, F64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2, F32X4, F64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2, F32X4, F64X2])
                }
            };
            let (result_type, max_lane) = extract_vector_type(value_type);
            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                _ => {
                    let ref_value = *random_values_with_same_type.choose(&mut rng).unwrap();

                    let mut random_inserted_values_with_same_type = get_dominator_values_with_type(
                        dominator_blocks,
                        block_dominator_values,
                        result_type,
                    );
                    let mut inserted_value = *random_inserted_values_with_same_type
                        .choose(&mut rng)
                        .unwrap();

                    let new_value = cur.ins().insertlane(
                        ref_value,
                        inserted_value,
                        Uimm8::from(rng.gen_range(0..=max_lane - 1)),
                    );
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(ref_value, value_type),
                            TypedValue::new(inserted_value, result_type),
                        ]),
                    ));
                }
            }
        }
        Opcode::Trap => {
            return None;
            cur.ins().trap(TrapCode::StackOverflow);
            return None;
        }

        Opcode::Splat => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2, F32X4, F64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2, F32X4, F64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2, F32X4, F64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2, F32X4, F64X2])
                }
            };
            let (lane_type, max_lane) = extract_vector_type(value_type);
            let random_values_with_same_type =
                get_dominator_values_with_type(dominator_blocks, block_dominator_values, lane_type);
            match random_values_with_same_type.len() {
                0 => return None,
                _ => {
                    let ref_value = *random_values_with_same_type.choose(&mut rng).unwrap();

                    let new_value = cur.ins().splat(value_type, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(ref_value, lane_type)]),
                    ));
                }
            }
        }
        Opcode::SetPinnedReg => {
            return None;
        }

        Opcode::VanyTrue => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2, F16X8, F32X4, F64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2, F32X4, F64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2, F32X4])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2, F32X4, F64X2])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let vanyed_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let boolean_value = cur.ins().vany_true(vanyed_value);
            return Some((
                Some(TypedValue::new(boolean_value, I8)),
                Some(vec![TypedValue::new(vanyed_value, value_type)]),
            ));
        }

        Opcode::VallTrue => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2, F16X8, F32X4, F64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2, F32X4, F64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2, F32X4])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2, F32X4, F64X2])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let valled_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let boolean_value = cur.ins().vall_true(valled_value);
            return Some((
                Some(TypedValue::new(boolean_value, I8)),
                Some(vec![TypedValue::new(valled_value, value_type)]),
            ));
        }

        Opcode::VhighBits => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            if dominator_values.len() == 0 {
                return None;
            }
            let vhighed_value = *select_random_value(&dominator_values, 0.4).unwrap();
            match value_type {
                I8X16 => {
                    let new_value = cur.ins().vhigh_bits(ir::types::I8, vhighed_value);
                    return Some((
                        Some(TypedValue::new(new_value, I8)),
                        Some(vec![TypedValue::new(vhighed_value, value_type)]),
                    ));
                }
                I16X8 => {
                    let new_value = cur.ins().vhigh_bits(ir::types::I16, vhighed_value);
                    return Some((
                        Some(TypedValue::new(new_value, I16)),
                        Some(vec![TypedValue::new(vhighed_value, value_type)]),
                    ));
                }
                I32X4 => {
                    let new_value = cur.ins().vhigh_bits(ir::types::I32, vhighed_value);
                    return Some((
                        Some(TypedValue::new(new_value, I32)),
                        Some(vec![TypedValue::new(vhighed_value, value_type)]),
                    ));
                }
                I64X2 => {
                    let new_value = cur.ins().vhigh_bits(ir::types::I64, vhighed_value);
                    return Some((
                        Some(TypedValue::new(new_value, I64)),
                        Some(vec![TypedValue::new(vhighed_value, value_type)]),
                    ));
                }
                _ => {
                    return None;
                }
            }
        }
        Opcode::Ineg => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            if dominator_values.len() == 0 {
                return None;
            }
            let neged_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let new_value = cur.ins().ineg(neged_value);
            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(neged_value, value_type)]),
            ));
        }
        Opcode::Iabs => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64, I8X16, I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64, I8X16, I16X8, I32X4, I64X2])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            if dominator_values.len() == 0 {
                return None;
            }
            let iabsed_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let new_value = cur.ins().iabs(iabsed_value);

            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(iabsed_value, value_type)]),
            ));
        }
        Opcode::Bnot => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, F16, F32, F64, I8X16, I16X8, I32X4, I64X2, F16X8,
                        F32X4, F64X2,
                    ])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[
                        I8, I16, I32, I64, I128, I8X16, I16X8, I32X4, I64X2, F32X4, F64X2,
                    ])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            if dominator_values.len() == 0 {
                return None;
            }
            let bnoted_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let new_value = cur.ins().bnot(bnoted_value);
            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(bnoted_value, value_type)]),
            ));
        }
        Opcode::Bitrev => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            if dominator_values.len() == 0 {
                return None;
            }
            let bitreved_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let new_value = cur.ins().bitrev(bitreved_value);

            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(bitreved_value, value_type)]),
            ));
        }
        Opcode::Clz => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            if dominator_values.len() == 0 {
                return None;
            }
            let clzed_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let new_value = cur.ins().clz(clzed_value);

            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(clzed_value, value_type)]),
            ));
        }
        #[cfg(not(feature = "x86-64"))]
        Opcode::Cls => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            if dominator_values.len() == 0 {
                return None;
            }
            let clsed_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let new_value = cur.ins().clz(clsed_value);

            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(clsed_value, value_type)]),
            ));
        }
        Opcode::Ctz => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            if dominator_values.len() == 0 {
                return None;
            }
            let ctzed_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let new_value = cur.ins().ctz(ctzed_value);

            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(ctzed_value, value_type)]),
            ));
        }
        Opcode::Bswap => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I16, I32, I64, I128])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I16, I32, I64, I128])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I16, I32, I64, I128])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I16, I32, I64, I128])
                }
            };

            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            if dominator_values.len() == 0 {
                return None;
            }
            let bswaped_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let new_value = cur.ins().bswap(bswaped_value);

            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(bswaped_value, value_type)]),
            ));
        }
        Opcode::Popcnt => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64, I128, I8X16])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            if dominator_values.len() == 0 {
                return None;
            }
            let popcnted_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let new_value = cur.ins().popcnt(popcnted_value);

            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(popcnted_value, value_type)]),
            ));
        }
        Opcode::Sqrt => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[F32, F64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let sqrted_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let new_value = cur.ins().sqrt(sqrted_value);

            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(sqrted_value, value_type)]),
            ));
        }
        Opcode::Fneg => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let fneged_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let new_value = cur.ins().fneg(fneged_value);

            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(fneged_value, value_type)]),
            ));
        }
        Opcode::Fabs => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let fabsed_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let new_value = cur.ins().fabs(fabsed_value);

            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(fabsed_value, value_type)]),
            ));
        }
        Opcode::Ceil => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let ceiled_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let new_value = cur.ins().ceil(ceiled_value);

            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(ceiled_value, value_type)]),
            ));
        }
        Opcode::Floor => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let floored_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let new_value = cur.ins().floor(floored_value);

            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(floored_value, value_type)]),
            ));
        }
        Opcode::Trunc => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let trunced_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let new_value = cur.ins().trunc(trunced_value);

            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(trunced_value, value_type)]),
            ));
        }
        Opcode::Nearest => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let nearested_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let new_value = cur.ins().nearest(nearested_value);

            return Some((
                Some(TypedValue::new(new_value, value_type)),
                Some(vec![TypedValue::new(nearested_value, value_type)]),
            ));
        }

        Opcode::ScalarToVector => {
            let result_value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I16X8, I32X4, I64X2, F32X4, F64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2, F32X4, F64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2, F32X4])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8X16, I16X8, I32X4, I64X2, F32X4, F64X2])
                }
            };
            let (value_type, max_lane) = extract_vector_type(result_value_type);
            let mut candidate_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match candidate_values.len() {
                0 => return None,
                _ => {
                    let param_value = *candidate_values.choose(&mut rng).unwrap();
                    let new_value = cur.ins().scalar_to_vector(result_value_type, param_value);
                    return Some((
                        Some(TypedValue::new(new_value, result_value_type)),
                        Some(vec![TypedValue::new(param_value, value_type)]),
                    ));
                }
            }
        }
        Opcode::Bmask => {
            let target_value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
            };
            let param_value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32, I64, I128])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                param_value_type,
            );
            let bmasked_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let new_value = cur.ins().bmask(target_value_type, bmasked_value);

            return Some((
                Some(TypedValue::new(new_value, target_value_type)),
                Some(vec![TypedValue::new(bmasked_value, param_value_type)]),
            ));
        }
        Opcode::Ireduce => {
            let to_value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I8, I16, I32])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I8, I16, I32])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I8, I16, I32])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I8, I16, I32])
                }
            };
            let from_value_type = match to_value_type {
                I8 => random_type(&[I16, I32, I64]),
                I16 => random_type(&[I32, I64]),
                I32 => random_type(&[I64]),
                _ => panic!("the from type of ireduce instr is unexpected!"),
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                from_value_type,
            );
            let ireduced_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let new_value = cur.ins().ireduce(to_value_type, ireduced_value);

            return Some((
                Some(TypedValue::new(new_value, to_value_type)),
                Some(vec![TypedValue::new(ireduced_value, from_value_type)]),
            ));
        }

        Opcode::SwidenLow => {
            let to_value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I16X8, I32X4, I64X2])
                }
            };
            let from_value_type = match to_value_type {
                I16X8 => I8X16,
                I32X4 => I16X8,
                I64X2 => I32X4,
                _ => panic!("the from value type of swidenlow instr is unexpected!"),
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                from_value_type,
            );
            let swidenlowed_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let new_value = cur.ins().swiden_low(swidenlowed_value);

            return Some((
                Some(TypedValue::new(new_value, to_value_type)),
                Some(vec![TypedValue::new(swidenlowed_value, from_value_type)]),
            ));
        }

        Opcode::SwidenHigh => {
            let to_value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I16X8, I32X4, I64X2])
                }
            };
            let from_value_type = match to_value_type {
                I16X8 => I8X16,
                I32X4 => I16X8,
                I64X2 => I32X4,
                _ => panic!("the from value type of swidenhigh instr is unexpected!"),
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                from_value_type,
            );
            let swidenhighed_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let new_value = cur.ins().swiden_high(swidenhighed_value);

            return Some((
                Some(TypedValue::new(new_value, to_value_type)),
                Some(vec![TypedValue::new(swidenhighed_value, from_value_type)]),
            ));
        }

        Opcode::UwidenLow => {
            let to_value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I16X8, I32X4, I64X2])
                }
            };
            let from_value_type = match to_value_type {
                I16X8 => I8X16,
                I32X4 => I16X8,
                I64X2 => I32X4,
                _ => panic!("the from value type of swidenhigh instr is unexpected!"),
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                from_value_type,
            );
            let uwidenlowed_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let new_value = cur.ins().uwiden_low(uwidenlowed_value);

            return Some((
                Some(TypedValue::new(new_value, to_value_type)),
                Some(vec![TypedValue::new(uwidenlowed_value, from_value_type)]),
            ));
        }

        Opcode::UwidenHigh => {
            let to_value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I16X8, I32X4, I64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I16X8, I32X4, I64X2])
                }
            };
            let from_value_type = match to_value_type {
                I16X8 => I8X16,
                I32X4 => I16X8,
                I64X2 => I32X4,
                _ => panic!("the from value type of swidenhigh instr is unexpected!"),
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                from_value_type,
            );
            let uwidenhighed_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let new_value = cur.ins().uwiden_high(uwidenhighed_value);

            return Some((
                Some(TypedValue::new(new_value, to_value_type)),
                Some(vec![TypedValue::new(uwidenhighed_value, from_value_type)]),
            ));
        }
        Opcode::Uextend => {
            /*
            ;; I{8,16} -> I32
            ;; I8 -> I16
            ;; I{8,16,32} -> I64.
            ;; I{8,16,32,64} -> I128.
            */
            let to_value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I16, I32, I64, I128])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I16, I32, I64, I128])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I16, I32, I64, I128])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I16, I32, I64, I128])
                }
            };
            let from_value_type = match to_value_type {
                I16 => random_type(&[I8]),
                I32 => random_type(&[I8, I16]),
                I64 => random_type(&[I8, I16, I32]),
                I128 => random_type(&[I8, I16, I32, I64]),
                _ => panic!("the from type of ireduce instr is unexpected!"),
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                from_value_type,
            );
            let uextended_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let new_value = cur.ins().uextend(to_value_type, uextended_value);

            return Some((
                Some(TypedValue::new(new_value, to_value_type)),
                Some(vec![TypedValue::new(uextended_value, from_value_type)]),
            ));
        }
        Opcode::Sextend => {
            let to_value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I16, I32, I64, I128])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I16, I32, I64, I128])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I16, I32, I64, I128])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I16, I32, I64, I128])
                }
            };
            let from_value_type = match to_value_type {
                I16 => random_type(&[I8]),
                I32 => random_type(&[I8, I16]),
                I64 => random_type(&[I8, I16, I32]),
                I128 => random_type(&[I8, I16, I32, I64]),
                _ => panic!("the from type of ireduce instr is unexpected!"),
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                from_value_type,
            );
            let sextended_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let new_value = cur.ins().sextend(to_value_type, sextended_value);

            return Some((
                Some(TypedValue::new(new_value, to_value_type)),
                Some(vec![TypedValue::new(sextended_value, from_value_type)]),
            ));
        }
        Opcode::Fpromote => {
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                ir::types::F32,
            );
            let fpromoted_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let new_value = cur.ins().fpromote(F64, fpromoted_value);

            return Some((
                Some(TypedValue::new(new_value, ir::types::F64)),
                Some(vec![TypedValue::new(fpromoted_value, ir::types::F32)]),
            ));
        }
        Opcode::Fdemote => {
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                ir::types::F64,
            );
            let fdemoted_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let new_value = cur.ins().fdemote(ir::types::F32, fdemoted_value);

            return Some((
                Some(TypedValue::new(new_value, ir::types::F32)),
                Some(vec![TypedValue::new(fdemoted_value, ir::types::F64)]),
            ));
        }
        Opcode::Fvdemote => {
            let dominator_values =
                get_dominator_values_with_type(dominator_blocks, block_dominator_values, F64X2);
            let fvdemoted_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let new_value = cur.ins().fvdemote(fvdemoted_value);

            return Some((
                Some(TypedValue::new(new_value, ir::types::F32X4)),
                Some(vec![TypedValue::new(fvdemoted_value, ir::types::F64X2)]),
            ));
        }
        Opcode::FvpromoteLow => {
            let dominator_values =
                get_dominator_values_with_type(dominator_blocks, block_dominator_values, F32X4);
            let fvpromotelowed_value = *select_random_value(&dominator_values, 0.4).unwrap();
            let new_value = cur.ins().fvpromote_low(fvpromotelowed_value);

            return Some((
                Some(TypedValue::new(new_value, ir::types::F64X2)),
                Some(vec![TypedValue::new(fvpromotelowed_value, F32X4)]),
            ));
        }
        Opcode::FcvtToUint => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[F32, F64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[F32, F64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[F32, F64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[F32, F64])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let fcvttouinted_value = *select_random_value(&dominator_values, 0.4).unwrap();
            match value_type {
                F32 => {
                    let new_value = cur.ins().fcvt_to_uint(ir::types::I32, fcvttouinted_value);
                    return Some((
                        Some(TypedValue::new(new_value, I32)),
                        Some(vec![TypedValue::new(fcvttouinted_value, value_type)]),
                    ));
                }
                F64 => {
                    let new_value = cur.ins().fcvt_to_uint(ir::types::I64, fcvttouinted_value);
                    return Some((
                        Some(TypedValue::new(new_value, I64)),
                        Some(vec![TypedValue::new(fcvttouinted_value, value_type)]),
                    ));
                }
                _ => {
                    return None;
                }
            }
        }
        Opcode::FcvtToSint => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[F32, F64])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[F32, F64])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[F32, F64])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[F32, F64])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let fcvttosinted_value = *select_random_value(&dominator_values, 0.4).unwrap();

            match value_type {
                F32 => {
                    let new_value = cur.ins().fcvt_to_sint(ir::types::I32, fcvttosinted_value);
                    return Some((
                        Some(TypedValue::new(new_value, I32)),
                        Some(vec![TypedValue::new(fcvttosinted_value, value_type)]),
                    ));
                }
                F64 => {
                    let new_value = cur.ins().fcvt_to_sint(ir::types::I64, fcvttosinted_value);
                    return Some((
                        Some(TypedValue::new(new_value, I64)),
                        Some(vec![TypedValue::new(fcvttosinted_value, value_type)]),
                    ));
                }
                _ => {
                    return None;
                }
            }
        }
        Opcode::FcvtToUintSat => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[F32, F64, F32X4])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let fcvttouintsated_value = *select_random_value(&dominator_values, 0.4).unwrap();

            match value_type {
                F32 => {
                    let new_value = cur.ins().fcvt_to_uint_sat(I32, fcvttouintsated_value);
                    return Some((
                        Some(TypedValue::new(new_value, I32)),
                        Some(vec![TypedValue::new(fcvttouintsated_value, value_type)]),
                    ));
                }
                F64 => {
                    let new_value = cur.ins().fcvt_to_uint_sat(I64, fcvttouintsated_value);
                    return Some((
                        Some(TypedValue::new(new_value, I64)),
                        Some(vec![TypedValue::new(fcvttouintsated_value, value_type)]),
                    ));
                }
                F32X4 => {
                    let new_value = cur.ins().fcvt_to_uint_sat(I32X4, fcvttouintsated_value);
                    return Some((
                        Some(TypedValue::new(new_value, I32X4)),
                        Some(vec![TypedValue::new(fcvttouintsated_value, value_type)]),
                    ));
                }
                F64X2 => {
                    let new_value = cur.ins().fcvt_to_uint_sat(I64X2, fcvttouintsated_value);
                    return Some((
                        Some(TypedValue::new(new_value, I64X2)),
                        Some(vec![TypedValue::new(fcvttouintsated_value, value_type)]),
                    ));
                }
                _ => {
                    return None;
                }
            }
        }
        Opcode::FcvtToSintSat => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[F32, F64, F32X4])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[F32, F64, F32X4, F64X2])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let fcvttosintsated_value = *select_random_value(&dominator_values, 0.4).unwrap();

            match value_type {
                F32 => {
                    let new_value = cur.ins().fcvt_to_sint_sat(I32, fcvttosintsated_value);
                    return Some((
                        Some(TypedValue::new(new_value, I32)),
                        Some(vec![TypedValue::new(fcvttosintsated_value, value_type)]),
                    ));
                }
                F64 => {
                    let new_value = cur.ins().fcvt_to_sint_sat(I64, fcvttosintsated_value);
                    return Some((
                        Some(TypedValue::new(new_value, I64)),
                        Some(vec![TypedValue::new(fcvttosintsated_value, value_type)]),
                    ));
                }
                F32X4 => {
                    let new_value = cur.ins().fcvt_to_sint_sat(I32X4, fcvttosintsated_value);
                    return Some((
                        Some(TypedValue::new(new_value, I32X4)),
                        Some(vec![TypedValue::new(fcvttosintsated_value, value_type)]),
                    ));
                }
                F64X2 => {
                    let new_value = cur.ins().fcvt_to_sint_sat(I64X2, fcvttosintsated_value);
                    return Some((
                        Some(TypedValue::new(new_value, I64X2)),
                        Some(vec![TypedValue::new(fcvttosintsated_value, value_type)]),
                    ));
                }
                _ => {
                    return None;
                }
            }
        }
        #[cfg(feature = "x86-64")]
        Opcode::X86Cvtt2dq => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[F32X4])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[F32X4, F64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[F32X4, F64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[F32X4, F64X2])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let x86cvtt2dqed_value = *select_random_value(&dominator_values, 0.4).unwrap();

            match value_type {
                F32X4 => {
                    let new_value = cur.ins().x86_cvtt2dq(I32X4, x86cvtt2dqed_value);
                    return Some((
                        Some(TypedValue::new(new_value, I32X4)),
                        Some(vec![TypedValue::new(x86cvtt2dqed_value, value_type)]),
                    ));
                }
                F64X2 => {
                    let new_value = cur.ins().x86_cvtt2dq(I64X2, x86cvtt2dqed_value);
                    return Some((
                        Some(TypedValue::new(new_value, I64X2)),
                        Some(vec![TypedValue::new(x86cvtt2dqed_value, value_type)]),
                    ));
                }
                _ => {
                    return None;
                }
            }
        }
        Opcode::FcvtFromUint => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I32, I64, I32X4, I64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I32, I64, I32X4, I64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I32, I64, I32X4, I64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I32, I64, I32X4, I64X2])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let fcvtfromuinted_value = *select_random_value(&dominator_values, 0.4).unwrap();

            match value_type {
                I32 => {
                    let new_value = cur.ins().fcvt_from_uint(F32, fcvtfromuinted_value);
                    return Some((
                        Some(TypedValue::new(new_value, F32)),
                        Some(vec![TypedValue::new(fcvtfromuinted_value, value_type)]),
                    ));
                }
                I64 => {
                    let new_value = cur.ins().fcvt_from_uint(F64, fcvtfromuinted_value);
                    return Some((
                        Some(TypedValue::new(new_value, F64)),
                        Some(vec![TypedValue::new(fcvtfromuinted_value, value_type)]),
                    ));
                }
                I32X4 => {
                    let new_value = cur.ins().fcvt_from_uint(F32X4, fcvtfromuinted_value);
                    return Some((
                        Some(TypedValue::new(new_value, F32X4)),
                        Some(vec![TypedValue::new(fcvtfromuinted_value, value_type)]),
                    ));
                }
                I64X2 => {
                    let new_value = cur.ins().fcvt_from_uint(F64X2, fcvtfromuinted_value);
                    return Some((
                        Some(TypedValue::new(new_value, F64X2)),
                        Some(vec![TypedValue::new(fcvtfromuinted_value, value_type)]),
                    ));
                }
                _ => {
                    return None;
                }
            }
        }
        Opcode::FcvtFromSint => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I32, I64, I32X4, I64X2])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I32, I64, I32X4, I64X2])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I32, I64, I32X4, I64X2])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I32, I64, I32X4, I64X2])
                }
            };
            let dominator_values = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            let fcvtfromsinted_value = *select_random_value(&dominator_values, 0.4).unwrap();

            match value_type {
                I32 => {
                    let new_value = cur.ins().fcvt_from_sint(F32, fcvtfromsinted_value);
                    return Some((
                        Some(TypedValue::new(new_value, F32)),
                        Some(vec![TypedValue::new(fcvtfromsinted_value, value_type)]),
                    ));
                }
                I64 => {
                    let new_value = cur.ins().fcvt_from_sint(F64, fcvtfromsinted_value);
                    return Some((
                        Some(TypedValue::new(new_value, F64)),
                        Some(vec![TypedValue::new(fcvtfromsinted_value, value_type)]),
                    ));
                }
                I32X4 => {
                    let new_value = cur.ins().fcvt_from_sint(F32X4, fcvtfromsinted_value);
                    return Some((
                        Some(TypedValue::new(new_value, F32X4)),
                        Some(vec![TypedValue::new(fcvtfromsinted_value, value_type)]),
                    ));
                }
                I64X2 => {
                    let new_value = cur.ins().fcvt_from_sint(F64X2, fcvtfromsinted_value);
                    return Some((
                        Some(TypedValue::new(new_value, F64X2)),
                        Some(vec![TypedValue::new(fcvtfromsinted_value, value_type)]),
                    ));
                }
                _ => {
                    return None;
                }
            }
        }
        Opcode::Isplit => {
            return None;
        }
        Opcode::F128const => {
            return None;
            let random_u128: u128 = rng.gen();
            let ieee128_value: Ieee128 = Ieee128::with_bits(random_u128);
            let f128_constant = cur.func.dfg.constants.insert(ieee128_value.into());

            let new_value = cur.ins().f128const(f128_constant);
            return Some((Some(TypedValue::new(new_value, F128)), None));
        }
        Opcode::Vconst => {
            return None;
        }

        Opcode::GlobalValue => {
            return None;
        }
        Opcode::SymbolValue => {
            return None;
        }
        Opcode::TlsValue => {
            return None;
        }
        #[cfg(not(feature = "s390x"))]
        Opcode::F16const => {
            return None;
            let new_value = cur.ins().f16const(Ieee16::with_bits(rng.random::<u16>()));
            return Some((Some(TypedValue::new(new_value, ir::types::F16)), None));
        }
        Opcode::F32const => {
            let new_value = cur.ins().f32const(Ieee32::from(rng.random::<f32>()));
            return Some((Some(TypedValue::new(new_value, ir::types::F32)), None));
        }
        Opcode::F64const => {
            let new_value = cur.ins().f64const(Ieee64::from(rng.random::<f64>()));
            return Some((Some(TypedValue::new(new_value, ir::types::F64)), None));
        }
        Opcode::Iconst => {
            let choice = rng.gen_range(0..4);
            match choice {
                0 => {
                    let i8_value = cur
                        .ins()
                        .iconst(ir::types::I8, Imm64::from(rng.random::<i64>()));
                    return Some((Some(TypedValue::new(i8_value, ir::types::I8)), None));
                }
                1 => {
                    let i16_value = cur
                        .ins()
                        .iconst(ir::types::I16, Imm64::from(rng.random::<i64>()));
                    return Some((Some(TypedValue::new(i16_value, ir::types::I16)), None));
                }
                2 => {
                    let i32_value = cur
                        .ins()
                        .iconst(ir::types::I32, Imm64::from(rng.random::<i64>()));
                    return Some((Some(TypedValue::new(i32_value, ir::types::I32)), None));
                }
                _ => {
                    let i64_value = cur
                        .ins()
                        .iconst(ir::types::I64, Imm64::from(rng.random::<i64>()));
                    return Some((Some(TypedValue::new(i64_value, ir::types::I64)), None));
                }
            }
        }
        #[cfg(feature = "x86-64")]
        Opcode::X86Pmulhrsw => {
            let value_type = {
                #[cfg(feature = "x86-64")]
                {
                    random_type(&[I16X8])
                }
                #[cfg(feature = "aarch64")]
                {
                    random_type(&[I16X8])
                }
                #[cfg(feature = "riscv")]
                {
                    random_type(&[I16X8])
                }
                #[cfg(feature = "s390x")]
                {
                    random_type(&[I16X8])
                }
            };
            let mut random_values_with_same_type = get_dominator_values_with_type(
                dominator_blocks,
                block_dominator_values,
                value_type,
            );
            match random_values_with_same_type.len() {
                0 => return None,
                1 => {
                    let ref_value = random_values_with_same_type.pop().unwrap();
                    let new_value = cur.ins().x86_pmulhrsw(ref_value, ref_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![TypedValue::new(new_value, value_type)]),
                    ));
                }
                _ => {
                    let first_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();
                    let second_value =
                        *select_random_value(&random_values_with_same_type, 0.4).unwrap();

                    let new_value = cur.ins().x86_pmulhrsw(first_value, second_value);
                    return Some((
                        Some(TypedValue::new(new_value, value_type)),
                        Some(vec![
                            TypedValue::new(first_value, value_type),
                            TypedValue::new(second_value, value_type),
                        ]),
                    ));
                }
            }
        }
        Opcode::ReturnCall => {
            return None;
        }
        _ => {
            return None;
            panic!("unrecognized instr")
        }
    };

    return None;
}
