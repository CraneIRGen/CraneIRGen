pub mod dominator_tree;
pub mod instruction_selector;

use crate::dominator_tree::compute_dominators;
use crate::instruction_selector::{
    get_dominator_values_with_type, get_random_cond_value, populate_block_instructions,
    select_random_value, TypedValue,
};
use bytemuck::{bytes_of, cast_ref};
use cg_constructor::{generate_random_signature, FunctionNode};
use commons::fixed_rng::gen_and_print_range;
use cranelift_codegen::cursor::{Cursor, CursorPosition, FuncCursor};
use cranelift_codegen::entity::EntityRef;
use cranelift_codegen::flowgraph::{BlockPredecessor, ControlFlowGraph};
use cranelift_codegen::ir;
use cranelift_codegen::ir::immediates::{Ieee128, Offset32, V128Imm};
use cranelift_codegen::ir::types::*;
use cranelift_codegen::ir::{
    types, ArgumentPurpose, Block, BlockCall, ConstantData, Endianness, ExtFuncData, ExternalName,
    FuncRef, Function, GlobalValueData, Inst, InstBuilder, InstructionData, JumpTableData,
    JumpTables, Opcode, StackSlotData, StackSlotKind, Type, UserExternalName, Value, ValueList,
};
use mongodb::bson::{doc, from_bson, Bson};
use mongodb::{
    bson,
    bson::Document,
    sync::{Client, Collection},
};
use rand::prelude::{IndexedRandom, IteratorRandom};
use rand::{thread_rng, Rng};
use serde::{Deserialize, Serialize};
use serde_json::Value as JsonValue;
use std::borrow::BorrowMut;
use std::collections::{HashMap, HashSet};
use std::io::Write;
use wide::{f32x4, f64x2, i16x8, i32x4, i64x2, i8x16};

#[derive(Debug, Serialize, Deserialize)]
struct BlockJson {
    instrs: Vec<JsonValue>,
    block_type: Vec<JsonValue>,
    context: Vec<JsonValue>,
}

impl BlockJson {
    fn new() -> Self {
        Self {
            instrs: Vec::new(),
            block_type: Vec::new(),
            context: Vec::new(),
        }
    }

    fn add_instr(&mut self, json: JsonValue) {
        self.instrs.push(json)
    }

    fn add_block_type(&mut self, json: JsonValue) {
        self.block_type.push(json)
    }

    fn add_context(&mut self, json: JsonValue) {
        self.context.push(json)
    }

    fn to_json_string(&self) -> anyhow::Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }

    fn from_json_string(json_str: &str) -> anyhow::Result<Self, serde_json::Error> {
        serde_json::from_str(json_str)
    }
}

fn dfs(
    cfg: &ControlFlowGraph,
    node: Block,
    visited: &mut HashSet<Block>,
    dfs_order: &mut Vec<Block>,
) {
    visited.insert(node);
    dfs_order.push(node);

    for successor in cfg.succ_iter(node) {
        if !visited.contains(&successor) {
            dfs(&cfg, successor, visited, dfs_order);
        }
    }
}

pub fn function_generator(
    func: &mut Function,
    is_root_func: bool,
    all_documents: &Vec<Document>,
) -> (
    HashMap<Block, HashSet<Block>>,
    HashMap<Block, HashSet<TypedValue>>,
) {
    fn get_random_instr_snippet(collection: &Collection<Document>) -> Vec<InstructionData> {
        let mut instr_snippet: Vec<InstructionData> = vec![];

        loop {
            let pipeline = vec![doc! { "$sample": { "size": 1 } }];
            let mut cursor = collection.aggregate(pipeline).run().unwrap();

            if let Some(result) = cursor.next() {
                match result {
                    Ok(document) => {
                        let block: BlockJson = from_bson(Bson::Document(document.clone())).unwrap();
                        if block.instrs.len() <= 200 {
                            for instr in block.instrs {
                                let instr_data: InstructionData =
                                    serde_json::from_str(&instr.to_string()).unwrap();
                                instr_snippet.push(instr_data);
                                println!("Deserialized instr data are: {:?}\n", instr_data);
                            }

                            break;
                        } else {
                            continue;
                        }
                    }
                    Err(e) => panic!("Error getting document: {:?}\n", e),
                }
            }
        }

        instr_snippet
    }

    fn get_instr_snippet_200_list(collection: &Collection<Document>) -> Vec<Vec<InstructionData>> {
        let mut find_result = collection.find(Document::new());
        let mut cursor = find_result.run().unwrap();
        let mut instr_snippet_list: Vec<Vec<InstructionData>> = vec![];

        while let Some(result) = cursor.next() {
            match result {
                Ok(document) => {
                    if let Some(instrs) = document.get_array("instrs").ok() {
                        if instrs.len() <= 200 {
                            let mut instr_snippet = vec![];
                            for instr in instrs {
                                match serde_json::from_str(&instr.to_string()) {
                                    Ok(instr_data) => instr_snippet.push(instr_data),
                                    Err(e) => {
                                        println!("Error serde json: {:?}\n", e);
                                        continue;
                                    }
                                }
                            }
                            instr_snippet_list.push(instr_snippet);
                        }
                    }
                }
                Err(e) => panic!("Error getting document: {:?}\n", e),
            }
        }

        instr_snippet_list
    }

    fn get_instr_snippet_10_list(collection: &Collection<Document>) -> Vec<Vec<InstructionData>> {
        let filter = doc! {
            "$expr": {
                "$lt": [{ "$size": "$instrs" }, 10]
            }
        };

        let mut find_result = collection.find(filter);
        let mut cursor = find_result.run().unwrap();
        let mut instr_snippet_list: Vec<Vec<InstructionData>> = vec![];

        while let Some(result) = cursor.next() {
            match result {
                Ok(document) => {
                    if let Some(instrs) = document.get_array("instrs").ok() {
                        let mut instr_snippet = vec![];
                        for instr in instrs {
                            match serde_json::from_str(&instr.to_string()) {
                                Ok(instr_data) => instr_snippet.push(instr_data),
                                Err(e) => {
                                    println!("Error serde json: {:?}\n", e);
                                    continue;
                                }
                            }
                        }
                        instr_snippet_list.push(instr_snippet);
                    }
                }
                Err(e) => panic!("Error getting document: {:?}\n", e),
            }
        }

        instr_snippet_list
    }

    fn get_instr_snippet_10_list_from_documents(
        all_documents: &Vec<Document>,
    ) -> Vec<Vec<InstructionData>> {
        let mut instr_snippet_list: Vec<Vec<InstructionData>> = vec![];

        for document in all_documents {
            if let Some(instrs) = document.get_array("instrs").ok() {
                if instrs.len() < 10 {
                    let mut instr_snippet = vec![];
                    for instr in instrs {
                        match serde_json::from_str(&instr.to_string()) {
                            Ok(instr_data) => instr_snippet.push(instr_data),
                            Err(e) => {
                                eprintln!("Error parsing instr: {:?}", e);
                                continue;
                            }
                        }
                    }
                    instr_snippet_list.push(instr_snippet);
                }
            }
        }

        instr_snippet_list
    }

    let mut sig = func.signature.clone();

    let instr_snippet_list = get_instr_snippet_10_list_from_documents(all_documents);

    let mut func_cursor = FuncCursor::new(func);
    let entry_block = func_cursor.layout().entry_block().unwrap();

    let mut dfs_order: Vec<Block> = vec![];
    {
        let cfg = ControlFlowGraph::with_function(func_cursor.func);

        let mut visited: HashSet<Block> = HashSet::new();
        dfs(&cfg, entry_block, &mut visited, &mut dfs_order);
    }

    let mut block_ref_values: HashMap<Block, HashSet<TypedValue>> = HashMap::new();

    let mut block_def_values: HashMap<Block, HashSet<TypedValue>> = HashMap::new();

    let dominator_block_set: HashMap<Block, HashSet<Block>> = compute_dominators(func_cursor.func);

    for (i, node) in dfs_order.iter().enumerate() {
        func_cursor.goto_first_insertion_point(*node);

        let mut rng = thread_rng();
        let mut instr_snippet = vec![];

        let mut def_values: HashSet<TypedValue> = HashSet::new();

        let mut ref_values: HashSet<TypedValue> = HashSet::new();

        if i == 0 {
            if sig.params.len() != 0 {
                for param_type in &sig.params {
                    let param_value = func_cursor
                        .func
                        .dfg
                        .append_block_param(*node, param_type.value_type);
                    def_values.insert(TypedValue::new(param_value, param_type.value_type));
                }
            }

            let ss0 = func_cursor.func.create_sized_stack_slot(StackSlotData::new(
                StackSlotKind::ExplicitSlot,
                32,
                0,
            ));
            let ss1 = func_cursor.func.create_sized_stack_slot(StackSlotData::new(
                StackSlotKind::ExplicitSlot,
                32,
                0,
            ));

            #[cfg(feature = "x86-64")]
            {
                let random_u16: u16 = rng.random();
                let random_i64: i64 = rng.random();
                let random_f32: f32 = rng.random();
                let random_f64: f64 = rng.random();

                let i8_value = func_cursor.ins().iconst(I8, random_i64);
                let i16_value = func_cursor.ins().iconst(I16, random_i64);
                let i32_value = func_cursor.ins().iconst(I32, random_i64);
                let i64_value = func_cursor.ins().iconst(I64, random_i64);
                let i128_value = func_cursor.ins().uextend(I128, i64_value);

                let f16_value = func_cursor
                    .ins()
                    .f16const(ir::immediates::Ieee16::with_bits(random_u16));
                let f32_value = func_cursor.ins().f32const(random_f32);
                let f64_value = func_cursor.ins().f64const(random_f64);

                let byte_slice: Vec<u8> = (0..16).map(|_| rng.gen()).collect();
                let v128_constant = func_cursor
                    .func
                    .dfg
                    .constants
                    .insert(ConstantData::from(byte_slice));

                let random_i8 = rng.random::<i8>();
                let random_i16 = rng.random::<i16>();
                let random_i32 = rng.random::<i32>();
                let random_i64 = rng.random::<i64>();

                let i8x16number = i8x16::new([random_i8; 16]);
                let i16x8number = i16x8::new([random_i16; 8]);
                let i32x4number = i32x4::new([random_i32; 4]);
                let i64x2number = i64x2::new([random_i64; 2]);
                let f32x4number = f32x4::new([random_f32; 4]);
                let f64x2number = f64x2::new([random_f64; 2]);

                let i8x16_number = cast_ref::<i8x16, [u8; 16]>(&i8x16number);
                let i16x8_number = cast_ref::<i16x8, [u8; 16]>(&i16x8number);
                let i32x4_number = cast_ref::<i32x4, [u8; 16]>(&i32x4number);
                let i64x2_number = cast_ref::<i64x2, [u8; 16]>(&i64x2number);
                let f32x4_number = cast_ref::<f32x4, [u8; 16]>(&f32x4number);
                let f64x2_number = cast_ref::<f64x2, [u8; 16]>(&f64x2number);

                let i8x16_constant = func_cursor
                    .func
                    .dfg
                    .constants
                    .insert(ConstantData::from(i8x16_number.to_vec()));
                let i16x8_constant = func_cursor
                    .func
                    .dfg
                    .constants
                    .insert(ConstantData::from(i16x8_number.to_vec()));
                let i32x4_constant = func_cursor
                    .func
                    .dfg
                    .constants
                    .insert(ConstantData::from(i32x4_number.to_vec()));
                let i64x2_constant = func_cursor
                    .func
                    .dfg
                    .constants
                    .insert(ConstantData::from(i64x2_number.to_vec()));
                let f32x4_constant = func_cursor
                    .func
                    .dfg
                    .constants
                    .insert(ConstantData::from(f32x4_number.to_vec()));
                let f64x2_constant = func_cursor
                    .func
                    .dfg
                    .constants
                    .insert(ConstantData::from(f64x2_number.to_vec()));

                let i8x16_value = func_cursor.ins().vconst(I8X16, i8x16_constant);
                let i16x8_value = func_cursor.ins().vconst(I16X8, i16x8_constant);
                let i32x4_value = func_cursor.ins().vconst(I32X4, i32x4_constant);
                let i64x2_value = func_cursor.ins().vconst(I64X2, i64x2_constant);

                let f16x8_value = func_cursor.ins().vconst(F16X8, v128_constant);
                let f32x4_value = func_cursor.ins().vconst(F32X4, f32x4_constant);
                let f64x2_value = func_cursor.ins().vconst(F64X2, f64x2_constant);

                let ss0_addr = func_cursor
                    .ins()
                    .stack_addr(ir::types::I64, ss0, Offset32::new(0));
                let ss1_addr = func_cursor
                    .ins()
                    .stack_addr(ir::types::I64, ss1, Offset32::new(0));
                let mut mem_flag_little = ir::MemFlags::new();
                mem_flag_little.set_endianness(Endianness::Little);
                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss0_addr, Offset32::new(0));
                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss0_addr, Offset32::new(8));
                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss0_addr, Offset32::new(16));
                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss0_addr, Offset32::new(24));

                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss1_addr, Offset32::new(0));
                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss1_addr, Offset32::new(8));
                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss1_addr, Offset32::new(16));
                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss1_addr, Offset32::new(24));

                def_values.insert(TypedValue::new(i8_value, I8));
                def_values.insert(TypedValue::new(i16_value, I16));
                def_values.insert(TypedValue::new(i32_value, I32));
                def_values.insert(TypedValue::new(i64_value, I64));
                def_values.insert(TypedValue::new(i128_value, I128));

                def_values.insert(TypedValue::new(f16_value, F16));
                def_values.insert(TypedValue::new(f32_value, F32));
                def_values.insert(TypedValue::new(f64_value, F64));

                def_values.insert(TypedValue::new(i8x16_value, I8X16));
                def_values.insert(TypedValue::new(i16x8_value, I16X8));
                def_values.insert(TypedValue::new(i32x4_value, I32X4));
                def_values.insert(TypedValue::new(i64x2_value, I64X2));
                def_values.insert(TypedValue::new(f16x8_value, F16X8));
                def_values.insert(TypedValue::new(f32x4_value, F32X4));
                def_values.insert(TypedValue::new(f64x2_value, F64X2));
            }

            #[cfg(feature = "aarch64")]
            {
                let random_i64: i64 = rng.random();
                let random_u16: u16 = rng.random();
                let random_f32: f32 = rng.random();
                let random_f64: f64 = rng.random();

                let i8_value = func_cursor.ins().iconst(I8, random_i64);
                let i16_value = func_cursor.ins().iconst(I16, random_i64);
                let i32_value = func_cursor.ins().iconst(I32, random_i64);
                let i64_value = func_cursor.ins().iconst(I64, random_i64);
                let i128_value = func_cursor.ins().uextend(I128, i64_value);

                let f16_value = func_cursor
                    .ins()
                    .f16const(ir::immediates::Ieee16::with_bits(random_u16));
                let f32_value = func_cursor.ins().f32const(random_f32);
                let f64_value = func_cursor.ins().f64const(random_f64);

                let random_u128: u128 = rng.gen();

                let byte_slice: Vec<u8> = (0..16).map(|_| rng.gen()).collect();
                let v128_constant = func_cursor
                    .func
                    .dfg
                    .constants
                    .insert(ConstantData::from(byte_slice));

                let random_i8 = rng.random::<i8>();
                let random_i16 = rng.random::<i16>();
                let random_i32 = rng.random::<i32>();
                let random_i64 = rng.random::<i64>();

                let i8x16number = i8x16::new([random_i8; 16]);
                let i16x8number = i16x8::new([random_i16; 8]);
                let i32x4number = i32x4::new([random_i32; 4]);
                let i64x2number = i64x2::new([random_i64; 2]);
                let f32x4number = f32x4::new([random_f32; 4]);
                let f64x2number = f64x2::new([random_f64; 2]);

                let i8x16_number = cast_ref::<i8x16, [u8; 16]>(&i8x16number);
                let i16x8_number = cast_ref::<i16x8, [u8; 16]>(&i16x8number);
                let i32x4_number = cast_ref::<i32x4, [u8; 16]>(&i32x4number);
                let i64x2_number = cast_ref::<i64x2, [u8; 16]>(&i64x2number);
                let f32x4_number = cast_ref::<f32x4, [u8; 16]>(&f32x4number);
                let f64x2_number = cast_ref::<f64x2, [u8; 16]>(&f64x2number);

                let i8x16_constant = func_cursor
                    .func
                    .dfg
                    .constants
                    .insert(ConstantData::from(i8x16_number.to_vec()));
                let i16x8_constant = func_cursor
                    .func
                    .dfg
                    .constants
                    .insert(ConstantData::from(i16x8_number.to_vec()));
                let i32x4_constant = func_cursor
                    .func
                    .dfg
                    .constants
                    .insert(ConstantData::from(i32x4_number.to_vec()));
                let i64x2_constant = func_cursor
                    .func
                    .dfg
                    .constants
                    .insert(ConstantData::from(i64x2_number.to_vec()));
                let f32x4_constant = func_cursor
                    .func
                    .dfg
                    .constants
                    .insert(ConstantData::from(f32x4_number.to_vec()));
                let f64x2_constant = func_cursor
                    .func
                    .dfg
                    .constants
                    .insert(ConstantData::from(f64x2_number.to_vec()));

                let i8x16_value = func_cursor.ins().vconst(I8X16, i8x16_constant);
                let i16x8_value = func_cursor.ins().vconst(I16X8, i16x8_constant);
                let i32x4_value = func_cursor.ins().vconst(I32X4, i32x4_constant);
                let i64x2_value = func_cursor.ins().vconst(I64X2, i64x2_constant);

                let f32x4_value = func_cursor.ins().vconst(F32X4, f32x4_constant);
                let f64x2_value = func_cursor.ins().vconst(F64X2, f64x2_constant);

                let ss0_addr = func_cursor
                    .ins()
                    .stack_addr(ir::types::I64, ss0, Offset32::new(0));
                let ss1_addr = func_cursor
                    .ins()
                    .stack_addr(ir::types::I64, ss1, Offset32::new(0));
                let mut mem_flag_little = ir::MemFlags::new();
                mem_flag_little.set_endianness(Endianness::Little);
                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss0_addr, Offset32::new(0));
                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss0_addr, Offset32::new(8));
                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss0_addr, Offset32::new(16));
                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss0_addr, Offset32::new(24));

                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss1_addr, Offset32::new(0));
                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss1_addr, Offset32::new(8));
                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss1_addr, Offset32::new(16));
                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss1_addr, Offset32::new(24));

                def_values.insert(TypedValue::new(i8_value, I8));
                def_values.insert(TypedValue::new(i16_value, I16));
                def_values.insert(TypedValue::new(i32_value, I32));
                def_values.insert(TypedValue::new(i64_value, I64));

                def_values.insert(TypedValue::new(f16_value, F16));
                def_values.insert(TypedValue::new(f32_value, F32));
                def_values.insert(TypedValue::new(f64_value, F64));

                def_values.insert(TypedValue::new(i128_value, I128));

                def_values.insert(TypedValue::new(i8x16_value, I8X16));
                def_values.insert(TypedValue::new(i16x8_value, I16X8));
                def_values.insert(TypedValue::new(i32x4_value, I32X4));
                def_values.insert(TypedValue::new(i64x2_value, I64X2));

                def_values.insert(TypedValue::new(f32x4_value, F32X4));
                def_values.insert(TypedValue::new(f64x2_value, F64X2));
            }

            #[cfg(feature = "riscv")]
            {
                use bytemuck::cast_ref;

                let random_i64: i64 = rng.random();
                let random_u16: u16 = rng.random();
                let random_f32: f32 = rng.random();
                let random_f64: f64 = rng.random();

                let i8_value = func_cursor.ins().iconst(I8, random_i64);
                let i16_value = func_cursor.ins().iconst(I16, random_i64);
                let i32_value = func_cursor.ins().iconst(I32, random_i64);
                let i64_value = func_cursor.ins().iconst(I64, random_i64);
                let i128_value = func_cursor.ins().uextend(I128, i64_value);

                let f32_value = func_cursor.ins().f32const(random_f32);
                let f64_value = func_cursor.ins().f64const(random_f64);

                let random_u128: u128 = rng.gen();

                let byte_slice: Vec<u8> = (0..16).map(|_| rng.gen()).collect();
                let v128_constant = func_cursor
                    .func
                    .dfg
                    .constants
                    .insert(ConstantData::from(byte_slice));

                let random_i8 = rng.random::<i8>();
                let random_i16 = rng.random::<i16>();
                let random_i32 = rng.random::<i32>();
                let random_i64 = rng.random::<i64>();

                let i8x16number = i8x16::new([random_i8; 16]);
                let i16x8number = i16x8::new([random_i16; 8]);
                let i32x4number = i32x4::new([random_i32; 4]);
                let i64x2number = i64x2::new([random_i64; 2]);
                let f32x4number = f32x4::new([random_f32; 4]);
                let f64x2number = f64x2::new([random_f64; 2]);

                let i8x16_number = cast_ref::<i8x16, [u8; 16]>(&i8x16number);
                let i16x8_number = cast_ref::<i16x8, [u8; 16]>(&i16x8number);
                let i32x4_number = cast_ref::<i32x4, [u8; 16]>(&i32x4number);
                let i64x2_number = cast_ref::<i64x2, [u8; 16]>(&i64x2number);
                let f32x4_number = cast_ref::<f32x4, [u8; 16]>(&f32x4number);
                let f64x2_number = cast_ref::<f64x2, [u8; 16]>(&f64x2number);

                let i8x16_constant = func_cursor
                    .func
                    .dfg
                    .constants
                    .insert(ConstantData::from(i8x16_number.to_vec()));
                let i16x8_constant = func_cursor
                    .func
                    .dfg
                    .constants
                    .insert(ConstantData::from(i16x8_number.to_vec()));
                let i32x4_constant = func_cursor
                    .func
                    .dfg
                    .constants
                    .insert(ConstantData::from(i32x4_number.to_vec()));
                let i64x2_constant = func_cursor
                    .func
                    .dfg
                    .constants
                    .insert(ConstantData::from(i64x2_number.to_vec()));
                let f32x4_constant = func_cursor
                    .func
                    .dfg
                    .constants
                    .insert(ConstantData::from(f32x4_number.to_vec()));
                let f64x2_constant = func_cursor
                    .func
                    .dfg
                    .constants
                    .insert(ConstantData::from(f64x2_number.to_vec()));

                let i8x16_value = func_cursor.ins().vconst(I8X16, i8x16_constant);
                let i16x8_value = func_cursor.ins().vconst(I16X8, i16x8_constant);
                let i32x4_value = func_cursor.ins().vconst(I32X4, i32x4_constant);
                let i64x2_value = func_cursor.ins().vconst(I64X2, i64x2_constant);

                let f32x4_value = func_cursor.ins().vconst(F32X4, f32x4_constant);
                let f64x2_value = func_cursor.ins().vconst(F64X2, f64x2_constant);

                let ss0_addr = func_cursor
                    .ins()
                    .stack_addr(ir::types::I64, ss0, Offset32::new(0));
                let ss1_addr = func_cursor
                    .ins()
                    .stack_addr(ir::types::I64, ss1, Offset32::new(0));
                let mut mem_flag_little = ir::MemFlags::new();
                mem_flag_little.set_endianness(Endianness::Little);
                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss0_addr, Offset32::new(0));
                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss0_addr, Offset32::new(8));
                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss0_addr, Offset32::new(16));
                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss0_addr, Offset32::new(24));

                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss1_addr, Offset32::new(0));
                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss1_addr, Offset32::new(8));
                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss1_addr, Offset32::new(16));
                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss1_addr, Offset32::new(24));

                def_values.insert(TypedValue::new(i8_value, I8));
                def_values.insert(TypedValue::new(i16_value, I16));
                def_values.insert(TypedValue::new(i32_value, I32));
                def_values.insert(TypedValue::new(i64_value, I64));
                def_values.insert(TypedValue::new(i128_value, I128));

                def_values.insert(TypedValue::new(f32_value, F32));
                def_values.insert(TypedValue::new(f64_value, F64));

                def_values.insert(TypedValue::new(i8x16_value, I8X16));
                def_values.insert(TypedValue::new(i16x8_value, I16X8));
                def_values.insert(TypedValue::new(i32x4_value, I32X4));
                def_values.insert(TypedValue::new(i64x2_value, I64X2));

                def_values.insert(TypedValue::new(f32x4_value, F32X4));
                def_values.insert(TypedValue::new(f64x2_value, F64X2));
            }

            #[cfg(feature = "s390x")]
            {
                let random_i64: i64 = rng.random();
                let random_u16: u16 = rng.random();
                let random_f32: f32 = rng.random();
                let random_f64: f64 = rng.random();

                let i8_value = func_cursor.ins().iconst(I8, random_i64);
                let i16_value = func_cursor.ins().iconst(I16, random_i64);
                let i32_value = func_cursor.ins().iconst(I32, random_i64);
                let i64_value = func_cursor.ins().iconst(I64, random_i64);
                let i128_value = func_cursor.ins().uextend(I128, i64_value);

                let f32_value = func_cursor.ins().f32const(random_f32);
                let f64_value = func_cursor.ins().f64const(random_f64);

                let random_u128: u128 = rng.gen();

                let byte_slice: Vec<u8> = (0..16).map(|_| rng.gen()).collect();
                let v128_constant = func_cursor
                    .func
                    .dfg
                    .constants
                    .insert(ConstantData::from(byte_slice));

                let random_i8 = rng.random::<i8>();
                let random_i16 = rng.random::<i16>();
                let random_i32 = rng.random::<i32>();
                let random_i64 = rng.random::<i64>();

                let i8x16number = i8x16::new([random_i8; 16]);
                let i16x8number = i16x8::new([random_i16; 8]);
                let i32x4number = i32x4::new([random_i32; 4]);
                let i64x2number = i64x2::new([random_i64; 2]);
                let f32x4number = f32x4::new([random_f32; 4]);
                let f64x2number = f64x2::new([random_f64; 2]);

                let i8x16_number = cast_ref::<i8x16, [u8; 16]>(&i8x16number);
                let i16x8_number = cast_ref::<i16x8, [u8; 16]>(&i16x8number);
                let i32x4_number = cast_ref::<i32x4, [u8; 16]>(&i32x4number);
                let i64x2_number = cast_ref::<i64x2, [u8; 16]>(&i64x2number);
                let f32x4_number = cast_ref::<f32x4, [u8; 16]>(&f32x4number);
                let f64x2_number = cast_ref::<f64x2, [u8; 16]>(&f64x2number);

                let i8x16_constant = func_cursor
                    .func
                    .dfg
                    .constants
                    .insert(ConstantData::from(i8x16_number.to_vec()));
                let i16x8_constant = func_cursor
                    .func
                    .dfg
                    .constants
                    .insert(ConstantData::from(i16x8_number.to_vec()));
                let i32x4_constant = func_cursor
                    .func
                    .dfg
                    .constants
                    .insert(ConstantData::from(i32x4_number.to_vec()));
                let i64x2_constant = func_cursor
                    .func
                    .dfg
                    .constants
                    .insert(ConstantData::from(i64x2_number.to_vec()));
                let f32x4_constant = func_cursor
                    .func
                    .dfg
                    .constants
                    .insert(ConstantData::from(f32x4_number.to_vec()));
                let f64x2_constant = func_cursor
                    .func
                    .dfg
                    .constants
                    .insert(ConstantData::from(f64x2_number.to_vec()));

                let i8x16_value = func_cursor.ins().vconst(I8X16, i8x16_constant);
                let i16x8_value = func_cursor.ins().vconst(I16X8, i16x8_constant);
                let i32x4_value = func_cursor.ins().vconst(I32X4, i32x4_constant);
                let i64x2_value = func_cursor.ins().vconst(I64X2, i64x2_constant);

                let f32x4_value = func_cursor.ins().vconst(F32X4, f32x4_constant);
                let f64x2_value = func_cursor.ins().vconst(F64X2, f64x2_constant);

                let ss0_addr = func_cursor
                    .ins()
                    .stack_addr(ir::types::I64, ss0, Offset32::new(0));
                let ss1_addr = func_cursor
                    .ins()
                    .stack_addr(ir::types::I64, ss1, Offset32::new(0));
                let mut mem_flag_little = ir::MemFlags::new();
                mem_flag_little.set_endianness(Endianness::Little);
                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss0_addr, Offset32::new(0));
                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss0_addr, Offset32::new(8));
                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss0_addr, Offset32::new(16));
                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss0_addr, Offset32::new(24));

                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss1_addr, Offset32::new(0));
                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss1_addr, Offset32::new(8));
                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss1_addr, Offset32::new(16));
                func_cursor
                    .ins()
                    .store(mem_flag_little, i64_value, ss1_addr, Offset32::new(24));

                def_values.insert(TypedValue::new(i8_value, I8));
                def_values.insert(TypedValue::new(i16_value, I16));
                def_values.insert(TypedValue::new(i32_value, I32));
                def_values.insert(TypedValue::new(i64_value, I64));
                def_values.insert(TypedValue::new(i128_value, I128));

                def_values.insert(TypedValue::new(f32_value, F32));
                def_values.insert(TypedValue::new(f64_value, F64));

                def_values.insert(TypedValue::new(i8x16_value, I8X16));
                def_values.insert(TypedValue::new(i16x8_value, I16X8));

                def_values.insert(TypedValue::new(i32x4_value, I32X4));
                def_values.insert(TypedValue::new(f32x4_value, F32X4));
                def_values.insert(TypedValue::new(i64x2_value, I64X2));
                def_values.insert(TypedValue::new(f64x2_value, F64X2));
            }

            block_def_values.insert(entry_block, def_values.clone());
        }

        let mut dominator_blocks: HashSet<Block> = HashSet::new();
        match dominator_block_set.get(node) {
            Some(blocks) => dominator_blocks.extend(blocks),
            None => {}
        };

        instr_snippet = instr_snippet_list
            .get(gen_and_print_range(0, 5, false) as usize)
            .unwrap()
            .clone();

        for instr in instr_snippet {
            match populate_block_instructions(
                &mut func_cursor,
                instr,
                &dominator_blocks,
                &block_def_values,
            ) {
                Some((new_value, ref_values_op)) => {
                    if let Some(values) = ref_values_op {
                        for value in values {
                            ref_values.insert(value);
                        }
                    }

                    if new_value != None {
                        def_values.insert(new_value.unwrap());
                    }
                }
                None => {
                    println!("no new value is defined");
                }
            }
        }

        block_def_values.insert(*node, def_values.clone());

        block_ref_values.insert(*node, ref_values);

        if func_cursor.func.layout.last_inst(*node).is_none() {
            func_cursor.ins().nop();
        }

        func_cursor.goto_last_inst(*node);
        let last_instr_id = func_cursor.current_inst().unwrap();
        let mut last_instr_data = func_cursor.func.dfg.insts[last_instr_id];

        match last_instr_data {
            ir::InstructionData::Brif {
                opcode,
                arg,
                blocks,
            } => {
                let cond_value = get_random_cond_value(&dominator_blocks, &block_def_values);
                let args = last_instr_data.arguments_mut(&mut func_cursor.func.dfg.value_lists);
                args[0] = cond_value;
                func_cursor.func.dfg.insts[last_instr_id].clone_from(&last_instr_data);
                let block_params = func_cursor.func.dfg.block_params(*node).to_vec();
                if block_params.len() != 0 {
                    func_cursor.func.dfg.remove_block_param(block_params[0]);
                }
            }
            ir::InstructionData::BranchTable { opcode, arg, table } => {
                let cond_value = get_random_cond_value(&dominator_blocks, &block_def_values);
                let args = last_instr_data.arguments_mut(&mut func_cursor.func.dfg.value_lists);
                args[0] = cond_value;
                func_cursor.func.dfg.insts[last_instr_id].clone_from(&last_instr_data);
                let block_params = func_cursor.func.dfg.block_params(*node).to_vec();
                if block_params.len() != 0 {
                    func_cursor.func.dfg.remove_block_param(block_params[0]);
                }
            }
            _ => {}
        }
    }

    fn get_value_type_intersection(
        blocks: &Vec<Block>,
        block_def_values: &HashMap<Block, HashSet<TypedValue>>,
        block_ref_values: &HashMap<Block, HashSet<TypedValue>>,
    ) -> Vec<Type> {
        let current_block_ref_values = block_ref_values.get(&blocks[0]).unwrap();

        let mut intersection: Option<HashSet<Type>> = Some(
            current_block_ref_values
                .iter()
                .map(|tv| tv.get_type())
                .collect(),
        );

        for pre_block in blocks[1..].iter() {
            let def_values = block_def_values.get(&pre_block).unwrap();

            let pre_block_def_types: HashSet<_> =
                def_values.iter().map(|tv| tv.get_type()).collect();

            intersection = match intersection {
                Some(ref mut set) => {
                    set.retain(|t| pre_block_def_types.contains(t));
                    Some(set.clone())
                }
                None => panic!("The intersection should not be None"),
            };
        }

        match intersection {
            Some(ref intersected_types) if !intersected_types.is_empty() => {
                println!("Intersection of value types: {:?}", intersected_types);
            }
            _ => {
                println!("No common value types found.");
            }
        }

        return intersection.map_or_else(Vec::new, |set| set.into_iter().collect());
    }

    for (i, node) in dfs_order.iter().enumerate() {
        let cfg = ControlFlowGraph::with_function(func_cursor.func);
        let pre_blocks = cfg.pred_iter(*node).collect::<Vec<_>>();
        if pre_blocks.len() >= 2 {
            let mut node_and_pre_blocks = vec![*node];
            pre_blocks.iter().map(|x| node_and_pre_blocks.push(x.block));
            let value_type_intersection = get_value_type_intersection(
                &node_and_pre_blocks,
                &block_def_values,
                &block_ref_values,
            );

            let mut rng = thread_rng();
            let range = rng.gen_range(1..4);
            let block_params_type: Vec<Type> = value_type_intersection
                .choose_multiple(&mut rng, range)
                .cloned()
                .collect();

            let mut block_params: Vec<Value> = vec![];

            for param_type in block_params_type.iter() {
                let param_value = func_cursor.func.dfg.append_block_param(*node, *param_type);
                let mut node_def_values = block_def_values.get(node).unwrap().clone();
                node_def_values.insert(TypedValue::new(param_value, *param_type));

                block_def_values.insert(*node, node_def_values.clone());
                block_params.push(param_value);
            }

            for pre_block in pre_blocks.iter().map(|x| x.block) {
                let mut dominator_blocks: HashSet<Block> = HashSet::new();
                match dominator_block_set.get(&pre_block) {
                    Some(blocks) => dominator_blocks.extend(blocks),
                    None => {}
                };

                let mut value_lists = func_cursor.func.dfg.value_lists.clone();

                func_cursor.goto_last_inst(pre_block);
                let last_instr_id = func_cursor.current_inst().unwrap();

                let mut last_instr_data = func_cursor.func.dfg.insts[last_instr_id].clone();

                match &mut last_instr_data {
                    InstructionData::Jump {
                        opcode,
                        destination,
                    } => {
                        let mut block_args: Vec<Value> = vec![];

                        for (i, param_type) in block_params_type.iter().enumerate() {
                            let values_with_same_type = get_dominator_values_with_type(
                                &dominator_blocks,
                                &block_def_values,
                                *param_type,
                            );
                            let random_value =
                                *select_random_value(&values_with_same_type, 0.4).unwrap();
                            block_args.push(random_value);
                        }
                        let new_block_call = BlockCall::new(
                            destination.block(&value_lists),
                            block_args.as_slice(),
                            &mut value_lists,
                        );
                        destination.clone_from(&new_block_call);
                    }
                    InstructionData::Brif {
                        opcode,
                        arg,
                        blocks,
                    } => {
                        let mut block_args: Vec<Value> = vec![];

                        let false_block = blocks[1].block(&value_lists);
                        let mut dest_block_call = &mut blocks[0];
                        if false_block == *node {
                            dest_block_call = &mut blocks[1];
                        }

                        for (i, param_type) in block_params_type.iter().enumerate() {
                            let values_with_same_type = get_dominator_values_with_type(
                                &dominator_blocks,
                                &block_def_values,
                                *param_type,
                            );
                            let random_value =
                                *select_random_value(&values_with_same_type, 0.4).unwrap();
                            block_args.push(random_value);
                        }

                        let new_block_call = BlockCall::new(
                            dest_block_call.block(&value_lists),
                            block_args.as_slice(),
                            &mut value_lists,
                        );
                        dest_block_call.clone_from(&new_block_call);
                    }
                    InstructionData::BranchTable { opcode, arg, table } => {
                        let mut block_args: Vec<Value> = vec![];

                        let jump_table_data =
                            func_cursor.func.dfg.jump_tables.get_mut(*table).unwrap();

                        for block_call in jump_table_data.all_branches_mut() {
                            if block_call.block(&value_lists) == *node {
                                for (i, param_type) in block_params_type.iter().enumerate() {
                                    let values_with_same_type = get_dominator_values_with_type(
                                        &dominator_blocks,
                                        &block_def_values,
                                        *param_type,
                                    );
                                    let random_value =
                                        *select_random_value(&values_with_same_type, 0.4).unwrap();
                                    block_args.push(random_value);
                                }
                                let new_block_call = BlockCall::new(
                                    block_call.block(&value_lists),
                                    block_args.as_slice(),
                                    &mut value_lists,
                                );
                                block_call.clone_from(&new_block_call);
                            }
                        }
                    }
                    _ => {
                        panic!("A block that contains a postfix, but the last instruction is not a jump instruction")
                    }
                }
                func_cursor.func.dfg.insts[last_instr_id].clone_from(&last_instr_data);
                func_cursor.func.dfg.value_lists.clone_from(&value_lists);
            }

            func_cursor.goto_first_inst(*node);
            while let Some(inst) = func_cursor.next_inst() {
                let data_flow_graph = func_cursor.func.dfg.clone();
                let mut value_lists = func_cursor.func.dfg.value_lists.clone();

                let instr_data = &mut func_cursor.func.dfg.insts[inst];

                let op = instr_data.opcode();
                if matches!(
                    op,
                    Opcode::Load
                        | Opcode::Store
                        | Opcode::Uload8
                        | Opcode::Sload8
                        | Opcode::Istore8
                        | Opcode::Uload16
                        | Opcode::Sload16
                        | Opcode::Istore16
                        | Opcode::Uload32
                        | Opcode::Sload32
                        | Opcode::Istore32
                        | Opcode::Uload8x8
                        | Opcode::Sload8x8
                        | Opcode::Uload16x4
                        | Opcode::Sload16x4
                        | Opcode::Uload32x2
                        | Opcode::Sload32x2
                        | Opcode::StackLoad
                        | Opcode::StackStore
                        | Opcode::DynamicStackLoad
                        | Opcode::DynamicStackStore
                        | Opcode::AtomicLoad
                        | Opcode::AtomicStore
                        | Opcode::AtomicRmw
                        | Opcode::AtomicCas
                ) {
                    continue;
                }

                let ref_values = instr_data.arguments_mut(&mut value_lists);

                for ref_value in ref_values.iter_mut() {
                    let ref_value_type = data_flow_graph.value_type(*ref_value);
                    for (i, param_type) in block_params_type.iter().enumerate() {
                        if param_type.eq(&ref_value_type) && rng.gen_range(0..10) < 3 {
                            ref_value.clone_from(&block_params[i]);
                        }
                    }
                }
            }
        }
    }

    fn get_last_block(func_cursor: &FuncCursor, dfs_order: &Vec<Block>) -> Option<Block> {
        let cfg = ControlFlowGraph::with_function(func_cursor.func);

        for block in dfs_order.iter() {
            let post_blocks = cfg.succ_iter(*block).collect::<Vec<_>>();
            if post_blocks.is_empty() {
                return Some(*block);
            }
        }
        return None;
    }

    if is_root_func == true {
        let all_types = vec![
            I8, I16, I32, I64, F32, F64, I16X8, I32X4, F32X4, I64X2, F64X2,
        ];
        let scalar_types = vec![I8, I16, I32, I64, F32, F64];

        let selected_types = &all_types;

        let mut rng = thread_rng();

        let main_func_sig =
            generate_random_signature(selected_types.clone(), rng.gen_range(3..6), true);
        func_cursor.func.signature.clone_from(&main_func_sig);

        func_cursor
            .func
            .signature
            .uses_special_return(ArgumentPurpose::StructReturn);
        sig = main_func_sig;
    }

    let last_block = get_last_block(&func_cursor, &dfs_order).unwrap();
    if sig.returns.len() != 0 {
        let mut return_values: Vec<Value> = vec![];

        let mut dominator_blocks: HashSet<Block> = HashSet::new();
        match dominator_block_set.get(&last_block) {
            Some(blocks) => dominator_blocks.extend(blocks),
            None => {}
        };

        for return_type in sig.returns {
            let values_with_same_type = get_dominator_values_with_type(
                &dominator_blocks,
                &block_def_values,
                return_type.value_type,
            );
            let random_value = *select_random_value(&values_with_same_type, 0.4).unwrap();
            return_values.push(random_value);
        }
        func_cursor.goto_bottom(last_block);
        func_cursor.ins().return_(return_values.as_slice());
    }

    println!("last block is {:?}", last_block);

    return (dominator_block_set, block_def_values);
}

pub fn insert_function_invocation(
    func_node: &mut FunctionNode,
    func_dominator_ref_map_vec: &Vec<(
        Function,
        (
            HashMap<Block, HashSet<Block>>,
            HashMap<Block, HashSet<TypedValue>>,
        ),
    )>,
) {
    fn get_dominated_blocks(
        block: &Block,
        dominance_map: &HashMap<Block, HashSet<Block>>,
    ) -> HashSet<Block> {
        let mut dominated_blocks = HashSet::new();

        for (key, value) in dominance_map.iter() {
            if value.contains(block) {
                dominated_blocks.insert(key.clone());
            }
        }

        dominated_blocks
    }

    let mut rng = thread_rng();

    let child_sub_funcs: Vec<Function> = func_node.get_child_funcs_clone();

    let func = &mut func_node.func;
    for child_func in child_sub_funcs {
        let sig = child_func.signature.clone();
        let sig_ref = func.import_signature(sig.clone());

        let external_name = UserExternalName::from(child_func.name.get_user().unwrap().clone());
        let external_name_ref = func.declare_imported_user_function(external_name.into());

        let child_func_ref = func.import_function(ExtFuncData {
            name: ExternalName::User(external_name_ref),
            signature: sig_ref,
            colocated: false,
        });

        let mut func_cursor = FuncCursor::new(func);

        for (function, (dominance_map, block_def_values)) in func_dominator_ref_map_vec.iter() {
            let func_name = function.name.clone();
            if func_cursor.func.name.to_string() == func_name.to_string() {
                let mut all_blocks: Vec<Block> = dominance_map.keys().cloned().collect();
                all_blocks.sort();
                let inserted_block = all_blocks[1..].choose(&mut rand::thread_rng()).unwrap();

                let mut dominated_blocks = get_dominated_blocks(inserted_block, dominance_map);

                let mut dominator_blocks: HashSet<Block> = HashSet::new();
                match dominance_map.get(inserted_block) {
                    Some(blocks) => {
                        dominator_blocks.extend(blocks);
                    }
                    None => {}
                };

                if dominated_blocks.contains(inserted_block) {
                    dominated_blocks.remove(inserted_block);
                }

                func_cursor.goto_last_inst(*inserted_block);

                let mut call_params: Vec<Value> = vec![];
                for param in sig.params.iter().cloned() {
                    let values_with_same_type = get_dominator_values_with_type(
                        &dominator_blocks,
                        &block_def_values,
                        param.value_type,
                    );

                    let random_value = *select_random_value(&values_with_same_type, 0.4).unwrap();
                    call_params.push(random_value);
                }
                let call_inst = func_cursor
                    .ins()
                    .call(child_func_ref, call_params.as_slice());

                match dominated_blocks.iter().choose(&mut thread_rng()) {
                    Some(block) => {
                        let modified_block = block;

                        func_cursor.goto_first_inst(*modified_block);

                        let mut value_lists = func_cursor.func.dfg.value_lists.clone();

                        for next_instr in func_cursor.next_inst() {
                            let instr_data = &mut func_cursor.func.dfg.insts[next_instr];

                            let op = instr_data.opcode();
                            if matches!(
                                op,
                                Opcode::Load
                                    | Opcode::Store
                                    | Opcode::Uload8
                                    | Opcode::Sload8
                                    | Opcode::Istore8
                                    | Opcode::Uload16
                                    | Opcode::Sload16
                                    | Opcode::Istore16
                                    | Opcode::Uload32
                                    | Opcode::Sload32
                                    | Opcode::Istore32
                                    | Opcode::Uload8x8
                                    | Opcode::Sload8x8
                                    | Opcode::Uload16x4
                                    | Opcode::Sload16x4
                                    | Opcode::Uload32x2
                                    | Opcode::Sload32x2
                                    | Opcode::StackLoad
                                    | Opcode::StackStore
                                    | Opcode::DynamicStackLoad
                                    | Opcode::DynamicStackStore
                                    | Opcode::AtomicLoad
                                    | Opcode::AtomicStore
                                    | Opcode::AtomicRmw
                                    | Opcode::AtomicCas
                            ) {
                                continue;
                            }

                            let mut call_results = func_cursor
                                .func
                                .dfg
                                .inst_results(call_inst)
                                .iter()
                                .copied()
                                .collect::<Vec<_>>();

                            let dfg = func_cursor.func.dfg.clone();

                            let args_mut = func_cursor.func.dfg.insts[next_instr]
                                .arguments_mut(&mut value_lists);

                            for arg in args_mut.iter_mut() {
                                for (i, call_result) in call_results.iter_mut().enumerate() {
                                    if dfg.value_type(*call_result) == dfg.value_type(*arg)
                                        && rng.gen_range(0..10) < 2
                                    {
                                        arg.clone_from(call_result);
                                    }
                                }
                            }
                        }

                        func_cursor.func.dfg.value_lists.clone_from(&value_lists);
                    }

                    None => {}
                }
            }
        }
    }
}
