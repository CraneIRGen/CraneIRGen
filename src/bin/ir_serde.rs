use anyhow::Result;
use clap::Parser;
use cranelift_codegen::cursor::{Cursor, FuncCursor};
use cranelift_codegen::flowgraph::ControlFlowGraph;
use cranelift_codegen::ir::instructions::InstructionFormat;
use cranelift_codegen::ir::{Function, Immediate, InstructionData, Value};
use cranelift_reader::parse_functions;
use mongodb::bson::{from_bson, Bson};
use mongodb::options::ClientOptions;
use mongodb::{
    bson,
    bson::Document,
    sync::{Client, Collection},
};
use serde::{Deserialize, Serialize};
use serde_json::Value as JsonValue;
use std::fmt::Debug;
use std::fs::File;
use std::io::prelude::*;
use std::path::Path;
use std::process;
use std::str::FromStr;
use std::{fs, io};

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

    fn to_json_string(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }

    fn from_json_string(json_str: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(json_str)
    }

    fn compare_instrs(&self, other: &BlockJson) -> bool {
        if self.instrs.len() != other.instrs.len() {
            return false;
        }

        for (instr_self, instr_other) in self.instrs.iter().zip(&other.instrs) {
            if let (Some(opcode_self), Some(opcode_other)) =
                (instr_self.as_object(), instr_other.as_object())
            {
                if opcode_self.get("opcode") != opcode_other.get("opcode") {
                    return false;
                }
            } else {
                panic!("errors when convert json into object.");
            }
        }

        true
    }
}

fn process_dirs_clif(dir: &Path) -> io::Result<()> {
    if dir.is_dir() {
        for entry in fs::read_dir(dir)? {
            let entry = entry?;
            let path = entry.path();

            if path.is_dir() {
                process_dirs_clif(&path)?;
            } else if path.is_file()
                && path.extension().and_then(|ext| ext.to_str()) == Some("clif")
            {
                println!("Converting file: {:?}", path);

                let mut file = File::open(&path)?;

                let mut ir_str = String::new();

                file.read_to_string(&mut ir_str)?;

                let mut ir_funcs = match parse_functions(&ir_str) {
                    Ok(funcs) => funcs,
                    Err(e) => {
                        eprintln!("Parsing error: {:?}", e);
                        continue;
                    }
                };

                let func = &mut ir_funcs[0];

                traverse_blocks(func);

                let is_leaf = func.is_leaf();
                if is_leaf == false {
                    println!("function {:?} has call instructions", &path)
                }
            }
        }
    }
    Ok(())
}

fn main() -> Result<()> {
    let path = Path::new("./cranelift_ir");
    process_dirs_clif(path);
    Ok(())
}

fn get_collection() -> Result<Collection<Document>> {
    let client_uri = "mongodb://localhost:27017";
    let client = Client::with_uri_str(client_uri)?;

    let database = client.database("cranelift");
    let collection = database.collection::<Document>("ir");

    Ok(collection)
}

fn documents_are_equal(doc: &Document, new_block_json: &str) -> Result<bool> {
    let old_block: BlockJson = from_bson(Bson::Document(doc.clone()))?;
    let new_block = BlockJson::from_json_string(new_block_json)?;

    Ok(old_block.compare_instrs(&new_block))
}

fn insert_json_into_mongodb(new_block_json: &str) -> Result<()> {
    let collection = get_collection()?;

    let new_document: Document = serde_json::from_str(new_block_json)?;

    let mut find_result = collection.find(Document::new());
    let mut cursor = find_result.run()?;

    while let Some(result) = cursor.next() {
        match result {
            Ok(doc) => {
                if documents_are_equal(&doc, new_block_json)? {
                    println!("Document already exists in the collection, skipping insert.");
                    return Ok(());
                }
            }
            Err(e) => {
                eprintln!("Error reading document: {}", e);
                return Err(e.into());
            }
        }
    }

    match collection.insert_one(new_document).run() {
        Ok(_) => println!("Document inserted successfully!"),
        Err(e) => {
            eprintln!("Failed to insert document: {}", e);
            return Err(e.into());
        }
    }
    Ok(())
}

fn traverse_cfg(func: &mut Function) {
    let mut cfg = ControlFlowGraph::with_function(func);
}

fn traverse_blocks(func: &mut Function) {
    let mut func_tmp = func.clone();
    let mut pos = FuncCursor::new(&mut func_tmp);
    while let Some(block) = pos.next_block() {
        let mut block_json = BlockJson::new();

        block_json
            .add_context(serde_json::json!({"dynamic_stack_slots": func.dynamic_stack_slots}));
        block_json.add_context(serde_json::json!({"sized_stack_slots": func.sized_stack_slots}));
        block_json.add_context(serde_json::json!({"global_values": func.global_values}));
        block_json.add_context(serde_json::json!({"memory_types": func.memory_types}));
        block_json.add_context(serde_json::json!({"ext_funcs": func.dfg.ext_funcs}));
        block_json.add_context(serde_json::json!({"constants": func.dfg.constants}));
        block_json.add_context(serde_json::json!({"stack_limit": func.stack_limit}));

        let block_data = &pos.func.dfg.blocks[block];

        let block_params = block_data.params(&pos.func.dfg.value_lists);

        let mut block_type = Vec::new();

        for block_param in block_params.iter().copied() {
            println!("{:?}", pos.func.dfg.value_type(block_param));
            block_type.push(pos.func.dfg.value_type(block_param));
        }

        let instr_json = serde_json::json!({"opcode": "block", "type": block_type});
        block_json.add_block_type(instr_json);

        let serialized = serde_json::to_string(block_data).unwrap();
        println!("Serialized: {}", serialized);

        while let Some(inst) = pos.next_inst() {
            let instr_data = pos.func.dfg.insts[inst];

            let opcode = instr_data.opcode();
            let instr_args = pos.func.dfg.inst_args(inst);
            let instr_result = pos.func.dfg.inst_results(inst);

            let serialized = serde_json::to_string(&instr_data).unwrap();
            println!("Serialized: {}\n", serialized);

            block_json.add_instr(serde_json::json!(instr_data));

            let deserialized: InstructionData = serde_json::from_str(&serialized).unwrap();
            println!("Deserialized: {:?}\n", deserialized);

            let values: Vec<_> = pos.func.dfg.inst_values(inst).collect();
        }

        println!("{:?}", block_json);

        insert_json_into_mongodb(&block_json.to_json_string().unwrap());
    }
}
