use cf_constructor::{cf_construct, cfg_print, output_clif};
use cg_constructor::{cg_post_order_traversal, generate_function_call_graph, FunctionNode};
use clap::{ArgAction, Parser};
use commons::fixed_rng::initialize_rng;
use commons::types::{config_intersection, load_config, ArchConfig};
use cranelift_codegen::cfg_printer::CFGPrinter;
use cranelift_codegen::flowgraph::ControlFlowGraph;
use cranelift_codegen::ir::{
    AbiParam, Block, ExtFuncData, ExternalName, Function, Signature, UserExternalName, UserFuncName,
};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::{ir, write_function};
use env_logger;
use function_generator::dominator_tree::compute_dominators;
use function_generator::instruction_selector::TypedValue;
use function_generator::{function_generator, insert_function_invocation};
use log::{info, LevelFilter};
use mongodb::bson::{doc, from_bson, Bson};
use mongodb::{
    bson,
    bson::Document,
    sync::{Client, Collection},
};
use std::borrow::BorrowMut;
use std::collections::{HashMap, HashSet};
use std::fmt::format;
use std::fs;
use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::str::FromStr;
use std::{env, vec};
use toml;

fn get_collection() -> anyhow::Result<Collection<Document>> {
    
    let client_uri = "mongodb://localhost:27017";
    let client = Client::with_uri_str(client_uri).unwrap();

    let database = client.database("cranelift");
    let collection = database.collection::<Document>("ir");

    Ok(collection)
}

fn load_all_documents() -> anyhow::Result<Vec<Document>> {
    let client_uri = "mongodb://localhost:27017/?connectTimeoutMS=10000";
    let client = Client::with_uri_str(client_uri)?;
    let collection = client.database("cranelift").collection::<Document>("ir");

    let find_result = collection.find(Document::new());
    let cursor = find_result.run().unwrap();
    let docs: Vec<Document> = cursor.filter_map(Result::ok).collect();

    Ok(docs)
}



#[test]
fn print_all_opcode() {
    use cranelift_codegen::ir::Opcode;

    fn get_all_opcode_strings() -> Vec<String> {
        Opcode::all()
            .iter()
            .map(|opcode| opcode.to_string())
            .collect()
    }

    
    let all_instruction_names = get_all_opcode_strings();
    println!("All opcodes: {:?}", all_instruction_names);
}

#[test]
fn dominator_tree_test() {
    initialize_rng();

    let mut root_func_node = generate_function_call_graph();
    
    cf_construct(&mut root_func_node.func, None, 0);

    
    let dominators = compute_dominators(&root_func_node.func);
    
    for (node, dom_set) in &dominators {
        println!("Node {}: Dominators: {:?}", node, dom_set);
    }
}

fn generate_ir(config: &ArchConfig, path: &str, num: u32) -> Result<(), String> {
    let mut fileid = 0;
    initialize_rng();

    
    let all_documents = load_all_documents().unwrap();

    while true {
        let mut clif_output = String::from_str("\n").unwrap();

        
        let mut func_dominator_ref_map_vec: Vec<(
            Function,
            (
                HashMap<Block, HashSet<Block>>,
                HashMap<Block, HashSet<TypedValue>>,
            ),
        )> = Vec::new();

        let mut root_func_node = generate_function_call_graph();
        
        cf_construct(&mut root_func_node.func, None, 0);
        let (dominator_block_set, block_def_values) =
            function_generator(&mut root_func_node.func, true, &all_documents, config);

        func_dominator_ref_map_vec.push((
            root_func_node.func.clone(),
            (dominator_block_set, block_def_values),
        ));

        let mut func_node_post_order: Vec<FunctionNode> = vec![];
        cg_post_order_traversal(root_func_node.clone(), &mut func_node_post_order);
        if let Some((last, rest)) = func_node_post_order.split_last_mut() {
            for func_node in rest.iter_mut() {
                let func = &mut func_node.func;

                cf_construct(func, None, 0);
                let (dominator_block_set, block_def_values) =
                    function_generator(func, false, &all_documents, config);

                
                func_dominator_ref_map_vec
                    .push((func.clone(), (dominator_block_set, block_def_values)));

                insert_function_invocation(func_node, &func_dominator_ref_map_vec);

                write_function(&mut clif_output, &func_node.func);
            }
            insert_function_invocation(&mut root_func_node, &func_dominator_ref_map_vec);
            write_function(&mut clif_output, &root_func_node.func);
        }

        let mut tests_str = String::from_str("test ").unwrap();
        config.tests.iter().for_each(|test| {
            tests_str.push_str(&format!(" {}", test));
        });
        let mut config_sets_str = String::new();
        config.config_sets.iter().for_each(|(key, value)| {
            config_sets_str.push_str(&format!("\nset {}={}", key, value));
        });
        let mut target_str = String::new();
        config.target.iter().for_each(|target| {
            target_str.push_str(&format!("\ntarget {}", target));
        });

        clif_output.push_str("\n\n; print: %main()");

        
        let path = Path::new(path);
        fs::create_dir_all(path);

        let mut clif_none_file =
            File::create(path.join(format!("cranelift_ir_{}_none.clif", fileid))).unwrap();
        let mut clif_speed_file =
            File::create(path.join(format!("cranelift_ir_{}_speed.clif", fileid))).unwrap();
        let mut clif_speed_size_file =
            File::create(path.join(format!("cranelift_ir_{}_speed_and_size.clif", fileid)))
                .unwrap();

        let mut clif_none_output = clif_output.clone();
        clif_none_output.insert_str(
            0,
            &format!(
                "{}\n{}\nset opt_level=none\n{}",
                tests_str, config_sets_str, target_str
            ),
        );
        let mut clif_speed_output = clif_output.clone();
        clif_speed_output.insert_str(
            0,
            &format!(
                "{}\n{}\nset opt_level=speed\n{}",
                tests_str, config_sets_str, target_str
            ),
        );
        let mut clif_speed_size_output = clif_output.clone();
        clif_speed_size_output.insert_str(
            0,
            &format!(
                "{}\n{}\nset opt_level=speed_and_size\n{}",
                tests_str, config_sets_str, target_str
            ),
        );

        clif_none_file.write_all(clif_none_output.as_bytes()); 
        clif_speed_file.write_all(clif_speed_output.as_bytes()); 
        clif_speed_size_file.write_all(clif_speed_size_output.as_bytes()); 
        info!("{}", format!("file cranelift_ir_{}.clif generated", fileid));

        fileid += 1;
        if fileid >= num {
            println!("Reached fileid limit, breaking loop");
            break;
        }
    }

    Ok(())
}

fn generate_ir_intersection(configs: Vec<ArchConfig>, path: &str, num: u32) -> Result<(), String> {
    let mut fileid = 0;
    initialize_rng();

    
    let all_documents = load_all_documents().unwrap();

    while true {
        let mut clif_output = String::from_str("\n").unwrap();

        
        let mut func_dominator_ref_map_vec: Vec<(
            Function,
            (
                HashMap<Block, HashSet<Block>>,
                HashMap<Block, HashSet<TypedValue>>,
            ),
        )> = Vec::new();

        let mut root_func_node = generate_function_call_graph();
        
        cf_construct(&mut root_func_node.func, None, 0);
        let (dominator_block_set, block_def_values) =
            function_generator(&mut root_func_node.func, true, &all_documents, &configs[0]);

        func_dominator_ref_map_vec.push((
            root_func_node.func.clone(),
            (dominator_block_set, block_def_values),
        ));

        let mut func_node_post_order: Vec<FunctionNode> = vec![];
        cg_post_order_traversal(root_func_node.clone(), &mut func_node_post_order);
        if let Some((last, rest)) = func_node_post_order.split_last_mut() {
            for func_node in rest.iter_mut() {
                let func = &mut func_node.func;

                cf_construct(func, None, 0);
                let (dominator_block_set, block_def_values) =
                    function_generator(func, false, &all_documents, &configs[0]);

                
                func_dominator_ref_map_vec
                    .push((func.clone(), (dominator_block_set, block_def_values)));

                insert_function_invocation(func_node, &func_dominator_ref_map_vec);

                write_function(&mut clif_output, &func_node.func);
            }
            insert_function_invocation(&mut root_func_node, &func_dominator_ref_map_vec);
            write_function(&mut clif_output, &root_func_node.func);
        }

        clif_output.push_str("\n\n; print: %main()");

        for i in 0..configs.len() {
            let config = &configs[i];
            let mut tests_str = String::from_str("test ").unwrap();
            config.tests.iter().for_each(|test| {
                tests_str.push_str(&format!(" {}", test));
            });
            let mut config_sets_str = String::new();
            config.config_sets.iter().for_each(|(key, value)| {
                config_sets_str.push_str(&format!("\nset {}={}", key, value));
            });
            let mut target_str = String::new();
            config.target.iter().for_each(|target| {
                target_str.push_str(&format!("\ntarget {}", target));
            });

            
            let mut path = Path::new(path).join(&config.arch);
            fs::create_dir_all(&path);

            let mut clif_none_file =
                File::create(path.join(format!("cranelift_ir_{}_none.clif", fileid))).unwrap();
            let mut clif_speed_file =
                File::create(path.join(format!("cranelift_ir_{}_speed.clif", fileid))).unwrap();
            let mut clif_speed_size_file =
                File::create(path.join(format!("cranelift_ir_{}_speed_and_size.clif", fileid)))
                    .unwrap();

            let mut clif_none_output = clif_output.clone();
            clif_none_output.insert_str(
                0,
                &format!(
                    "{}\n{}\nset opt_level=none\n{}",
                    tests_str, config_sets_str, target_str
                ),
            );
            let mut clif_speed_output = clif_output.clone();
            clif_speed_output.insert_str(
                0,
                &format!(
                    "{}\n{}\nset opt_level=speed\n{}",
                    tests_str, config_sets_str, target_str
                ),
            );
            let mut clif_speed_size_output = clif_output.clone();
            clif_speed_size_output.insert_str(
                0,
                &format!(
                    "{}\n{}\nset opt_level=speed_and_size\n{}",
                    tests_str, config_sets_str, target_str
                ),
            );

            clif_none_file.write_all(clif_none_output.as_bytes()); 
            clif_speed_file.write_all(clif_speed_output.as_bytes()); 
            clif_speed_size_file.write_all(clif_speed_size_output.as_bytes()); 
            info!(
                "{}",
                format!(
                    "Arch {} file cranelift_ir_{}.clif generated",
                    &config.arch, fileid
                )
            );
        }

        fileid += 1;
        if fileid >= num {
            println!("Reached fileid limit, breaking loop");
            break;
        }
    }

    Ok(())
}

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[arg(required = true)]
    mode: String,

    
    
    #[arg(
        required = true,
        num_args = 1..,  
        value_name = "CONFIG_PATH",
    )]
    config_paths: Vec<PathBuf>,

    
    #[arg(short, long, default_value_t = 1, required = true)]
    num: u32,

    #[arg(required = true, value_name = "OUTPUT_PATH")]
    output_path: PathBuf,
}

fn main() -> Result<(), String> {
    
    env_logger::builder().filter_level(LevelFilter::Info).init();

    let args = Cli::parse();

    let mode = args.mode;

    match mode.as_str() {
        "single" => {
            let config_path = args.config_paths.get(0).unwrap();

            let mut config = load_config(config_path.to_str().unwrap());
            config.build_instruction_map();
            let num: u32 = args.num;

            fs::create_dir_all(&args.output_path)
                .map_err(|e| format!("Failed to create output dir: {}", e))?;

            generate_ir(&config, args.output_path.to_str().unwrap(), num)
                .map_err(|e| format!("Failed to generate IR: {}", e))?;
        }
        "intersection" => {
            let config_paths: Vec<&str> = args
                .config_paths
                .iter()
                .map(|p| p.to_str().unwrap())
                .collect();

            let mut intersection_config = config_intersection(config_paths.clone())
                .map_err(|e| format!("Failed to compute config intersection: {}", e))?;

            let output_path = &args.output_path.clone();
            let num: u32 = args.num;

            fs::create_dir_all(output_path)
                .map_err(|e| format!("Failed to create output dir: {}", e))?;

            let mut configs: Vec<ArchConfig> = vec![];

            for single_config in config_paths.iter() {
                let mut config = load_config(single_config);

                
                intersection_config.arch = config.arch.clone();
                intersection_config.tests = config.tests.clone();
                intersection_config.config_sets = config.config_sets.clone();
                intersection_config.target = config.target.clone();
                intersection_config.build_instruction_map();

                let config = intersection_config.clone();
                configs.push(config);
            }

            generate_ir_intersection(configs, output_path.to_str().unwrap(), num)
                .map_err(|e| format!("Failed to generate IR intersection: {}", e))?;
        }
        _ => {
            return Err(format!("Unknown mode: {}", mode));
        }
    }

    Ok(())
}
