use cf_constructor::{cf_construct, cfg_print, output_clif};
use cg_constructor::{cg_post_order_traversal, generate_function_call_graph, FunctionNode};
use commons::fixed_rng::initialize_rng;
use commons::types::ArchConfig;
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
use std::path::Path;
use std::str::FromStr;
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
fn cf_construct_test() {
    initialize_rng();

    let mut root_func_node = generate_function_call_graph();

    cf_construct(&mut root_func_node.func, None, 0);

    let all_documents = load_all_documents().unwrap();
    function_generator(&mut root_func_node.func, true, &all_documents);

    cfg_print(&mut root_func_node.func, "test_dominator.dot");
    output_clif(&mut root_func_node.func, "test1.clif");
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

#[test]
fn multi_func_test() {
    env_logger::builder().filter_level(LevelFilter::Info).init();

    let mut funcid = 0;

    let mut clif_output = String::new();
    let mut dot_output = String::new();

    initialize_rng();

    let all_documents = load_all_documents().unwrap();

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
        function_generator(&mut root_func_node.func, true, &all_documents);

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
                function_generator(func, false, &all_documents);

            func_dominator_ref_map_vec
                .push((func.clone(), (dominator_block_set, block_def_values)));

            insert_function_invocation(func_node, &func_dominator_ref_map_vec);

            write_function(&mut clif_output, &func_node.func);
            funcid += 1;
        }
        insert_function_invocation(&mut root_func_node, &func_dominator_ref_map_vec);

        write_function(&mut clif_output, &root_func_node.func);
    }

    let mut clif_file = File::create("multi_func.clif").unwrap();
    clif_file.write_all(clif_output.as_bytes());
}

#[test]
fn multi_file_test() {
    env_logger::builder().filter_level(LevelFilter::Info).init();

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
            function_generator(&mut root_func_node.func, true, &all_documents);

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
                    function_generator(func, false, &all_documents);

                func_dominator_ref_map_vec
                    .push((func.clone(), (dominator_block_set, block_def_values)));

                insert_function_invocation(func_node, &func_dominator_ref_map_vec);

                write_function(&mut clif_output, &func_node.func);
            }
            insert_function_invocation(&mut root_func_node, &func_dominator_ref_map_vec);
            write_function(&mut clif_output, &root_func_node.func);
        }

        let path = Path::new("../../clifcases718/riscv");
        fs::create_dir_all(path);

        let mut clif_none_file =
            File::create(path.join(format!("multi_func{}_none.clif", fileid))).unwrap();
        let mut clif_speed_file =
            File::create(path.join(format!("multi_func{}_speed.clif", fileid))).unwrap();
        let mut clif_speed_size_file =
            File::create(path.join(format!("multi_func{}_speed_and_size.clif", fileid))).unwrap();

        clif_output.push_str("\n\n; print: %main()");
        let mut clif_none_output = clif_output.clone();
        let mut clif_speed_output = clif_output.clone();
        let mut clif_speed_size_output = clif_output.clone();

        #[cfg(feature = "x86-64")]
        {
            clif_none_output.insert_str(0, "test inline precise-output optimize    
            set opt_level=none
            set preserve_frame_pointers=true
            set enable_multi_ret_implicit_sret=true
            set enable_nan_canonicalization=true
            \n
            target x86_64 sse42 has_avx
            target aarch64 
            target s390x
            target riscv64gc  has_zcd has_zbkb has_zbc has_zbs has_zicond has_zvl32b has_zvl64b has_zvl128b has_zvl1024b has_zvl2048b has_zvl4096b has_zvl8192b has_zvl16384b has_zvl32768b\n");

            clif_speed_output.insert_str(0, "test inline precise-output optimize
            set opt_level=speed
            set preserve_frame_pointers=true
            set enable_multi_ret_implicit_sret=true   
            set enable_nan_canonicalization=true
            \n
            target x86_64 sse42 has_avx
            target aarch64 
            target s390x
            target riscv64gc  has_zcd has_zbkb has_zbc has_zbs has_zicond has_zvl32b has_zvl64b has_zvl128b has_zvl1024b has_zvl2048b has_zvl4096b has_zvl8192b has_zvl16384b has_zvl32768b\n");

            clif_speed_size_output.insert_str(0, "test inline precise-output optimize
            set opt_level=speed_and_size          
            set preserve_frame_pointers=true
            set enable_multi_ret_implicit_sret=true
            set enable_nan_canonicalization=true
            \n
            target x86_64 sse42 has_avx
            target aarch64 
            target s390x
            target riscv64gc  has_zcd has_zbkb has_zbc has_zbs has_zicond has_zvl32b has_zvl64b has_zvl128b has_zvl1024b has_zvl2048b has_zvl4096b has_zvl8192b has_zvl16384b has_zvl32768b\n");
        }
        #[cfg(feature = "aarch64")]
        {
            clif_none_output.insert_str(0, "test inline precise-output optimize    
            set opt_level=none
            set preserve_frame_pointers=true
            set enable_multi_ret_implicit_sret=true
            set enable_nan_canonicalization=true 
            \n
            target x86_64 sse42 has_avx
            target aarch64 
            target s390x
            target riscv64gc  has_zcd has_zbkb has_zbc has_zbs has_zicond has_zvl32b has_zvl64b has_zvl128b has_zvl1024b has_zvl2048b has_zvl4096b has_zvl8192b has_zvl16384b has_zvl32768b\n");
            clif_speed_output.insert_str(0, "test inline precise-output optimize
            set opt_level=speed
            set preserve_frame_pointers=true
            set enable_multi_ret_implicit_sret=true
            set enable_nan_canonicalization=true
            \n
            target x86_64 sse42 has_avx
            target aarch64 
            target s390x
            target riscv64gc  has_zcd has_zbkb has_zbc has_zbs has_zicond has_zvl32b has_zvl64b has_zvl128b has_zvl1024b has_zvl2048b has_zvl4096b has_zvl8192b has_zvl16384b has_zvl32768b\n");
            clif_speed_size_output.insert_str(0, "test inline precise-output optimize
            set opt_level=speed_and_size
            set preserve_frame_pointers=true
            set enable_multi_ret_implicit_sret=true
            set enable_nan_canonicalization=true
            \n
            target x86_64 sse42 has_avx
            target aarch64 
            target s390x
            target riscv64gc  has_zcd has_zbkb has_zbc has_zbs has_zicond has_zvl32b has_zvl64b has_zvl128b has_zvl1024b has_zvl2048b has_zvl4096b has_zvl8192b has_zvl16384b has_zvl32768b\n");
        }
        #[cfg(feature = "riscv")]
        {
            clif_none_output.insert_str(0, "test inline precise-output optimize    
            set opt_level=none
            set preserve_frame_pointers=true
            set enable_multi_ret_implicit_sret=true
            set enable_nan_canonicalization=true            
            \n
            target x86_64 sse42 has_avx
            target aarch64 
            target s390x
            target riscv64gc  has_zcd has_zbkb has_zbc has_zbs has_zicond has_zvl32b has_zvl64b has_zvl128b has_zvl1024b has_zvl2048b has_zvl4096b has_zvl8192b has_zvl16384b has_zvl32768b\n");
            clif_speed_output.insert_str(0, "test inline precise-output optimize
            set opt_level=speed
            set preserve_frame_pointers=true
            set enable_multi_ret_implicit_sret=true
            set enable_nan_canonicalization=true
            \n
            target x86_64 sse42 has_avx
            target aarch64 
            target s390x
            target riscv64gc  has_zcd has_zbkb has_zbc has_zbs has_zicond has_zvl32b has_zvl64b has_zvl128b has_zvl1024b has_zvl2048b has_zvl4096b has_zvl8192b has_zvl16384b has_zvl32768b\n");
            clif_speed_size_output.insert_str(0, "test inline precise-output optimize
            set opt_level=speed_and_size
            set preserve_frame_pointers=true
            set enable_multi_ret_implicit_sret=true
            set enable_nan_canonicalization=true
            \n
            target x86_64 sse42 has_avx
            target aarch64 
            target s390x
            target riscv64gc  has_zcd has_zbkb has_zbc has_zbs has_zicond has_zvl32b has_zvl64b has_zvl128b has_zvl1024b has_zvl2048b has_zvl4096b has_zvl8192b has_zvl16384b has_zvl32768b\n");
        }

        #[cfg(feature = "s390x")]
        {
            clif_none_output.insert_str(0, "test inline precise-output optimize    
            set opt_level=none
            set preserve_frame_pointers=true
            set enable_multi_ret_implicit_sret=true
            set enable_nan_canonicalization=true
            \n
            target x86_64 sse42 has_avx
            target aarch64 
            target s390x
            target riscv64gc  has_zcd has_zbkb has_zbc has_zbs has_zicond has_zvl32b has_zvl64b has_zvl128b has_zvl1024b has_zvl2048b has_zvl4096b has_zvl8192b has_zvl16384b has_zvl32768b\n");
            clif_speed_output.insert_str(0, "test inline precise-output optimize
            set opt_level=speed
            set preserve_frame_pointers=true
            set enable_multi_ret_implicit_sret=true
            set enable_nan_canonicalization=true
            \n
            target x86_64 sse42 has_avx
            target aarch64 
            target s390x
            target riscv64gc  has_zcd has_zbkb has_zbc has_zbs has_zicond has_zvl32b has_zvl64b has_zvl128b has_zvl1024b has_zvl2048b has_zvl4096b has_zvl8192b has_zvl16384b has_zvl32768b\n");
            clif_speed_size_output.insert_str(0, "test inline precise-output optimize
            set opt_level=speed_and_size
            set preserve_frame_pointers=true
            set enable_multi_ret_implicit_sret=true
            set enable_nan_canonicalization=true
            \n
            target x86_64 sse42 has_avx
            target aarch64 
            target s390x
            target riscv64gc  has_zcd has_zbkb has_zbc has_zbs has_zicond has_zvl32b has_zvl64b has_zvl128b has_zvl1024b has_zvl2048b has_zvl4096b has_zvl8192b has_zvl16384b has_zvl32768b\n");
        }

        clif_none_file.write_all(clif_none_output.as_bytes());
        clif_speed_file.write_all(clif_speed_output.as_bytes());
        clif_speed_size_file.write_all(clif_speed_size_output.as_bytes());
        info!("{}", format!("file multi_func{}.clif generated", fileid));

        fileid += 1;
        if fileid >= 10000 {
            println!("Reached fileid limit, breaking loop");
            break;
        }
    }
}

fn main() {
    let config_path = "configs/arch_x86.toml";
    let content = std::fs::read_to_string(config_path).expect("Failed to read config file");
    let config: ArchConfig = toml::from_str(&content).expect("Failed to parse config");
    print!("Loaded config: {:?}", config);
}
