use cranelift_codegen::cfg_printer::CFGPrinter;
use cranelift_codegen::cursor::{Cursor, CursorPosition, FuncCursor};
use cranelift_codegen::flowgraph::{BlockPredecessor, ControlFlowGraph};
use cranelift_codegen::ir::entities::Block;
use cranelift_codegen::ir::layout::{BlockNode, Blocks};
use cranelift_codegen::ir::{
    types, BlockCall, Function, Inst, InstBuilder, InstructionData, JumpTableData, Layout, Value,
};
use cranelift_codegen::packed_option::PackedOption;
use rand::{thread_rng, Rng};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::Write;

fn reverse_postorder(
    cfg: &ControlFlowGraph,
    start_node: Block,
    dominators: &mut HashMap<Block, HashSet<Block>>,
) -> Vec<Block> {
    let mut visited = HashSet::new();
    let mut postorder = Vec::new();

    fn dfs(
        cfg: &ControlFlowGraph,
        node: Block,
        visited: &mut HashSet<Block>,
        postorder: &mut Vec<Block>,
    ) {
        if visited.contains(&node) {
            return;
        }
        visited.insert(node);

        for succ in cfg.succ_iter(node) {
            dfs(cfg, succ, visited, postorder);
        }

        postorder.push(node);
    }

    dfs(cfg, start_node, &mut visited, &mut postorder);

    postorder.reverse();
    postorder
}

pub fn compute_dominators(func: &Function) -> HashMap<Block, HashSet<Block>> {
    let cfg = ControlFlowGraph::with_function(func);
    let start_node = func.layout.entry_block().expect("入口节点不存在");

    let mut dominators: HashMap<Block, HashSet<Block>> = HashMap::new();
    let mut nodes: HashSet<Block> = HashSet::new();
    for _block in func.layout.blocks() {
        nodes.insert(_block);
    }

    for &node in &nodes {
        if node == start_node {
            let mut entry_dom = HashSet::new();
            entry_dom.insert(start_node);
            dominators.insert(start_node, entry_dom);
        } else {
            dominators.insert(node, nodes.clone());
        }
    }

    let reverse_postorder = reverse_postorder(&cfg, start_node, &mut dominators);

    let mut changed = true;

    while changed {
        changed = false;

        for &node in &reverse_postorder {
            if node == start_node {
                continue;
            }

            let mut predecessors: Vec<Block> = vec![];
            for predecessor in cfg.pred_iter(node) {
                predecessors.push(predecessor.block)
            }

            let mut new_dom = nodes.clone();
            for &pred in &predecessors {
                if let Some(pred_dom) = dominators.get(&pred) {
                    new_dom = new_dom.intersection(pred_dom).cloned().collect();
                }
            }

            new_dom.insert(node);

            if dominators.get(&node) != Some(&new_dom) {
                dominators.insert(node, new_dom);
                changed = true;
            }
        }
    }

    dominators
}
