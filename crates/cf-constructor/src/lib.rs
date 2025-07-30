use commons::fixed_rng::{gen_and_print_range, FixedRng};
use cranelift_codegen::cfg_printer::CFGPrinter;
use cranelift_codegen::cursor::{Cursor, CursorPosition, FuncCursor};
use cranelift_codegen::flowgraph::{BlockPredecessor, ControlFlowGraph};
use cranelift_codegen::ir::entities::Block;
use cranelift_codegen::ir::layout::{BlockNode, Blocks};
use cranelift_codegen::ir::{
    types, BlockCall, Function, Inst, InstBuilder, InstructionData, JumpTableData, Layout, Value,
};
use cranelift_codegen::packed_option::PackedOption;
use cranelift_codegen::write_function;
use rand::{thread_rng, Rng};
use std::cell::RefCell;
use std::collections::HashMap;
use std::fs::File;
use std::io::Write;

const MAX_DEPTH: usize = 2;

pub fn add(left: u64, right: u64) -> u64 {
    left + right
}

#[cfg(test)]
mod tests {
    use cranelift_codegen::cfg_printer::CFGPrinter;
    use cranelift_codegen::cursor::*;
    use cranelift_codegen::flowgraph::ControlFlowGraph;
    use cranelift_codegen::ir::{types, InstBuilder};
    use std::fs::File;
    use std::io::Write;

    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }

    #[test]
    fn sequential_test() {
        let func = &mut Function::new();

        let sequential = sequential(func, 3);

        let mut cfg = ControlFlowGraph::with_function(&func);

        if cfg.is_valid() {
            println!("valide");
        }

        fn get_block(block_type: &BlockType) -> &Block {
            match block_type {
                BlockType::Block(ref block) => block,
                _ => panic!("Expected BlockType::Block"),
            }
        }

        let block0_predecessors = cfg
            .pred_iter(*get_block(&sequential.blocks[0]))
            .collect::<Vec<_>>();
        let block1_predecessors = cfg
            .pred_iter(*get_block(&sequential.blocks[1]))
            .collect::<Vec<_>>();
        let block2_predecessors = cfg
            .pred_iter(*get_block(&sequential.blocks[2]))
            .collect::<Vec<_>>();

        let block0_successors = cfg
            .succ_iter(*get_block(&sequential.blocks[0]))
            .collect::<Vec<_>>();
        let block1_successors = cfg
            .succ_iter(*get_block(&sequential.blocks[1]))
            .collect::<Vec<_>>();
        let block2_successors = cfg
            .succ_iter(*get_block(&sequential.blocks[2]))
            .collect::<Vec<_>>();

        println!("{}", block0_predecessors.len());
        println!("{}", block1_predecessors.len());
        println!("{}", block1_predecessors.len());
    }

    #[test]
    fn if_else_test() {
        let func = &mut Function::new();
        let if_else = if_else(func);

        let mut cfg = ControlFlowGraph::with_function(&func);

        if cfg.is_valid() {
            println!("valide");
        }

        let cfg_printer = CFGPrinter::new(func);

        cfg_print(func, "if_elsee.dot");
    }

    #[test]
    fn while_test() {
        let func = &mut Function::new();
        let while_blocks = while_blocks(func);

        let mut cfg = ControlFlowGraph::with_function(&func);

        if cfg.is_valid() {
            println!("valide");
        }
    }

    #[test]
    fn switch_test() {
        let func = &mut Function::new();
        let switch_blocks = switch_blocks(func, 3);

        let mut cfg = ControlFlowGraph::with_function(&func);

        if cfg.is_valid() {
            println!("valide");
        }
    }

    #[test]
    fn layout_test() {
        let mut func = Function::new();
        let block0 = func.dfg.make_block();
        let cond = func.dfg.append_block_param(block0, types::I32);
        let block1 = func.dfg.make_block();
        let block2 = func.dfg.make_block();

        let br_block0_block2_block1;
        let br_block1_block1_block2;

        {
            let mut cur = FuncCursor::new(&mut func);

            cur.insert_block(block0);
            br_block0_block2_block1 = cur.ins().brif(cond, block2, &[], block1, &[]);

            cur.insert_block(block1);
            br_block1_block1_block2 = cur.ins().brif(cond, block1, &[], block2, &[]);

            cur.insert_block(block2);
        }

        let block3 = func.dfg.make_block();
        let block4 = func.dfg.make_block();
        {
            let mut cur = FuncCursor::new(&mut func);

            cur.insert_block(block3);
            let brif_instr = cur.ins().brif(cond, block0, &[], block4, &[]);
            let mut cur = cur.at_last_inst(block3);

            let removed_instr = cur.remove_inst();

            cur.ins().brif(cond, block0, &[], block4, &[]);

            cur.insert_block(block4);
        }

        let block5 = func.dfg.make_block();
        func.layout.remove_block(block4);
        {
            let mut cur = FuncCursor::new(&mut func);
            let mut cur = cur.at_last_inst(block3);

            cur.ins().brif(cond, block0, &[], block5, &[]);

            cur.insert_block(block5);
        }

        cfg_print(&mut func, "test.dot");
        let mut cfg = ControlFlowGraph::with_function(&func);

        {
            let block0_predecessors = cfg.pred_iter(block0).collect::<Vec<_>>();
            let block1_predecessors = cfg.pred_iter(block1).collect::<Vec<_>>();
            let block2_predecessors = cfg.pred_iter(block2).collect::<Vec<_>>();

            let block0_successors = cfg.succ_iter(block0).collect::<Vec<_>>();
            let block1_successors = cfg.succ_iter(block1).collect::<Vec<_>>();
            let block2_successors = cfg.succ_iter(block2).collect::<Vec<_>>();

            println!("{}", block0_predecessors.len());
            println!("{}", block1_predecessors.len());
            println!("{}", block2_predecessors.len());
        }
    }

    #[test]
    fn layout_bug_test() {
        let mut func = Function::new();
        let block0 = func.dfg.make_block();
        let cond = func.dfg.append_block_param(block0, types::I32);
        let block1 = func.dfg.make_block();
        let block2 = func.dfg.make_block();

        let br_block1_block0_block2;

        {
            let mut cur = FuncCursor::new(&mut func);
            cur.insert_block(block0);
            cur.insert_block(block1);
            br_block1_block0_block2 = cur.ins().brif(cond, block0, &[], block2, &[]);
            cur.insert_block(block2);
        }

        let block3 = func.dfg.make_block();
        func.layout.remove_block(block2);
        {
            let mut cur = FuncCursor::new(&mut func);
            let mut cur = cur.at_last_inst(block1);

            cur.ins().brif(cond, block0, &[], block3, &[]);
            cur.insert_block(block3);
        }

        cfg_print(&mut func, "test.dot");
        let mut cfg = ControlFlowGraph::with_function(&func);
    }
}

pub enum BlockType {
    Block(Block),
    Sequential(Box<Sequential>),
    IfElse(Box<IfElse>),
    While(Box<While>),
    Switch(Box<Switch>),
}

pub struct Sequential {
    blocks: Vec<Box<BlockType>>,
}

impl Sequential {
    pub fn get_first_block(&self) -> Block {
        match self.blocks.get(0) {
            Some(block_type) => match block_type.as_ref() {
                BlockType::Block(ref first_block) => *first_block,
                _ => panic!("First block is not a BlockType::Block"),
            },
            None => panic!("No blocks in Sequential"),
        }
    }

    pub fn get_last_block(&self) -> Block {
        let block_len = self.blocks.len();
        match self.blocks.get(block_len - 1) {
            Some(block_type) => match block_type.as_ref() {
                BlockType::Block(ref last_block) => *last_block,
                _ => panic!("First block is not a BlockType::Block"),
            },
            None => panic!("No blocks in Sequential"),
        }
    }

    pub fn get_random_block(&self) -> Block {
        let block_len = self.blocks.len();
        let mut rng = rand::thread_rng();
        let i = gen_and_print_range(0, block_len as u32, false) as usize;

        match self.blocks.get(i) {
            Some(block_type) => match block_type.as_ref() {
                BlockType::Block(ref replaced_block) => *replaced_block,
                _ => panic!("First block is not a BlockType::Block"),
            },
            None => panic!("No blocks in Sequential"),
        }
    }
}

pub struct IfElse {
    cond_block: Box<BlockType>,
    true_block: Box<BlockType>,
    false_block: Box<BlockType>,
    last_block: Box<BlockType>,
}

impl IfElse {
    pub fn get_first_block(&self) -> Block {
        match self.cond_block.as_ref() {
            BlockType::Block(ref first_block) => *first_block,
            _ => panic!("Condition block is not a BlockType::Block"),
        }
    }

    pub fn get_last_block(&self) -> Block {
        match self.last_block.as_ref() {
            BlockType::Block(ref last_block) => *last_block,
            _ => panic!("Condition block is not a BlockType::Block"),
        }
    }

    pub fn get_random_block(&self) -> Block {
        let block_type = match gen_and_print_range(0, 2, false) {
            1 => &self.true_block,
            _ => &self.false_block,
        };

        match block_type.as_ref() {
            BlockType::Block(ref extracted_block) => return *extracted_block,
            _ => panic!("Condition block is not a BlockType::Block"),
        }
    }
}

pub struct While {
    while_block: Box<BlockType>,
    body_block: Box<BlockType>,
    false_block: Box<BlockType>,
}

impl While {
    pub fn get_first_block(&self) -> Block {
        match self.while_block.as_ref() {
            BlockType::Block(ref first_block) => return *first_block,
            _ => panic!("Condition block is not a BlockType::Block"),
        }
    }

    pub fn get_last_block(&self) -> Block {
        match self.false_block.as_ref() {
            BlockType::Block(ref last_block) => return *last_block,
            _ => panic!("Condition block is not a BlockType::Block"),
        }
    }

    pub fn get_random_block(&self) -> Block {
        let block_type = match gen_and_print_range(0, 3, false) {
            0 => &self.while_block,
            1 => &self.body_block,
            _ => &self.false_block,
        };

        match block_type.as_ref() {
            BlockType::Block(ref extracted_block) => return *extracted_block,
            _ => panic!("Condition block is not a BlockType::Block"),
        }
    }
}

pub struct Switch {
    switch_block: Box<BlockType>,
    default_block: Box<BlockType>,
    case_blocks: Vec<Box<BlockType>>,
    last_block: Box<BlockType>,
}

impl Switch {
    pub fn get_first_block(&self) -> Block {
        match self.switch_block.as_ref() {
            BlockType::Block(ref first_block) => return *first_block,
            _ => panic!("Condition block is not a BlockType::Block"),
        }
    }

    pub fn get_last_block(&self) -> Block {
        match self.last_block.as_ref() {
            BlockType::Block(ref last_block) => return *last_block,
            _ => panic!("Condition block is not a BlockType::Block"),
        }
    }

    pub fn get_random_block(&self) -> Block {
        let cases_num = self.case_blocks.len();

        let block_type = match gen_and_print_range(0, 3, false) {
            0 => &self.switch_block,
            1 => &self.default_block,
            _ => &self
                .case_blocks
                .get(gen_and_print_range(0, cases_num as u32, false) as usize)
                .unwrap(),
        };

        match block_type.as_ref() {
            BlockType::Block(ref extracted_block) => return *extracted_block,
            _ => panic!("Condition block is not a BlockType::Block"),
        }
    }
}

fn sequential(func: &mut Function, block_num: u32) -> Sequential {
    let mut sequential = Sequential { blocks: Vec::new() };

    for _ in 0..block_num {
        let block = func.dfg.make_block();
        sequential.blocks.push(Box::from(BlockType::Block(block)));
    }

    {
        let mut cur = FuncCursor::new(func);

        for i in 0..block_num - 1 {
            if let BlockType::Block(ref current_block) =
                sequential.blocks.get(i as usize).unwrap().as_ref()
            {
                if let BlockType::Block(ref next_block) =
                    sequential.blocks.get(i as usize + 1).unwrap().as_ref()
                {
                    cur.insert_block(current_block.clone());
                    cur.ins().jump(next_block.clone(), &[]);
                }
            }
        }

        cur.insert_block(
            match sequential
                .blocks
                .get(block_num as usize - 1)
                .unwrap()
                .as_ref()
            {
                BlockType::Block(ref block) => block.clone(),
                _ => panic!("expected a BlockType::Block"),
            },
        );
    }

    sequential
}

fn if_else(func: &mut Function) -> IfElse {
    let cond_block = func.dfg.make_block();
    let true_block = func.dfg.make_block();
    let false_block = func.dfg.make_block();
    let last_block = func.dfg.make_block();
    let if_else = IfElse {
        cond_block: Box::from(BlockType::Block(cond_block)),
        true_block: Box::from(BlockType::Block(true_block)),
        false_block: Box::from(BlockType::Block(false_block)),
        last_block: Box::from(BlockType::Block(last_block)),
    };

    let cond = func.dfg.append_block_param(cond_block, types::I32);

    {
        let mut cur = FuncCursor::new(func);

        cur.insert_block(cond_block);
        cur.ins().brif(cond, true_block, &[], false_block, &[]);

        cur.insert_block(true_block);
        cur.ins().jump(last_block, &[]);
        cur.insert_block(false_block);
        cur.ins().jump(last_block, &[]);
        cur.insert_block(last_block);
    }

    return if_else;
}

fn while_blocks(func: &mut Function) -> While {
    let cond_block = func.dfg.make_block();
    let body_block = func.dfg.make_block();
    let false_block = func.dfg.make_block();

    let while_blocks = While {
        while_block: Box::from(BlockType::Block(cond_block)),
        body_block: Box::from(BlockType::Block(body_block)),
        false_block: Box::from(BlockType::Block(false_block)),
    };

    let cond = func.dfg.append_block_param(cond_block, types::I32);

    {
        let mut cur = FuncCursor::new(func);

        cur.insert_block(cond_block);
        cur.ins().brif(cond, body_block, &[], false_block, &[]);

        cur.insert_block(body_block);
        cur.ins().jump(cond_block, &[]);

        cur.insert_block(false_block);
    }

    return while_blocks;
}

fn switch_blocks(func: &mut Function, case_num: usize) -> Switch {
    let cond_block = func.dfg.make_block();
    let default_block = func.dfg.make_block();
    let last_block = func.dfg.make_block();

    let mut switch_blocks = Switch {
        switch_block: Box::from(BlockType::Block(cond_block)),
        default_block: Box::from(BlockType::Block(default_block)),
        case_blocks: Vec::new(),
        last_block: Box::from(BlockType::Block(last_block)),
    };

    let mut block_call_list: Vec<BlockCall> = vec![];

    for i in 0..case_num {
        let case_block = func.dfg.make_block();
        switch_blocks
            .case_blocks
            .push(Box::from(BlockType::Block(case_block)));
        let block_call = func.dfg.block_call(case_block, &[]);
        block_call_list.push(block_call);
    }

    let cond = func.dfg.append_block_param(cond_block, types::I32);

    let jump_table_data = JumpTableData::new(
        func.dfg.block_call(default_block, &[]),
        block_call_list.as_slice(),
    );
    let jump_table = func.create_jump_table(jump_table_data);
    {
        let mut cur = FuncCursor::new(func);
        cur.insert_block(cond_block);
        cur.ins().br_table(cond, jump_table);
        for i in 0..case_num {
            match switch_blocks.case_blocks.get(i) {
                Some(block_type) => match block_type.as_ref() {
                    BlockType::Block(ref case_block) => {
                        cur.insert_block(*case_block);
                        cur.ins().jump(last_block, &[]);
                    }
                    _ => panic!("block is not a BlockType::Block"),
                },
                None => panic!("插入case_block失败"),
            }
        }
        cur.insert_block(default_block);
        cur.ins().jump(last_block, &[]);
        cur.insert_block(last_block);
    }
    return switch_blocks;
}

pub fn cfg_print(func: &mut Function, file_name: &str) {
    /*
    dot -Tpng .\if_esle.dot -o graph.png
    */

    let cfg_printer = CFGPrinter::new(func);

    let mut buffer = String::new();
    cfg_printer.write(&mut buffer).unwrap();

    let mut file = File::create(file_name).unwrap();
    file.write_all(buffer.as_bytes()).unwrap();
}

pub fn output_clif(func: &mut Function, file_name: &str) {
    let mut output = String::new();

    write_function(&mut output, &func).unwrap();

    let mut clif_file = File::create(file_name).unwrap();
    clif_file.write_all(output.as_bytes());
}

pub fn cf_construct(func: &mut Function, parent_block: Option<BlockType>, depth: usize) {
    let mut rng = rand::thread_rng();

    let mut child_cf: Option<BlockType> = None;

    match parent_block {
        Some(BlockType::Sequential(sequential_blocks)) => {
            let block_num = sequential_blocks.blocks.len();

            if true {
                let choice = gen_and_print_range(0, 4, false);

                let replaced_block = sequential_blocks.get_random_block();

                match choice {
                    0 => {
                        let child_sequential = sequential(func, gen_and_print_range(2, 5, false));

                        let child_first_block = child_sequential.get_first_block();
                        update_predecessor(func, child_first_block, replaced_block);
                        let child_last_block = child_sequential.get_last_block();
                        update_successor(func, child_last_block, replaced_block);

                        child_cf = Some(BlockType::Sequential(Box::from(child_sequential)));
                    }
                    1 => {
                        let child_if_else = if_else(func);
                        let child_first_block = child_if_else.get_first_block();
                        update_predecessor(func, child_first_block, replaced_block);
                        let child_last_block = child_if_else.get_last_block();
                        update_successor(func, child_last_block, replaced_block);

                        child_cf = Some(BlockType::IfElse(Box::from(child_if_else)));
                    }
                    2 => {
                        let child_while = while_blocks(func);

                        let child_first_block = child_while.get_first_block();
                        update_predecessor(func, child_first_block, replaced_block);
                        let child_last_block = child_while.get_last_block();
                        update_successor(func, child_last_block, replaced_block);

                        child_cf = Some(BlockType::While(Box::from(child_while)));
                    }
                    3 => {
                        let child_switch =
                            switch_blocks(func, gen_and_print_range(2, 5, false) as usize);

                        let child_first_block = child_switch.get_first_block();
                        update_predecessor(func, child_first_block, replaced_block);
                        let child_last_block = child_switch.get_last_block();
                        update_successor(func, child_last_block, replaced_block);

                        child_cf = Some(BlockType::Switch(Box::from(child_switch)));
                    }
                    _ => {
                        panic!("")
                    }
                }
            }
        }
        Some(BlockType::IfElse(if_else_blocks)) => {
            if true {
                let choice = gen_and_print_range(0, 4, false);

                let replaced_block = if_else_blocks.get_random_block();

                match choice {
                    0 => {
                        let child_sequential = sequential(func, gen_and_print_range(2, 5, false));
                        let child_first_block = child_sequential.get_first_block();
                        update_predecessor(func, child_first_block, replaced_block);
                        let child_last_block = child_sequential.get_last_block();
                        update_successor(func, child_last_block, replaced_block);

                        child_cf = Some(BlockType::Sequential(Box::from(child_sequential)));
                    }
                    1 => {
                        let child_if_else = if_else(func);
                        let child_first_block = child_if_else.get_first_block();
                        update_predecessor(func, child_first_block, replaced_block);
                        let child_last_block = child_if_else.get_last_block();
                        update_successor(func, child_last_block, replaced_block);

                        child_cf = Some(BlockType::IfElse(Box::from(child_if_else)));
                    }
                    2 => {
                        let child_while = while_blocks(func);
                        let child_first_block = child_while.get_first_block();
                        update_predecessor(func, child_first_block, replaced_block);
                        let child_last_block = child_while.get_last_block();
                        update_successor(func, child_last_block, replaced_block);

                        child_cf = Some(BlockType::While(Box::from(child_while)));
                    }
                    3 => {
                        let child_switch =
                            switch_blocks(func, gen_and_print_range(2, 5, false) as usize);
                        let child_first_block = child_switch.get_first_block();
                        update_predecessor(func, child_first_block, replaced_block);
                        let child_last_block = child_switch.get_last_block();
                        update_successor(func, child_last_block, replaced_block);

                        child_cf = Some(BlockType::Switch(Box::from(child_switch)));
                    }
                    _ => {}
                }
            }
        }
        Some(BlockType::While(while_block)) => {
            if true {
                let choice = gen_and_print_range(0, 4, false);

                let replaced_block = while_block.get_random_block();

                match choice {
                    0 => {
                        let child_sequential = sequential(func, gen_and_print_range(2, 5, false));
                        let child_first_block = child_sequential.get_first_block();
                        update_predecessor(func, child_first_block, replaced_block);
                        let child_last_block = child_sequential.get_last_block();
                        update_successor(func, child_last_block, replaced_block);

                        child_cf = Some(BlockType::Sequential(Box::from(child_sequential)));
                    }
                    1 => {
                        let child_if_else = if_else(func);
                        let child_first_block = child_if_else.get_first_block();
                        update_predecessor(func, child_first_block, replaced_block);
                        let child_last_block = child_if_else.get_last_block();
                        update_successor(func, child_last_block, replaced_block);

                        child_cf = Some(BlockType::IfElse(Box::from(child_if_else)));
                    }
                    2 => {
                        let child_while = while_blocks(func);
                        let child_first_block = child_while.get_first_block();
                        update_predecessor(func, child_first_block, replaced_block);
                        let child_last_block = child_while.get_last_block();
                        update_successor(func, child_last_block, replaced_block);

                        child_cf = Some(BlockType::While(Box::from(child_while)));
                    }
                    3 => {
                        let child_switch =
                            switch_blocks(func, gen_and_print_range(2, 5, false) as usize);
                        let child_first_block = child_switch.get_first_block();
                        update_predecessor(func, child_first_block, replaced_block);
                        let child_last_block = child_switch.get_last_block();
                        update_successor(func, child_last_block, replaced_block);

                        child_cf = Some(BlockType::Switch(Box::from(child_switch)));
                    }
                    _ => {}
                }
            }
        }
        Some(BlockType::Switch(switch_block)) => {
            if true {
                let choice = gen_and_print_range(0, 4, false);

                let replaced_block = switch_block.get_random_block();

                match choice {
                    0 => {
                        let child_sequential = sequential(func, gen_and_print_range(2, 5, false));
                        let child_first_block = child_sequential.get_first_block();
                        update_predecessor(func, child_first_block, replaced_block);
                        let child_last_block = child_sequential.get_last_block();
                        update_successor(func, child_last_block, replaced_block);

                        child_cf = Some(BlockType::Sequential(Box::from(child_sequential)));
                    }
                    1 => {
                        let child_if_else = if_else(func);
                        let child_first_block = child_if_else.get_first_block();
                        update_predecessor(func, child_first_block, replaced_block);
                        let child_last_block = child_if_else.get_last_block();
                        update_successor(func, child_last_block, replaced_block);

                        child_cf = Some(BlockType::IfElse(Box::from(child_if_else)));
                    }
                    2 => {
                        let child_while = while_blocks(func);
                        let child_first_block = child_while.get_first_block();
                        update_predecessor(func, child_first_block, replaced_block);
                        let child_last_block = child_while.get_last_block();
                        update_successor(func, child_last_block, replaced_block);

                        child_cf = Some(BlockType::While(Box::from(child_while)));
                    }
                    3 => {
                        let child_switch =
                            switch_blocks(func, gen_and_print_range(2, 5, false) as usize);
                        let child_first_block = child_switch.get_first_block();
                        update_predecessor(func, child_first_block, replaced_block);
                        let child_last_block = child_switch.get_last_block();
                        update_successor(func, child_last_block, replaced_block);

                        child_cf = Some(BlockType::Switch(Box::from(child_switch)));
                    }
                    _ => {}
                }
            }
        }
        None => {
            let entry_block = func.dfg.make_block();
            let end_block = func.dfg.make_block();

            {
                let mut cur = FuncCursor::new(func);
                cur.insert_block(entry_block);
                cur.insert_block(end_block);
            }

            let choice = gen_and_print_range(0, 4, false);

            match choice {
                0 => {
                    let child_sequential = sequential(func, gen_and_print_range(2, 5, false));
                    let mut cur = FuncCursor::new(func);
                    cur.goto_bottom(entry_block);
                    cur.ins().jump(child_sequential.get_first_block(), &[]);
                    cur.goto_bottom(child_sequential.get_last_block());
                    cur.ins().jump(end_block, &[]);

                    child_cf = Some(BlockType::Sequential(Box::from(child_sequential)));
                }
                1 => {
                    let child_if_else = if_else(func);
                    let mut cur = FuncCursor::new(func);
                    cur.goto_bottom(entry_block);
                    cur.ins().jump(child_if_else.get_first_block(), &[]);
                    let child_last_block = child_if_else.get_last_block();
                    cur.goto_bottom(child_last_block);
                    cur.ins().jump(end_block, &[]);

                    child_cf = Some(BlockType::IfElse(Box::from(child_if_else)));
                }
                2 => {
                    let child_while = while_blocks(func);
                    let mut cur = FuncCursor::new(func);
                    cur.goto_bottom(entry_block);
                    cur.ins().jump(child_while.get_first_block(), &[]);
                    cur.goto_bottom(child_while.get_last_block());
                    cur.ins().jump(end_block, &[]);

                    child_cf = Some(BlockType::While(Box::from(child_while)));
                }
                3 => {
                    let child_switch =
                        switch_blocks(func, gen_and_print_range(2, 5, false) as usize);
                    let mut cur = FuncCursor::new(func);
                    cur.goto_bottom(entry_block);
                    cur.ins().jump(child_switch.get_first_block(), &[]);
                    let child_last_block = child_switch.get_last_block();
                    cur.goto_bottom(child_last_block);
                    cur.ins().jump(end_block, &[]);

                    child_cf = Some(BlockType::Switch(Box::from(child_switch)));
                }
                _ => {}
            }
        }
        _ => {}
    }

    if depth >= MAX_DEPTH {
        return;
    } else if let None = child_cf {
        return;
    }
    cf_construct(func, Some(child_cf.unwrap()), depth + 1);
}

fn update_predecessor(func: &mut Function, block: Block, replaced_block: Block) {
    let mut cfg = ControlFlowGraph::with_function(&func);
    let mut pre_blocks: Vec<Block> = Vec::new();

    for BlockPredecessor {
        block: parent,
        inst,
    } in cfg.pred_iter(replaced_block)
    {
        pre_blocks.push(parent);
    }

    let mut cur = FuncCursor::new(func);

    for pre_block in pre_blocks {
        let last_control_instr = get_block_last_control_instr(&mut cur, pre_block).unwrap();

        match last_control_instr {
            InstructionData::Brif {
                opcode,
                arg,
                blocks,
            } => {
                cur.remove_inst();
                let true_block = blocks[0].block(&cur.func.dfg.value_lists);
                let false_block = blocks[1].block(&cur.func.dfg.value_lists);
                if true_block == replaced_block {
                    cur.ins().brif(arg, block, &[], false_block, &[]);
                } else if false_block == replaced_block {
                    cur.ins().brif(arg, true_block, &[], block, &[]);
                } else {
                    panic!("被替换块不存在于前块的br_if的跳转目标中")
                }
            }
            InstructionData::BranchTable { opcode, arg, table } => {
                let dfg = &mut cur.func.dfg;
                let mut default_block_call = dfg.jump_tables[table].default_block_mut();

                if default_block_call.block(&dfg.value_lists) == replaced_block {
                    default_block_call.set_block(block, &mut dfg.value_lists);
                }
                for case in dfg.jump_tables[table].as_mut_slice() {
                    if case.block(&dfg.value_lists) == replaced_block {
                        case.set_block(block, &mut dfg.value_lists);
                    }
                }
            }
            InstructionData::Jump {
                opcode,
                destination,
            } => {
                cur.remove_inst();
                cur.ins().jump(block, &[]);
            }
            _ => {
                panic!("前一个块的控制指令识别有错误")
            }
        }
    }
}

fn get_block_last_control_instr(cur: &mut FuncCursor, block: Block) -> Option<InstructionData> {
    match cur.layout().last_inst(block) {
        None => {
            return None;
        }
        Some(last_control_instr) => {
            let last_instr_data = cur.func.dfg.insts[last_control_instr];

            cur.set_position(CursorPosition::At(last_control_instr));

            return Some(last_instr_data);
        }
    }
}

fn update_successor(func: &mut Function, block: Block, replaced_block: Block) {
    let mut cfg = ControlFlowGraph::with_function(&func);
    let post_blocks = cfg.succ_iter(replaced_block).collect::<Vec<_>>();

    let mut cur = FuncCursor::new(func);

    if post_blocks.len() == 1 {
        if let Some(replaced_block_control_instr) =
            get_block_last_control_instr(&mut cur, replaced_block)
        {
            cur.remove_inst();
        }
        cur.goto_bottom(block);
        cur.ins().jump(post_blocks[0].clone(), &[]);
    } else if post_blocks.len() == 2 {
        if let Some(replaced_block_control_instr) =
            get_block_last_control_instr(&mut cur, replaced_block)
        {
            cur.remove_inst();

            cur.goto_bottom(block);
            match replaced_block_control_instr {
                InstructionData::Brif {
                    opcode,
                    arg,
                    blocks,
                } => {
                    cur.ins().brif(
                        arg,
                        post_blocks[0].clone(),
                        &[],
                        post_blocks[1].clone(),
                        &[],
                    );
                }
                _ => {
                    panic!("something error")
                }
            }
        } else {
            panic!("被替换的块没有跳转指令")
        }
    } else if post_blocks.len() >= 3 {
        let mut block_call_list: Vec<BlockCall> = vec![];
        for i in 1..post_blocks.len() {
            let block_call = cur.func.dfg.block_call(post_blocks[i], &[]);
            block_call_list.push(block_call);
        }
        let jump_table_data = JumpTableData::new(
            cur.func.dfg.block_call(post_blocks[0], &[]),
            &block_call_list,
        );
        let jump_table = cur.func.create_jump_table(jump_table_data);

        if let Some(replaced_block_control_instr) =
            get_block_last_control_instr(&mut cur, replaced_block)
        {
            cur.remove_inst();

            cur.goto_bottom(block);
            match replaced_block_control_instr {
                InstructionData::BranchTable { opcode, arg, table } => {
                    cur.ins().br_table(arg, jump_table);
                }
                _ => {
                    panic!("something error")
                }
            }
        } else {
            panic!("被替换的块没有跳转指令")
        }
    }

    cur.layout_mut().remove_block(replaced_block);
}
