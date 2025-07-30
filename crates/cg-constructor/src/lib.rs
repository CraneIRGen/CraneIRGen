use cranelift_codegen::flowgraph::ControlFlowGraph;
use cranelift_codegen::ir;
use cranelift_codegen::ir::{
    AbiParam, Block, ExternalName, FuncRef, Function, Signature, Type, UserFuncName,
};
use cranelift_codegen::isa::CallConv;
use rand::prelude::IndexedRandom;
use rand::{thread_rng, Rng};
use std::collections::HashSet;
use std::fmt;

#[derive(Debug, Clone)]
pub struct FunctionNode {
    pub func: Function,
    pub sig: Signature,
    pub name: UserFuncName,
    pub children: Vec<FunctionNode>,
}

impl FunctionNode {
    fn new(func: Function, func_name: UserFuncName, sig: Signature) -> Self {
        FunctionNode {
            func: func,
            sig: sig,
            name: func_name,
            children: Vec::new(),
        }
    }

    fn add_child(&mut self, child: FunctionNode) {
        self.children.push(child);
    }

    fn print(&self, depth: usize) {
        println!("{}{}", "  ".repeat(depth), self.func);
        for child in &self.children {
            child.print(depth + 1);
        }
    }

    pub fn get_child_funcs_clone(&self) -> Vec<Function> {
        let mut ret: Vec<Function> = Vec::new();
        for child in self.children.iter() {
            ret.push(child.func.clone());
        }
        ret
    }
}

pub fn cg_post_order_traversal(function_node: FunctionNode, post_order: &mut Vec<FunctionNode>) {
    for child in function_node.children.iter().cloned() {
        cg_post_order_traversal(child, post_order);
    }

    post_order.push(function_node);
}

fn generate_function_tree(
    node: &mut FunctionNode,
    max_depth: usize,
    current_depth: usize,
    func_id: &mut i32,
) {
    if current_depth < max_depth {
        let mut rng = rand::thread_rng();
        let num_children = rng.gen_range(1..=2);

        for i in 0..num_children {
            let mut child_func_sig = Signature::new(CallConv::Fast);

            let candidate_types = vec![
                ir::types::I32,
                ir::types::I64,
                ir::types::F32,
                ir::types::F64,
            ];
            child_func_sig.clone_from(&generate_random_signature(
                candidate_types,
                rng.gen_range(1..=2),
                false,
            ));
            *func_id += 1;
            let child_func_name = UserFuncName::user(1, *func_id as u32);
            let child_func =
                Function::with_name_signature(child_func_name.clone(), child_func_sig.clone());

            let mut child_node = FunctionNode::new(child_func, child_func_name, child_func_sig);
            generate_function_tree(&mut child_node, max_depth, current_depth + 1, func_id);
            node.add_child(child_node);
        }
    }
}

pub fn generate_function_call_graph() -> FunctionNode {
    let root_func_sig = Signature::new(CallConv::Fast);
    let root_func_name = UserFuncName::testcase("main");
    let root_func = Function::with_name_signature(root_func_name.clone(), root_func_sig.clone());

    let mut root = FunctionNode::new(root_func, root_func_name, root_func_sig);
    let max_depth = 4;
    let mut func_id = 0;
    generate_function_tree(&mut root, max_depth, 0, &mut func_id);

    return root;
}

pub fn generate_random_signature(
    candidate_types: Vec<Type>,
    types_num: usize,
    is_root_func: bool,
) -> Signature {
    let mut sig = Signature::new(CallConv::Fast);
    let mut rng = thread_rng();

    if is_root_func == false {
        let params_type: Vec<_> = candidate_types
            .choose_multiple(&mut rng, types_num)
            .cloned()
            .collect();
        for param in params_type {
            sig.params.push(AbiParam::new(param));
        }
    }

    let returns_type: Vec<_> = candidate_types
        .choose_multiple(&mut rng, types_num)
        .cloned()
        .collect();
    for return_type in returns_type {
        sig.returns.push(AbiParam::new(return_type));
    }

    sig
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelift_codegen::isa::CallConv;

    #[test]
    fn it_works() {
        let root_func_sig = Signature::new(CallConv::Fast);
        let root_func_name = UserFuncName::user(1, 0);
        let root_func =
            Function::with_name_signature(root_func_name.clone(), root_func_sig.clone());

        let mut root = FunctionNode::new(root_func, root_func_name, root_func_sig);
        let max_depth = 4;
        let mut func_id = 0;
        generate_function_tree(&mut root, max_depth, 0, &mut func_id);

        root.print(0);
    }
}
