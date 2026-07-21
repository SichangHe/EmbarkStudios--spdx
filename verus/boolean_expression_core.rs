//! Verus model for the strict boolean SPDX expression core.
//!
//! The model proves that compiling a boolean expression tree to postfix and
//! then evaluating that postfix stack preserves the tree's boolean meaning.
//! Rust tests bridge this bounded model to the production `spdx::Expression`
//! parse/evaluate path over a finite SPDX identifier corpus.

use vstd::prelude::*;

fn main() {}

verus! {

#[derive(Copy, Clone, PartialEq, Eq)]
enum BoolOp {
    And,
    Or,
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum PostfixNode {
    Val(bool),
    Op(BoolOp),
}

enum BoolExpr {
    Leaf(bool),
    Bin(BoolOp, Box<BoolExpr>, Box<BoolExpr>),
}

spec fn eval_op(op: BoolOp, lhs: bool, rhs: bool) -> bool {
    match op {
        BoolOp::And => lhs && rhs,
        BoolOp::Or => lhs || rhs,
    }
}

spec fn eval_expr(expr: BoolExpr) -> bool
    decreases expr,
{
    match expr {
        BoolExpr::Leaf(value) => value,
        BoolExpr::Bin(op, lhs, rhs) => eval_op(op, eval_expr(*lhs), eval_expr(*rhs)),
    }
}

spec fn compile_postfix(expr: BoolExpr) -> Seq<PostfixNode>
    decreases expr,
{
    match expr {
        BoolExpr::Leaf(value) => seq![PostfixNode::Val(value)],
        BoolExpr::Bin(op, lhs, rhs) => {
            compile_postfix(*lhs) + (compile_postfix(*rhs) + seq![PostfixNode::Op(op)])
        }
    }
}

spec fn step(node: PostfixNode, stack: Seq<bool>) -> Seq<bool> {
    match node {
        PostfixNode::Val(value) => stack.push(value),
        PostfixNode::Op(op) => {
            if stack.len() < 2 {
                stack
            } else {
                let rhs = stack[stack.len() - 1];
                let lhs = stack[stack.len() - 2];
                stack.subrange(0, stack.len() - 2).push(eval_op(op, lhs, rhs))
            }
        }
    }
}

spec fn run_postfix(nodes: Seq<PostfixNode>, stack: Seq<bool>) -> Seq<bool>
    decreases nodes.len(),
{
    if nodes.len() == 0 {
        stack
    } else {
        run_postfix(nodes.subrange(1, nodes.len() as int), step(nodes[0], stack))
    }
}

proof fn lemma_run_postfix_append(
    prefix: Seq<PostfixNode>,
    suffix: Seq<PostfixNode>,
    stack: Seq<bool>,
)
    ensures
        run_postfix(prefix + suffix, stack) == run_postfix(suffix, run_postfix(prefix, stack)),
    decreases prefix.len(),
{
    if prefix.len() == 0 {
    } else {
        assert((prefix + suffix)[0] == prefix[0]);
        assert((prefix + suffix).subrange(1, (prefix + suffix).len() as int)
            == prefix.subrange(1, prefix.len() as int) + suffix);
        lemma_run_postfix_append(
            prefix.subrange(1, prefix.len() as int),
            suffix,
            step(prefix[0], stack),
        );
    }
}

proof fn lemma_run_postfix_single(node: PostfixNode, stack: Seq<bool>)
    ensures
        run_postfix(seq![node], stack) == step(node, stack),
{
    assert(seq![node][0] == node);
    assert(seq![node].subrange(1, 1) == Seq::<PostfixNode>::empty());
    assert(run_postfix(seq![node], stack) == run_postfix(Seq::<PostfixNode>::empty(), step(node, stack)));
    assert(run_postfix(Seq::<PostfixNode>::empty(), step(node, stack)) == step(node, stack));
}

proof fn lemma_compile_postfix_correct(expr: BoolExpr, stack: Seq<bool>)
    ensures
        run_postfix(compile_postfix(expr), stack) == stack.push(eval_expr(expr)),
    decreases expr,
{
    match expr {
        BoolExpr::Leaf(value) => {
            assert(compile_postfix(expr) == seq![PostfixNode::Val(value)]);
            lemma_run_postfix_single(PostfixNode::Val(value), stack);
            assert(step(PostfixNode::Val(value), stack) == stack.push(value));
            assert(run_postfix(compile_postfix(expr), stack) == stack.push(eval_expr(expr)));
        }
        BoolExpr::Bin(op, lhs, rhs) => {
            assert(
                compile_postfix(expr)
                    == compile_postfix(*lhs) + (compile_postfix(*rhs) + seq![PostfixNode::Op(op)])
            );
            assert(eval_expr(expr) == eval_op(op, eval_expr(*lhs), eval_expr(*rhs)));
            lemma_run_postfix_append(compile_postfix(*lhs), compile_postfix(*rhs) + seq![PostfixNode::Op(op)], stack);
            lemma_compile_postfix_correct(*lhs, stack);
            let lhs_stack = stack.push(eval_expr(*lhs));
            assert(
                run_postfix(compile_postfix(expr), stack)
                    == run_postfix(
                        compile_postfix(*lhs) + (compile_postfix(*rhs) + seq![PostfixNode::Op(op)]),
                        stack,
                    )
            );
            assert(
                run_postfix(
                    compile_postfix(*lhs) + (compile_postfix(*rhs) + seq![PostfixNode::Op(op)]),
                    stack,
                ) == run_postfix(
                    compile_postfix(*rhs) + seq![PostfixNode::Op(op)],
                    run_postfix(compile_postfix(*lhs), stack),
                )
            );
            assert(
                run_postfix(compile_postfix(expr), stack)
                    == run_postfix(
                        compile_postfix(*rhs) + seq![PostfixNode::Op(op)],
                        run_postfix(compile_postfix(*lhs), stack),
                    )
            );
            assert(run_postfix(compile_postfix(*lhs), stack) == lhs_stack);
            assert(
                run_postfix(compile_postfix(expr), stack)
                    == run_postfix(compile_postfix(*rhs) + seq![PostfixNode::Op(op)], lhs_stack)
            );

            lemma_run_postfix_append(compile_postfix(*rhs), seq![PostfixNode::Op(op)], lhs_stack);
            lemma_compile_postfix_correct(*rhs, lhs_stack);
            let rhs_stack = lhs_stack.push(eval_expr(*rhs));
            assert(
                run_postfix(compile_postfix(*rhs) + seq![PostfixNode::Op(op)], lhs_stack)
                    == run_postfix(
                        seq![PostfixNode::Op(op)],
                        run_postfix(compile_postfix(*rhs), lhs_stack),
                    )
            );
            assert(run_postfix(compile_postfix(*rhs), lhs_stack) == rhs_stack);
            assert(
                run_postfix(compile_postfix(expr), stack)
                    == run_postfix(seq![PostfixNode::Op(op)], rhs_stack)
            );

            assert(step(PostfixNode::Op(op), rhs_stack) == stack.push(eval_op(op, eval_expr(*lhs), eval_expr(*rhs))));
            lemma_run_postfix_single(PostfixNode::Op(op), rhs_stack);
            assert(run_postfix(seq![PostfixNode::Op(op)], rhs_stack) == stack.push(eval_expr(expr)));
            assert(run_postfix(compile_postfix(expr), stack) == stack.push(eval_expr(expr)));
        }
    }
}

proof fn lemma_compile_postfix_total(expr: BoolExpr)
    ensures
        run_postfix(compile_postfix(expr), Seq::<bool>::empty())
            == Seq::<bool>::empty().push(eval_expr(expr)),
{
    lemma_compile_postfix_correct(expr, Seq::<bool>::empty());
}

} // verus!
