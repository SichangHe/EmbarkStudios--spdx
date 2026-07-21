use std::collections::BTreeSet;

use spdx::expression::{ExprNode, Operator};

const IDS: [&str; 4] = ["MIT", "Apache-2.0", "BSD-2-Clause", "ISC"];

#[derive(Clone, Debug)]
enum BoolExpr {
    Leaf(usize),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum PostfixNode {
    Leaf(usize),
    And,
    Or,
}

impl BoolExpr {
    fn precedence(&self) -> u8 {
        match self {
            Self::Leaf(_) => 3,
            Self::And(_, _) => 2,
            Self::Or(_, _) => 1,
        }
    }

    fn render_variants(&self) -> BTreeSet<String> {
        self.render_in_context(None)
    }

    fn render_in_context(&self, parent_prec: Option<u8>) -> BTreeSet<String> {
        let needs_parens = parent_prec.is_some_and(|prec| self.precedence() <= prec);
        let mut rendered = BTreeSet::new();

        match self {
            Self::Leaf(index) => {
                let body = IDS[*index].to_string();
                let structural = if needs_parens {
                    format!("({body})")
                } else {
                    body
                };
                rendered.insert(structural.clone());
                rendered.insert(format!("({structural})"));
            }
            Self::And(lhs, rhs) | Self::Or(lhs, rhs) => {
                let op = if matches!(self, Self::And(_, _)) {
                    "AND"
                } else {
                    "OR"
                };

                for left in lhs.render_in_context(Some(self.precedence())) {
                    for right in rhs.render_in_context(Some(self.precedence())) {
                        let body = format!("{left} {op} {right}");
                        let structural = if needs_parens {
                            format!("({body})")
                        } else {
                            body
                        };
                        rendered.insert(structural.clone());
                        rendered.insert(format!("({structural})"));
                    }
                }
            }
        }

        rendered
    }

    fn compile_postfix(&self, out: &mut Vec<PostfixNode>) {
        match self {
            Self::Leaf(index) => out.push(PostfixNode::Leaf(*index)),
            Self::And(lhs, rhs) => {
                lhs.compile_postfix(out);
                rhs.compile_postfix(out);
                out.push(PostfixNode::And);
            }
            Self::Or(lhs, rhs) => {
                lhs.compile_postfix(out);
                rhs.compile_postfix(out);
                out.push(PostfixNode::Or);
            }
        }
    }

    fn evaluate(&self, valuation: &[bool]) -> bool {
        match self {
            Self::Leaf(index) => valuation[*index],
            Self::And(lhs, rhs) => lhs.evaluate(valuation) && rhs.evaluate(valuation),
            Self::Or(lhs, rhs) => lhs.evaluate(valuation) || rhs.evaluate(valuation),
        }
    }
}

fn generate_exprs(start: usize, len: usize) -> Vec<BoolExpr> {
    if len == 1 {
        return vec![BoolExpr::Leaf(start)];
    }

    let mut exprs = Vec::new();
    for split in 1..len {
        let lefts = generate_exprs(start, split);
        let rights = generate_exprs(start + split, len - split);
        for lhs in &lefts {
            for rhs in &rights {
                exprs.push(BoolExpr::And(Box::new(lhs.clone()), Box::new(rhs.clone())));
                exprs.push(BoolExpr::Or(Box::new(lhs.clone()), Box::new(rhs.clone())));
            }
        }
    }

    exprs
}

fn expected_postfix(expr: &BoolExpr) -> Vec<PostfixNode> {
    let mut postfix = Vec::new();
    expr.compile_postfix(&mut postfix);
    postfix
}

fn actual_postfix(surface: &str) -> Vec<PostfixNode> {
    let parsed = spdx::Expression::parse(surface).unwrap();
    parsed
        .iter()
        .map(|node| match node {
            ExprNode::Req(req) => {
                PostfixNode::Leaf(index_of_id(req.req.license.id().unwrap().name))
            }
            ExprNode::Op(Operator::And) => PostfixNode::And,
            ExprNode::Op(Operator::Or) => PostfixNode::Or,
        })
        .collect()
}

fn index_of_id(name: &str) -> usize {
    IDS.iter().position(|candidate| *candidate == name).unwrap()
}

fn valuation_for(len: usize, mask: usize) -> Vec<bool> {
    (0..len).map(|bit| ((mask >> bit) & 1) == 1).collect()
}

#[test]
fn boolean_expression_core_bridge_matches_public_parse_and_evaluate() {
    let mut surfaces_checked = 0usize;
    let mut evaluations_checked = 0usize;

    for len in 1..=IDS.len() {
        for expr in generate_exprs(0, len) {
            let expected = expected_postfix(&expr);
            for surface in expr.render_variants() {
                let actual = actual_postfix(&surface);
                assert_eq!(actual, expected, "postfix mismatch for {surface}");
                surfaces_checked += 1;

                let parsed = spdx::Expression::parse(&surface).unwrap();
                for mask in 0..(1usize << len) {
                    let valuation = valuation_for(len, mask);
                    let expected_value = expr.evaluate(&valuation);
                    let actual_value = parsed
                        .evaluate(|req| valuation[index_of_id(req.license.id().unwrap().name)]);
                    assert_eq!(
                        actual_value, expected_value,
                        "evaluation mismatch for {surface} with valuation {valuation:?}",
                    );
                    evaluations_checked += 1;
                }
            }
        }
    }

    eprintln!(
        "boolean_expression_core_bridge checked {surfaces_checked} surfaces and {evaluations_checked} evaluations"
    );
}

#[test]
fn boolean_expression_core_rejects_basic_malformed_inputs() {
    for surface in ["MIT OR", "(MIT OR Apache-2.0", "MIT Apache-2.0", "AND MIT"] {
        assert!(
            spdx::Expression::parse(surface).is_err(),
            "unexpectedly accepted {surface}"
        );
    }
}
