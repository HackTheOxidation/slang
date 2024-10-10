pub mod ivl;
mod ivl_ext;

use ivl::{IVLCmd, IVLCmdKind};
use slang::ast::{Cmd, CmdKind, Expr, Ident};
use slang_ui::prelude::slang::ast::{Name, Type};
use slang_ui::prelude::slang::Span;
use slang_ui::prelude::*;

pub struct App;

impl slang_ui::Hook for App {
    fn analyze(&self, cx: &mut slang_ui::Context, file: &slang::SourceFile) -> Result<()> {
        // Get reference to Z3 solver
        let mut solver = cx.solver()?;

        // Iterate methods
        for m in file.methods() {
            // Get method's preconditions;
            let pres = m.requires();
            // Merge them into a single condition
            let pre = pres
                .cloned()
                .reduce(|a, b| a & b)
                .unwrap_or(Expr::bool(true));
            // Convert the expression into an SMT expression
            let spre = pre.smt()?;
            // Assert precondition
            solver.assert(spre.as_bool()?)?;

            // Get method's body
            let cmd = &m.body.clone().unwrap().cmd;
            // Encode it in IVL
            let ivl = cmd_to_ivlcmd(cmd)?;

            // Determine the post-condition
            let g = m.ensures()
                .cloned()
                .reduce(|a, b| a & b)
                .unwrap_or(Expr::bool(true));

            // Calculate obligation and error message (if obligation is not
            // verified)
            let (oblig, msg) = wp(&ivl, &g)?;
            // Convert obligation to SMT expression
            let soblig = oblig.smt()?;

            // Run the following solver-related statements in a closed scope.
            // That is, after exiting the scope, all assertions are forgotten
            // from subsequent executions of the solver
            solver.scope(|solver| {
                // Check validity of obligation
                solver.assert(!soblig.as_bool()?)?;
                // Run SMT solver on all current assertions
                match solver.check_sat()? {
                    // If the obligations result not valid, report the error (on
                    // the span in which the error happens)
                    smtlib::SatResult::Sat => {
                        cx.error(oblig.span, format!("{msg}"));
                    }
                    smtlib::SatResult::Unknown => {
                        cx.warning(oblig.span, "{msg}: unknown sat result");
                    }
                    smtlib::SatResult::Unsat => (),
                }
                Ok(())
            })?;
        }

        Ok(())
    }
}

// Transforms a command, C, into Dynamic Single Assignment (DSA) form
fn cmd_to_dsa(cmd: &Cmd) -> &Cmd {
    cmd
}

// Encoding of (assert-only) statements into IVL (for programs comprised of only
// a single assertion)
fn cmd_to_ivlcmd(cmd: &Cmd) -> Result<IVLCmd> {
    let cmd = cmd_to_dsa(cmd);
    match &cmd.kind {
        CmdKind::Assert { condition, message } => Ok(IVLCmd::assert(condition, &message.clone())),
        CmdKind::Assume { condition } => Ok(IVLCmd::assume(condition)),
        CmdKind::Assignment { name, expr } => {
            // TODO: Transform C into DSA (Module 05-04, 5:03)
            Ok(IVLCmd::assign(name, expr))
        }
        CmdKind::Seq(c1, c2) => Ok(IVLCmd::seq(&cmd_to_ivlcmd(c1)?, &cmd_to_ivlcmd(c2)?)),
        CmdKind::Match { body } => {
            Ok(IVLCmd::nondets(
                &body.cases
                    .iter()
                    .cloned()
                    .map(|case| {
                        IVLCmd::seq(&IVLCmd::assume(&case.condition), &cmd_to_ivlcmd(&case.cmd).unwrap())
                    })
                    .collect::<Vec<IVLCmd>>()
                    .as_slice()))
        }
        CmdKind::MethodCall { name, fun_name, method, .. } => {
            let method = method.get().unwrap();
            let return_ty = method.return_ty.clone().unwrap().1.clone();

            let requires = method.requires().fold(Expr::bool(true), |acc, e| acc.and(e));
            let ensures = method.ensures().fold(Expr::bool(true), |acc, e| acc.and(e));

            let message = format!("Asserting pre-condition for method call to: '{}' - {}:{}", fun_name.as_str(), fun_name.span.start(), fun_name.span.end());

            Ok(IVLCmd::seq(
                &IVLCmd::assert(&requires, message.as_str()),
                &IVLCmd::seq(&IVLCmd::havoc(&name.clone().unwrap(), &return_ty),
                             &IVLCmd::assume(&ensures))))
        }
        CmdKind::VarDefinition { name, ty, expr } => {
            if let Some(expr) = expr {
                Ok(IVLCmd::assign(&name.clone(), &expr))
            } else {
                Ok(IVLCmd::havoc(&name.clone(), &ty.clone().1))
            }
        }
        CmdKind::Return { expr } => {
            // We assume that the operational semantics of return is simply an assignment
            // to the result/output variable.
            let name = Name { span: cmd.span, ident: Ident("result".to_string()) };
            if let Some(expr) = expr {
                Ok(IVLCmd::assign(&name, expr))
            } else {
                Ok(IVLCmd::havoc(&name, &Type::Unresolved))
            }
        }
        _ => todo!("{}", format!("{:?} - Not supported (yet)", cmd.kind)),
    }
}

// Weakest precondition of (assert-only) IVL programs comprised of a single
// assertion
fn wp(ivl: &IVLCmd, g: &Expr) -> Result<(Expr, String)> {
    match &ivl.kind {
        IVLCmdKind::Assert { condition, message } =>
            Ok((condition.and(&g).with_span(condition.span), format!("Assertion failure: '{}' - {}:{}", message, condition.span.start(), condition.span.end()))),
        IVLCmdKind::Assume { condition } =>
            Ok((condition.imp(&g).with_span(condition.span), format!("Assume {} - {}:{}", condition, condition.span.start(), condition.span.end()))),
        IVLCmdKind::Seq(c1, c2) => wp(c2, g).and_then(|(wp_c2, _)| wp(c1, &wp_c2)),
        IVLCmdKind::NonDet(c1, c2) => {
            let (wp_c1, message_c1) = wp(c1, &g.with_span(c1.span))?;
            let (wp_c2, message_c2) = wp(c2, &g.with_span(c2.span))?;
            Ok((wp_c1.and(&wp_c2), format!("NonDet '{} || {}'", message_c1, message_c2)))
        }
        IVLCmdKind::Assignment { name, expr } => {
            // TODO Passification: encode every assignment as x := e as assume x == e.
            // (Module 05-04, 5:03)
            let out_expr = if name.ident.as_str() == "result" {
                g.subst_ident(&name.ident, &Expr::result(&expr.ty)).subst_result(expr)
            } else {
                g.subst_ident(&name.ident, expr)
            };
            Ok((out_expr.with_span(Span::from_start_end(name.span.start(), expr.span.end())), format!("Assignment of '{}' to '{}'", name, expr)))
            //wp(&IVLCmd::assume(&expr.op(Eq, &Expr::ident(&name.ident, &expr.ty.clone()))), &g)
        }
        IVLCmdKind::Havoc { name, ty: _ty } => {
            // TODO: Figure out the operational semantics of havoc
            // (remove "name" from G?)
            // (Module 05-05, 16:48)
            Ok((g.clone(), format!("Havoc'ing {}", name)))
        }
    }
}
