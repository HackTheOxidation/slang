pub mod ivl;
mod ivl_ext;

use ivl::{IVLCmd, IVLCmdKind};
use slang::ast::{Cmd, CmdKind, Expr, Ident};
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
            // Calculate obligation and error message (if obligation is not
            // verified)
            let (oblig, msg) = wp(&ivl, &Expr::bool(true))?;
            // Convert obligation to SMT expression
            let soblig = oblig.smt()?;

            // Run the following solver-related statements in a closed scope.
            // That is, after exiting the scope, all assertions are forgotten
            // from subsequent executions of the solver
            solver.scope(|solver| {
                // Check validity of obligation
                solver.assert(!soblig.as_bool()?)?;
                // Run SMT solver on all current assertions
                match solver.check_sat_with_model()? {
                    // If the obligations result not valid, report the error (on
                    // the span in which the error happens)
                    smtlib::SatResultWithModel::Sat(model) => {
                        cx.error(oblig.span, format!("{msg}: {model}"));
                    }
                    smtlib::SatResultWithModel::Unknown => {
                        cx.warning(oblig.span, "{msg}: unknown sat result");
                    }
                    smtlib::SatResultWithModel::Unsat => (),
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
        CmdKind::Assert { condition, .. } => Ok(IVLCmd::assert(condition, "Assert might fail!")),
        CmdKind::Assume { condition } => Ok(IVLCmd::assume(condition)),
        CmdKind::Assignment { name, expr } => {
            // TODO: Transform C into DSA (Module 05-04, 5:03)
            let expr = expr;
            Ok(IVLCmd::assign(name, expr))
        },
        CmdKind::Seq(c1, c2) => Ok(IVLCmd::seq(&cmd_to_ivlcmd(c1)?, &cmd_to_ivlcmd(c2)?)),
        CmdKind::Match { body } => {
            Ok(IVLCmd::nondets(
                    &body.cases
                    .iter()
                    .cloned()
                    .map(|case| {
                        if let Ok(encoding) = cmd_to_ivlcmd(&case.cmd) {
                            IVLCmd::seq(&IVLCmd::assume(&case.condition), &encoding)
                        } else {
                            IVLCmd::unreachable()
                        }
                    })
                    .collect::<Vec<IVLCmd>>()
                    .as_slice()))
        },
        _ => todo!("Not supported (yet)."),
    }
}

// Weakest precondition of (assert-only) IVL programs comprised of a single
// assertion
fn wp(ivl: &IVLCmd, g: &Expr) -> Result<(Expr, String)> {
    match &ivl.kind {
        IVLCmdKind::Assert { condition, message } => Ok((Expr::and(&condition, &g), message.clone())),
        IVLCmdKind::Assume { condition } => Ok((Expr::imp(&condition, &g), format!("Assume {}", condition))),
        IVLCmdKind::Seq(c1, c2) => {
            let (wp_c2, _) = wp(c2, g)?;
            wp(c1, &wp_c2)
        },
        IVLCmdKind::NonDet(c1, c2) => {
            let (wp_c1, _) = wp(c1, g)?;
            let (wp_c2, _) = wp(c2, g)?;
            Ok((Expr::and(&wp_c1, &wp_c2), "NonDet".to_string()))
        },
        IVLCmdKind::Assignment { name, expr } => {
            // TODO Passification: encode every assignment as x := e as assume x == e.
            // (Module 05-04, 5:03)
            let name = Expr::new_typed(slang::ast::ExprKind::Ident(Ident(name.as_str().to_string())), slang::ast::Type::Bool);
            wp(&IVLCmd::assume(&name.op(slang::ast::Op::Eq, &expr)), &g)
        },
        _ => todo!("{}", format!("{} - Not supported (yet).", ivl)),
    }
}
