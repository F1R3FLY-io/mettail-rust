//! `Rholang` process fragment island plugin (minimal GST).

use crate::error::{Result, SpecError};
use crate::island::plugin::{template_from_token, IslandArtifact, IslandPlugin, ProcGst, ProcStmt};
use crate::island::token::decode_island_body;
use crate::surface::IslandToken;

pub struct RholangProcPlugin;

impl IslandPlugin for RholangProcPlugin {
    fn lang_names(&self) -> &[&str] {
        &["Rholang", "rholang", "Proc", "proc"]
    }

    fn process(&self, token: &IslandToken) -> Result<IslandArtifact> {
        let _template = template_from_token(token);
        let decoded = decode_island_body(&token.body)?;
        let gst = parse_proc_gst(&decoded.text)?;
        Ok(IslandArtifact::RholangProc { gst })
    }
}

fn parse_proc_gst(body: &str) -> Result<ProcGst> {
    let trimmed = body.trim();
    if trimmed.is_empty() {
        return Ok(ProcGst::Empty);
    }
    let mut stmts = Vec::new();
    for line in trimmed.lines().map(str::trim).filter(|l| !l.is_empty()) {
        stmts.push(parse_line(line)?);
    }
    if stmts.len() == 1 {
        Ok(ProcGst::Stmt(stmts.into_iter().next().unwrap()))
    } else {
        Ok(ProcGst::Seq(stmts.into_iter().map(ProcGst::Stmt).collect()))
    }
}

fn parse_line(line: &str) -> Result<ProcStmt> {
    if let Some(rest) = line.strip_prefix("let ") {
        let (name, body) = rest.split_once('=').ok_or_else(|| SpecError::Island {
            lang: "Rholang".into(),
            message: format!("expected `=` in let binding: {line}"),
        })?;
        return Ok(ProcStmt::Let {
            name: name.trim().to_string(),
            body: body.trim().trim_end_matches(';').to_string(),
        });
    }
    if let Some(rest) = line.strip_prefix("for ") {
        return Ok(ProcStmt::For {
            bind: String::new(),
            source: rest.trim().trim_end_matches(';').to_string(),
            body: String::new(),
        });
    }
    if line.contains("!") {
        let parts: Vec<&str> = line.split('!').collect();
        if parts.len() >= 2 {
            return Ok(ProcStmt::Send {
                channel: parts[0].trim().to_string(),
                payload: parts[1].trim().trim_end_matches(';').to_string(),
            });
        }
    }
    Ok(ProcStmt::Raw(line.to_string()))
}
