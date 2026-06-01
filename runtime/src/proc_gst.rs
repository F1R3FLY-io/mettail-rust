#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProcGst {
    Empty,
    Stmt(ProcStmt),
    Seq(Vec<ProcGst>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProcStmt {
    Let {
        name: String,
        body: String,
    },
    For {
        bind: String,
        source: String,
        body: String,
    },
    Send {
        channel: String,
        payload: String,
    },
    Raw(String),
}
