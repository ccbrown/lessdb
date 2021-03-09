use super::storage::{Storage, Tree, Value};
use anyhow::{Context, Result};
use bytes::Bytes;
use std::{path::Path, sync::RwLock};

pub struct Node {
    storage: RwLock<Storage>,
}

pub enum WriteExpressionSetCondition {
    Exists(bool),
    Equals(usize),
}

impl WriteExpressionSetCondition {
    fn evaluate(
        &self,
        ctx: &ExpressionContext,
        value: Option<&Value>,
    ) -> Result<bool, ExpressionError> {
        Ok(match self {
            Self::Exists(exists) => *exists == value.is_some(),
            Self::Equals(other) => value == Some(ctx.value(*other)?),
        })
    }
}

#[derive(Debug, thiserror::Error)]
pub enum ExpressionError {
    #[error("undefined index: {0}")]
    UndefinedIndex(usize),
    #[error("invalid key index: {0}")]
    InvalidKeyIndex(usize),
    #[error(transparent)]
    Other(#[from] anyhow::Error),
}

#[derive(Debug, thiserror::Error)]
pub enum TransactionError {
    #[error("expression error: {0}")]
    ExpressionError(#[from] ExpressionError),
    #[error(transparent)]
    Other(#[from] anyhow::Error),
}

struct ExpressionContext {
    registers: Vec<Option<Value>>,
}

impl ExpressionContext {
    fn new(inputs: Vec<Value>) -> Self {
        Self {
            registers: inputs.into_iter().map(|v| Some(v)).collect(),
        }
    }

    fn value(&self, i: usize) -> Result<&Value, ExpressionError> {
        if i >= self.registers.len() {
            Err(ExpressionError::UndefinedIndex(i))
        } else {
            match &self.registers[i] {
                Some(v) => Ok(&v),
                None => Err(ExpressionError::UndefinedIndex(i)),
            }
        }
    }

    fn key(&self, i: usize) -> Result<&Bytes, ExpressionError> {
        if i >= self.registers.len() {
            Err(ExpressionError::UndefinedIndex(i))
        } else {
            match &self.registers[i] {
                Some(Value::Bytes(b)) => Ok(&b),
                None => Err(ExpressionError::UndefinedIndex(i)),
                _ => Err(ExpressionError::InvalidKeyIndex(i)),
            }
        }
    }

    fn set(&mut self, dest: usize, v: Option<Value>) {
        if self.registers.len() < dest {
            self.registers.resize(dest, None);
        }
        self.registers[dest] = v;
    }

    fn outputs(mut self, indices: Vec<usize>) -> Vec<Option<Value>> {
        indices
            .into_iter()
            .map(|i| {
                if i < self.registers.len() {
                    self.registers[i].take()
                } else {
                    None
                }
            })
            .collect()
    }
}

pub struct WriteTransaction {
    pub inputs: Vec<Value>,
    pub outputs: Vec<usize>,
    pub expr: WriteExpression,
}

pub enum WriteExpression {
    Clear {},
    Delete {
        key: usize,
    },
    Set {
        key: usize,
        value: usize,
        condition: Option<WriteExpressionSetCondition>,
    },
    Sequence {
        exprs: Vec<WriteExpression>,
    },
    Read {
        expr: ReadExpression,
    },
}

impl WriteExpression {
    fn evaluate(
        self,
        ctx: &mut ExpressionContext,
        mut tree: Tree,
    ) -> Result<Tree, ExpressionError> {
        Ok(match self {
            Self::Clear {} => tree.clear()?,
            Self::Delete { key } => {
                let (tree, _) = tree.delete(ctx.key(key)?)?;
                tree
            }
            Self::Set {
                key,
                value,
                condition,
            } => {
                let key = ctx.key(key)?.clone();
                let value = ctx.value(value)?.clone();
                let mut conditional_result = Ok(true);
                let tree = {
                    let conditional_result = &mut conditional_result;
                    tree.insert(key, |prev| {
                        match condition.map(|cond| cond.evaluate(ctx, prev)).transpose() {
                            Ok(pass) => {
                                if pass.unwrap_or(true) {
                                    Some(value)
                                } else {
                                    *conditional_result = Ok(false);
                                    None
                                }
                            }
                            Err(e) => {
                                *conditional_result = Err(e);
                                None
                            }
                        }
                    })?
                };
                conditional_result?;
                tree
            }
            Self::Read { expr } => {
                expr.evaluate(ctx, &tree)?;
                tree
            }
            Self::Sequence { exprs } => {
                for expr in exprs {
                    tree = expr.evaluate(ctx, tree)?;
                }
                tree
            }
        })
    }
}

pub struct ReadTransaction {
    pub inputs: Vec<Value>,
    pub outputs: Vec<usize>,
    pub expr: ReadExpression,
}

pub enum ReadExpression {
    Get { key: usize, dest: usize },
    Sequence { exprs: Vec<ReadExpression> },
}

impl ReadExpression {
    fn evaluate(self, ctx: &mut ExpressionContext, tree: &Tree) -> Result<(), ExpressionError> {
        match self {
            Self::Get { key, dest } => {
                ctx.set(dest, tree.get(ctx.key(key)?)?);
            }
            Self::Sequence { exprs } => {
                for expr in exprs {
                    expr.evaluate(ctx, tree)?;
                }
            }
        }
        Ok(())
    }
}

impl Node {
    pub fn new<P: AsRef<Path>>(data_path: P) -> Result<Self> {
        Ok(Self {
            storage: RwLock::new(
                Storage::open(data_path.as_ref().join("storage"))
                    .with_context(|| "unable to open storage")?,
            ),
        })
    }

    pub fn read(&self, tx: ReadTransaction) -> Result<Vec<Option<Value>>, TransactionError> {
        let storage = self.storage.read().expect("the lock shouldn't be poisoned");
        let tree = storage.tree();
        let mut ctx = ExpressionContext::new(tx.inputs);
        tx.expr.evaluate(&mut ctx, &tree)?;
        Ok(ctx.outputs(tx.outputs))
    }

    pub fn write(&self, tx: WriteTransaction) -> Result<Vec<Option<Value>>, TransactionError> {
        let mut storage = self
            .storage
            .write()
            .expect("the lock shouldn't be poisoned");
        let mut result = Ok(vec![]);
        {
            let result = &mut result;
            storage.commit(|tree| {
                let mut ctx = ExpressionContext::new(tx.inputs);
                let outputs = tx.outputs;
                Ok(match tx.expr.evaluate(&mut ctx, tree) {
                    Ok(tree) => {
                        *result = Ok(ctx.outputs(outputs));
                        Some(tree)
                    }
                    Err(e) => {
                        *result = Err(e);
                        None
                    }
                })
            })?;
        }
        Ok(result?)
    }
}
