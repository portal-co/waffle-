use crate::{
    pool::ListRef, Block, BlockDef, BlockTarget, FunctionBody, Operator, Terminator, Value,
    ValueDef,
};

impl cfg_traits::Func for FunctionBody {
    type Block = Block;
    type Blocks = EntityVec<Block, BlockDef>;
    fn blocks(&self) -> &Self::Blocks {
        &self.blocks
    }
    fn blocks_mut(&mut self) -> &mut Self::Blocks {
        &mut self.blocks
    }

    fn entry(&self) -> Self::Block {
        self.entry
    }
}
impl ssa_traits::Func for FunctionBody {
    type Value = Value;

    type Values = EntityVec<Value, ValueDef>;

    fn values(&self) -> &Self::Values {
        &self.values
    }

    fn values_mut(&mut self) -> &mut Self::Values {
        &mut self.values
    }
}
impl ssa_traits::HasValues<FunctionBody> for ListRef<Value> {
    fn values<'a>(
        &'a self,
        f: &'a FunctionBody,
    ) -> Box<dyn Iterator<Item = <FunctionBody as ssa_traits::Func>::Value> + 'a> {
        Box::new(f.arg_pool[*self].iter().cloned())
    }

    fn values_mut<'a>(
        &'a mut self,
        g: &'a mut FunctionBody,
    ) -> Box<dyn Iterator<Item = &'a mut <FunctionBody as ssa_traits::Func>::Value> + 'a>
    where
        FunctionBody: 'a,
    {
        Box::new(g.arg_pool[*self].iter_mut())
    }
}
impl ssa_traits::Value<FunctionBody> for ValueDef {}
impl ssa_traits::HasValues<FunctionBody> for ValueDef {
    fn values<'a>(
        &'a self,
        f: &'a FunctionBody,
    ) -> Box<dyn Iterator<Item = <FunctionBody as ssa_traits::Func>::Value> + 'a> {
        Box::new(match self {
            ValueDef::BlockParam(_, _, _) => Either::Left(None.into_iter()),
            ValueDef::Operator(_, l, _) => Either::Right(f.arg_pool[*l].iter().cloned()),
            ValueDef::PickOutput(a, _, _) => Either::Left(Some(*a).into_iter()),
            ValueDef::Alias(w) => Either::Left(Some(*w).into_iter()),
            ValueDef::Placeholder(_) => todo!(),
            // ValueDef::Trace(_, _) => todo!(),
            ValueDef::None => Either::Left(None.into_iter()),
        })
    }

    fn values_mut<'a>(
        &'a mut self,
        g: &'a mut FunctionBody,
    ) -> Box<dyn Iterator<Item = &'a mut <FunctionBody as ssa_traits::Func>::Value> + 'a>
    where
        FunctionBody: 'a,
    {
        Box::new(match self {
            ValueDef::BlockParam(_, _, _) => Either::Left(None.into_iter()),
            ValueDef::Operator(_, l, _) => Either::Right(g.arg_pool[*l].iter_mut()),
            ValueDef::PickOutput(a, _, _) => Either::Left(Some(a).into_iter()),
            ValueDef::Alias(w) => Either::Left(Some(w).into_iter()),
            ValueDef::Placeholder(_) => todo!(),
            // ValueDef::Trace(_, _) => todo!(),
            ValueDef::None => Either::Left(None.into_iter()),
        })
    }
}
impl ssa_traits::op::OpValue<FunctionBody, Operator> for ValueDef {
    type Residue = ValueDef;

    type Capture = ListRef<Value>;
    type Spit = Vec<Type>;

    fn disasm(
        self,
        f: &mut FunctionBody,
    ) -> std::result::Result<(Operator, Self::Capture, Self::Spit), Self::Residue> {
        match self {
            ValueDef::Operator(a, b, c) => Ok((a, b, f.type_pool[c].to_owned())),
            s => Err(s),
        }
    }

    fn of(f: &mut FunctionBody, o: Operator, c: Self::Capture, s: Self::Spit) -> Option<Self> {
        Some(Self::Operator(o, c, f.type_pool.from_iter(s.into_iter())))
    }

    fn lift(f: &mut FunctionBody, r: Self::Residue) -> Option<Self> {
        Some(r)
    }
}
impl ssa_traits::op::OpValue<FunctionBody, u32> for ValueDef {
    type Residue = ValueDef;

    type Capture = Val<FunctionBody>;

    type Spit = Type;

    fn disasm(
        self,
        f: &mut FunctionBody,
    ) -> std::result::Result<(u32, Self::Capture, Self::Spit), Self::Residue> {
        match self {
            ValueDef::PickOutput(a, b, c) => Ok((b, Val(a), c)),
            s => Err(s),
        }
    }

    fn of(f: &mut FunctionBody, o: u32, c: Self::Capture, s: Self::Spit) -> Option<Self> {
        Some(Self::PickOutput(c.0, o, s))
    }

    fn lift(f: &mut FunctionBody, r: Self::Residue) -> Option<Self> {
        Some(r)
    }
}
impl cfg_traits::Block<FunctionBody> for BlockDef {
    type Terminator = Terminator;

    fn term(&self) -> &Self::Terminator {
        &self.terminator
    }

    fn term_mut(&mut self) -> &mut Self::Terminator {
        &mut self.terminator
    }
}
impl ssa_traits::Block<FunctionBody> for BlockDef {
    fn insts(&self) -> impl Iterator<Item = <FunctionBody as ssa_traits::Func>::Value> {
        self.insts.iter().cloned()
    }

    fn add_inst(
        func: &mut FunctionBody,
        key: <FunctionBody as cfg_traits::Func>::Block,
        v: <FunctionBody as ssa_traits::Func>::Value,
    ) {
        func.append_to_block(key, v)
    }
}

impl cfg_traits::Target<FunctionBody> for BlockTarget {
    fn block(&self) -> <FunctionBody as cfg_traits::Func>::Block {
        self.block
    }

    fn block_mut(&mut self) -> &mut <FunctionBody as cfg_traits::Func>::Block {
        &mut self.block
    }
}

impl ssa_traits::Target<FunctionBody> for BlockTarget {
    fn push_value(&mut self, v: <FunctionBody as ssa_traits::Func>::Value) {
        self.args.push(v)
    }

    fn from_values_and_block(
        a: impl Iterator<Item = <FunctionBody as ssa_traits::Func>::Value>,
        k: <FunctionBody as cfg_traits::Func>::Block,
    ) -> Self {
        BlockTarget {
            block: k,
            args: a.collect(),
        }
    }
}
impl cfg_traits::Term<FunctionBody> for BlockTarget {
    type Target = BlockTarget;

    fn targets<'a>(
        &'a self,
    ) -> Box<(dyn std::iter::Iterator<Item = &'a crate::func::BlockTarget> + 'a)>
    where
        FunctionBody: 'a,
    {
        Box::new(std::iter::once(self))
    }

    fn targets_mut<'a>(
        &'a mut self,
    ) -> Box<(dyn std::iter::Iterator<Item = &'a mut crate::func::BlockTarget> + 'a)>
    where
        FunctionBody: 'a,
    {
        Box::new(std::iter::once(self))
    }
}
impl ssa_traits::HasValues<FunctionBody> for BlockTarget {
    fn values<'a>(
        &'a self,
        f: &'a FunctionBody,
    ) -> Box<dyn Iterator<Item = <FunctionBody as ssa_traits::Func>::Value> + 'a> {
        Box::new(self.args.iter().cloned())
    }

    fn values_mut<'a>(
        &'a mut self,
        g: &'a mut FunctionBody,
    ) -> Box<(dyn std::iter::Iterator<Item = &'a mut crate::ir::Value> + 'a)>
    where
        FunctionBody: 'a,
    {
        Box::new(self.args.iter_mut())
    }
}
impl cfg_traits::Term<FunctionBody> for Terminator {
    type Target = BlockTarget;

    fn targets<'a>(&'a self) -> Box<(dyn std::iter::Iterator<Item = &'a func::BlockTarget> + 'a)>
    where
        FunctionBody: 'a,
    {
        Box::new(match self {
            Terminator::Br { target } => Either::Left(Some(target).into_iter()),
            Terminator::CondBr {
                cond,
                if_true,
                if_false,
            } => Either::Right(Either::Left(once(if_true).chain(once(if_false)))),
            Terminator::Select {
                value,
                targets,
                default,
            } => Either::Right(Either::Right(targets.iter().chain(once(default)))),
            Terminator::Return { values } => Either::Left(None.into_iter()),
            Terminator::ReturnCall { func, args } => Either::Left(None.into_iter()),
            Terminator::ReturnCallIndirect { sig, table, args } => Either::Left(None.into_iter()),
            Terminator::ReturnCallRef { sig, args } => Either::Left(None.into_iter()),
            Terminator::Unreachable => Either::Left(None.into_iter()),
            Terminator::None => Either::Left(None.into_iter()),
        })
    }

    fn targets_mut<'a>(
        &'a mut self,
    ) -> Box<(dyn std::iter::Iterator<Item = &'a mut func::BlockTarget> + 'a)>
    where
        FunctionBody: 'a,
    {
        Box::new(match self {
            Terminator::Br { target } => Either::Left(Some(target).into_iter()),
            Terminator::CondBr {
                cond,
                if_true,
                if_false,
            } => Either::Right(Either::Left(once(if_true).chain(once(if_false)))),
            Terminator::Select {
                value,
                targets,
                default,
            } => Either::Right(Either::Right(targets.iter_mut().chain(once(default)))),
            Terminator::Return { values } => Either::Left(None.into_iter()),
            Terminator::ReturnCall { func, args } => Either::Left(None.into_iter()),
            Terminator::ReturnCallIndirect { sig, table, args } => Either::Left(None.into_iter()),
            Terminator::ReturnCallRef { sig, args } => Either::Left(None.into_iter()),
            Terminator::Unreachable => Either::Left(None.into_iter()),
            Terminator::None => Either::Left(None.into_iter()),
        })
    }
}
impl ssa_traits::HasValues<FunctionBody> for Terminator {
    fn values<'a>(
        &'a self,
        f: &'a FunctionBody,
    ) -> Box<dyn Iterator<Item = <FunctionBody as ssa_traits::Func>::Value> + 'a> {
        Box::new(match self {
            Terminator::Br { target } => {
                Either::Right(Either::Right(Either::Left(target.values(f))))
            }
            Terminator::CondBr {
                cond,
                if_true,
                if_false,
            } => Either::Right(Either::Right(Either::Right(Either::Left(
                once(*cond).chain(if_true.values(f).chain(if_false.values(f))),
            )))),
            Terminator::Select {
                value,
                targets,
                default,
            } => Either::Right(Either::Right(Either::Right(Either::Right(
                once(*value).chain(
                    default
                        .values(f)
                        .chain(targets.iter().flat_map(move |x| x.values(f))),
                ),
            )))),
            Terminator::Return { values } => Either::Right(Either::Left(values.iter().cloned())),
            Terminator::ReturnCall { func, args } => {
                Either::Right(Either::Left(args.iter().cloned()))
            }
            Terminator::ReturnCallIndirect { sig, table, args } => {
                Either::Right(Either::Left(args.iter().cloned()))
            }
            Terminator::ReturnCallRef { sig, args } => {
                Either::Right(Either::Left(args.iter().cloned()))
            }
            Terminator::Unreachable => Either::Left(empty()),
            Terminator::None => Either::Left(empty()),
        })
    }

    fn values_mut<'a>(
        &'a mut self,
        g: &'a mut FunctionBody,
    ) -> Box<(dyn std::iter::Iterator<Item = &'a mut crate::ir::Value> + 'a)>
    where
        FunctionBody: 'a,
    {
        Box::new(match self {
            Terminator::Br { target } => {
                Either::Right(Either::Right(Either::Left(target.values_mut(g))))
            }
            Terminator::CondBr {
                cond,
                if_true,
                if_false,
            } => Either::Right(Either::Right(Either::Right(Either::Left(
                once(cond).chain(if_true.args.iter_mut().chain(if_false.values_mut(g))),
            )))),
            Terminator::Select {
                value,
                targets,
                default,
            } => Either::Right(Either::Right(Either::Right(Either::Right(
                once(value).chain(
                    default
                        .values_mut(g)
                        .chain(targets.iter_mut().flat_map(|x| x.args.iter_mut())),
                ),
            )))),
            Terminator::Return { values } => Either::Right(Either::Left(values.iter_mut())),
            Terminator::ReturnCall { func, args } => Either::Right(Either::Left(args.iter_mut())),
            Terminator::ReturnCallIndirect { sig, table, args } => {
                Either::Right(Either::Left(args.iter_mut()))
            }
            Terminator::ReturnCallRef { sig, args } => Either::Right(Either::Left(args.iter_mut())),
            Terminator::Unreachable => Either::Left(empty()),
            Terminator::None => Either::Left(empty()),
        })
    }
}
