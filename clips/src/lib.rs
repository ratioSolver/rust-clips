use clips_sys::clips;
use std::{borrow::Cow, marker};

#[derive(Debug)]
pub struct Environment {
    raw: *mut clips::Environment,
    cleanup: bool,
}

#[derive(Debug)]
pub struct Fact<'env> {
    raw: *const clips::Fact,
    _marker: marker::PhantomData<&'env Environment>,
}

#[derive(Debug)]
pub struct Instance<'env> {
    raw: *mut clips::Instance,
    _marker: marker::PhantomData<&'env Environment>,
}

#[derive(Debug)]
pub struct ExternalAddress;

#[derive(Debug)]
pub enum ClipsValue<'env> {
    Symbol(Cow<'env, str>),
    Lexeme(Cow<'env, str>),
    Float(f64),
    Integer(i64),
    Void(),
    Multifield(Vec<ClipsValue<'env>>),
    Fact(Fact<'env>),
    InstanceName(Cow<'env, str>),
    Instance(Instance<'env>),
    ExternalAddress(ExternalAddress),
}
