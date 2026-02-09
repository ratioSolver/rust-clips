use clips_sys::clips;
use std::{borrow::Cow, ffi::CString, fmt::Display, path::Path};

#[derive(Debug)]
pub enum ClipsError {
    CreateEnvironmentError,
    ClearError,
    LoadFromStringError(String),
    RemoveUDFError(String),
    BatchStarError(String),
    LoadOpenFileError(String),
    LoadParsingError(String),
    AddUDFMinExceedsMaxError(String),
    AddUDFFunctionNameInUseError(String),
    AddUDFInvalidArgumentTypeError(String),
    AddUDFInvalidReturnTypeError(String),
}

impl Display for ClipsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            ClipsError::CreateEnvironmentError => write!(f, "Failed to create environment"),
            ClipsError::ClearError => write!(f, "Failed to clear environment"),
            ClipsError::LoadFromStringError(s) => write!(f, "Failed to load from string: {s}"),
            ClipsError::RemoveUDFError(s) => write!(f, "Failed to remove UDF: {s}"),
            ClipsError::BatchStarError(s) => write!(f, "Batch* error: {s}"),
            ClipsError::LoadOpenFileError(s) => write!(f, "Failed to open file: {s}"),
            ClipsError::LoadParsingError(s) => write!(f, "Failed to parse file: {s}"),
            ClipsError::AddUDFMinExceedsMaxError(s) => write!(f, "Minimum number of arguments exceeds maximum for UDF '{s}'"),
            ClipsError::AddUDFFunctionNameInUseError(s) => write!(f, "Function name '{s}' is already in use for UDF"),
            ClipsError::AddUDFInvalidArgumentTypeError(s) => write!(f, "Invalid argument type for UDF '{s}'"),
            ClipsError::AddUDFInvalidReturnTypeError(s) => write!(f, "Invalid return type for UDF '{s}'"),
        }
    }
}

#[derive(Debug)]
pub struct Environment {
    raw: *mut clips::Environment,
}

impl Environment {
    pub fn new() -> Result<Self, ClipsError> {
        let raw = unsafe { clips::CreateEnvironment() };
        if raw.is_null() { Err(ClipsError::CreateEnvironmentError) } else { Ok(Self { raw }) }
    }

    pub fn clear(&mut self) -> Result<(), ClipsError> {
        if unsafe { clips::Clear(self.raw) } { Ok(()) } else { Err(ClipsError::ClearError) }
    }

    pub fn load_from_str(&mut self, string: &str) -> Result<(), ClipsError> {
        if unsafe { clips::LoadFromString(self.raw, string.as_ptr() as *const i8, string.len()) } { Ok(()) } else { Err(ClipsError::LoadFromStringError(string.to_owned()).into()) }
    }

    pub fn load(&mut self, path: &Path) -> Result<(), ClipsError> {
        let path_str = CString::new(path.to_str().unwrap()).unwrap();
        let load_error = unsafe { clips::Load(self.raw, path_str.as_ptr() as *const i8) };

        match load_error {
            x if x == clips::LoadError_LE_NO_ERROR => Ok(()),
            x if x == clips::LoadError_LE_OPEN_FILE_ERROR as u32 => Err(ClipsError::LoadOpenFileError(path.to_str().unwrap().to_owned()).into()),
            x if x == clips::LoadError_LE_PARSING_ERROR as u32 => Err(ClipsError::LoadParsingError(path.to_str().unwrap().to_owned()).into()),
            _ => unreachable!(),
        }
    }

    pub fn reset(&mut self) {
        unsafe { clips::Reset(self.raw) };
    }

    pub fn run(&mut self, limit: i64) -> i64 {
        unsafe { clips::Run(self.raw, limit) }
    }

    pub fn fact_builder(&self, template_name: &str) -> FactBuilder {
        FactBuilder::new(self, template_name)
    }
}

#[derive(Debug)]
pub struct FactBuilder {
    raw: *mut clips::FactBuilder,
}

impl FactBuilder {
    fn new(env: &Environment, template_name: &str) -> Self {
        let template_name_cstr = CString::new(template_name).unwrap();
        let raw = unsafe { clips::CreateFactBuilder(env.raw, template_name_cstr.as_ptr() as *const i8) };
        Self { raw }
    }
}

impl Drop for FactBuilder {
    fn drop(&mut self) {
        unsafe { clips::FBDispose(self.raw) };
    }
}

#[derive(Debug)]
pub struct Fact {
    raw: *const clips::Fact,
}

#[derive(Debug)]
pub struct Instance {
    raw: *mut clips::Instance,
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
    Fact(Fact),
    InstanceName(Cow<'env, str>),
    Instance(Instance),
    ExternalAddress(ExternalAddress),
}

impl Drop for Environment {
    fn drop(&mut self) {
        unsafe { clips::DestroyEnvironment(self.raw) };
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_environment_creation() {
        let env = Environment::new();
        assert!(env.is_ok());
    }

    #[test]
    fn test_environment_clear() {
        let mut env = Environment::new().unwrap();
        let result = env.clear();
        assert!(result.is_ok());
    }

    #[test]
    fn test_load_from_string() {
        let mut env = Environment::new().unwrap();
        let result = env.load_from_str("(deftemplate test_deftemplate)");
        assert!(result.is_ok());
    }
}
