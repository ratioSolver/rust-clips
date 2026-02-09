use clips_sys::clips;
use std::{
    borrow::Cow,
    ffi::{CStr, CString},
    fmt::Display,
    path::Path,
};

#[derive(Debug)]
pub enum ClipsError {
    CreateEnvironmentError,
    ClearError,
    LoadFromStringError(String),
    RemoveUDFError(String),
    BatchStarError(String),
    LoadOpenFileError(String),
    LoadParsingError(String),
    PutSlotSlotNotFoundError(String),
    PutSlotTypeError(String),
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
            ClipsError::PutSlotSlotNotFoundError(s) => write!(f, "Slot not found: {s}"),
            ClipsError::PutSlotTypeError(s) => write!(f, "Type error for slot: {s}"),
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

    pub fn clear(&self) -> Result<(), ClipsError> {
        if unsafe { clips::Clear(self.raw) } { Ok(()) } else { Err(ClipsError::ClearError) }
    }

    pub fn load_from_str(&self, string: &str) -> Result<(), ClipsError> {
        if unsafe { clips::LoadFromString(self.raw, string.as_ptr() as *const i8, string.len()) } { Ok(()) } else { Err(ClipsError::LoadFromStringError(string.to_owned()).into()) }
    }

    pub fn load(&self, path: &Path) -> Result<(), ClipsError> {
        let path_str = CString::new(path.to_str().unwrap()).unwrap();
        let load_error = unsafe { clips::Load(self.raw, path_str.as_ptr() as *const i8) };

        match load_error {
            clips::LoadError_LE_NO_ERROR => Ok(()),
            clips::LoadError_LE_OPEN_FILE_ERROR => Err(ClipsError::LoadOpenFileError(path.to_str().unwrap().to_owned()).into()),
            clips::LoadError_LE_PARSING_ERROR => Err(ClipsError::LoadParsingError(path.to_str().unwrap().to_owned()).into()),
            _ => unreachable!(),
        }
    }

    pub fn reset(&self) {
        unsafe { clips::Reset(self.raw) };
    }

    pub fn run(&self, limit: i64) -> i64 {
        unsafe { clips::Run(self.raw, limit) }
    }

    pub fn fact_builder(&self, template_name: &str) -> FactBuilder {
        FactBuilder::new(self, template_name)
    }

    pub fn multifield_builder(&self, size: usize) -> MultifieldBuilder {
        MultifieldBuilder::new(self, size)
    }

    pub fn add_udf(&mut self, name: &str, return_types: Option<Type>, min_args: u16, max_args: u16, arg_types: Vec<Type>, function: &dyn FnMut(&mut Self, &mut UDFContext) -> ClipsValue<'static>) -> Result<(), ClipsError> {
        let name_cstr = CString::new(name).unwrap();
        let return_types_mask = return_types.map_or("v".to_string(), |t| Type::format(&t));
        unimplemented!()
    }
}

impl Drop for Environment {
    fn drop(&mut self) {
        unsafe { clips::DestroyEnvironment(self.raw) };
    }
}

#[derive(Debug)]
pub struct Multifield {
    raw: *mut clips::Multifield,
}

impl Multifield {
    fn new(raw: *mut clips::Multifield) -> Self {
        Self { raw }
    }
}

#[derive(Debug)]
pub struct MultifieldBuilder {
    raw: *mut clips::MultifieldBuilder,
}

impl MultifieldBuilder {
    fn new(env: &Environment, size: usize) -> Self {
        let raw = unsafe { clips::CreateMultifieldBuilder(env.raw, size) };
        Self { raw }
    }

    pub fn put_int(&mut self, value: i64) {
        unsafe { clips::MBAppendInteger(self.raw, value) };
    }

    pub fn put_float(&mut self, value: f64) {
        unsafe { clips::MBAppendFloat(self.raw, value) };
    }

    pub fn put_symbol(&mut self, value: &str) {
        let value_cstr = CString::new(value).unwrap();
        unsafe { clips::MBAppendSymbol(self.raw, value_cstr.as_ptr() as *const i8) };
    }

    pub fn put_string(&mut self, value: &str) {
        let value_cstr = CString::new(value).unwrap();
        unsafe { clips::MBAppendString(self.raw, value_cstr.as_ptr() as *const i8) };
    }

    pub fn put_multifield(&mut self, value: Multifield) {
        unsafe { clips::MBAppendMultifield(self.raw, value.raw) };
    }

    pub fn create(self) -> Multifield {
        let raw = unsafe { clips::MBCreate(self.raw) };
        Multifield::new(raw)
    }
}

impl Drop for MultifieldBuilder {
    fn drop(&mut self) {
        unsafe { clips::MBDispose(self.raw) };
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

    pub fn put_int(&mut self, slot_name: &str, value: i64) -> Result<(), ClipsError> {
        let slot_name_cstr = CString::new(slot_name).unwrap();
        let put_int_error = unsafe { clips::FBPutSlotInteger(self.raw, slot_name_cstr.as_ptr() as *const i8, value) };
        match put_int_error {
            clips::PutSlotError_PSE_NO_ERROR => Ok(()),
            clips::PutSlotError_PSE_SLOT_NOT_FOUND_ERROR => Err(ClipsError::PutSlotSlotNotFoundError(slot_name.to_owned()).into()),
            clips::PutSlotError_PSE_TYPE_ERROR => Err(ClipsError::PutSlotTypeError(slot_name.to_owned()).into()),
            _ => unreachable!(),
        }
    }

    pub fn put_float(&mut self, slot_name: &str, value: f64) -> Result<(), ClipsError> {
        let slot_name_cstr = CString::new(slot_name).unwrap();
        let put_float_error = unsafe { clips::FBPutSlotFloat(self.raw, slot_name_cstr.as_ptr() as *const i8, value) };
        match put_float_error {
            clips::PutSlotError_PSE_NO_ERROR => Ok(()),
            clips::PutSlotError_PSE_SLOT_NOT_FOUND_ERROR => Err(ClipsError::PutSlotSlotNotFoundError(slot_name.to_owned()).into()),
            clips::PutSlotError_PSE_TYPE_ERROR => Err(ClipsError::PutSlotTypeError(slot_name.to_owned()).into()),
            _ => unreachable!(),
        }
    }

    pub fn put_symbol(&mut self, slot_name: &str, value: &str) -> Result<(), ClipsError> {
        let slot_name_cstr = CString::new(slot_name).unwrap();
        let value_cstr = CString::new(value).unwrap();
        let put_symbol_error = unsafe { clips::FBPutSlotSymbol(self.raw, slot_name_cstr.as_ptr() as *const i8, value_cstr.as_ptr() as *const i8) };
        match put_symbol_error {
            clips::PutSlotError_PSE_NO_ERROR => Ok(()),
            clips::PutSlotError_PSE_SLOT_NOT_FOUND_ERROR => Err(ClipsError::PutSlotSlotNotFoundError(slot_name.to_owned()).into()),
            clips::PutSlotError_PSE_TYPE_ERROR => Err(ClipsError::PutSlotTypeError(slot_name.to_owned()).into()),
            _ => unreachable!(),
        }
    }

    pub fn put_string(&mut self, slot_name: &str, value: &str) -> Result<(), ClipsError> {
        let slot_name_cstr = CString::new(slot_name).unwrap();
        let value_cstr = CString::new(value).unwrap();
        let put_string_error = unsafe { clips::FBPutSlotString(self.raw, slot_name_cstr.as_ptr() as *const i8, value_cstr.as_ptr() as *const i8) };
        match put_string_error {
            clips::PutSlotError_PSE_NO_ERROR => Ok(()),
            clips::PutSlotError_PSE_SLOT_NOT_FOUND_ERROR => Err(ClipsError::PutSlotSlotNotFoundError(slot_name.to_owned()).into()),
            clips::PutSlotError_PSE_TYPE_ERROR => Err(ClipsError::PutSlotTypeError(slot_name.to_owned()).into()),
            _ => unreachable!(),
        }
    }

    pub fn put_multifield(&mut self, slot_name: &str, value: Multifield) -> Result<(), ClipsError> {
        let slot_name_cstr = CString::new(slot_name).unwrap();
        let put_multifield_error = unsafe { clips::FBPutSlotMultifield(self.raw, slot_name_cstr.as_ptr() as *const i8, value.raw) };
        match put_multifield_error {
            clips::PutSlotError_PSE_NO_ERROR => Ok(()),
            clips::PutSlotError_PSE_SLOT_NOT_FOUND_ERROR => Err(ClipsError::PutSlotSlotNotFoundError(slot_name.to_owned()).into()),
            clips::PutSlotError_PSE_TYPE_ERROR => Err(ClipsError::PutSlotTypeError(slot_name.to_owned()).into()),
            _ => unreachable!(),
        }
    }

    pub fn assert(self) -> Fact {
        let raw = unsafe { clips::FBAssert(self.raw) };
        Fact::new(raw)
    }
}

impl Drop for FactBuilder {
    fn drop(&mut self) {
        unsafe { clips::FBDispose(self.raw) };
    }
}

#[derive(Debug)]
pub struct Fact {
    raw: *mut clips::Fact,
}

impl Fact {
    fn new(raw: *mut clips::Fact) -> Self {
        Self { raw }
    }
}

impl Drop for Fact {
    fn drop(&mut self) {
        unsafe { clips::Retract(self.raw) };
    }
}

pub struct Type(pub u32);
const CODES: &[(u32, char)] = &[(clips::CLIPSType_BOOLEAN_BIT, 'b'), (clips::CLIPSType_INTEGER_BIT, 'l'), (clips::CLIPSType_FLOAT_BIT, 'd'), (clips::CLIPSType_STRING_BIT, 's'), (clips::CLIPSType_SYMBOL_BIT, 'y'), (clips::CLIPSType_VOID_BIT, 'v'), (clips::CLIPSType_MULTIFIELD_BIT, 'm')];

impl Type {
    pub const BOOLEAN: u32 = clips::CLIPSType_BOOLEAN_BIT;
    pub const SYMBOL: u32 = clips::CLIPSType_SYMBOL_BIT;
    pub const STRING: u32 = clips::CLIPSType_STRING_BIT;
    pub const FLOAT: u32 = clips::CLIPSType_FLOAT_BIT;
    pub const INTEGER: u32 = clips::CLIPSType_INTEGER_BIT;
    pub const VOID: u32 = clips::CLIPSType_VOID_BIT;
    pub const MULTIFIELD: u32 = clips::CLIPSType_MULTIFIELD_BIT;

    fn format(mask: &Type) -> String {
        if mask.0 == 0 {
            return "*".to_string();
        }
        CODES.iter().filter(|(bit, _)| (mask.0 & *bit) != 0).map(|(_, code)| *code).collect()
    }
}

#[derive(Debug)]
pub struct UDFContext {
    raw: *mut clips::UDFContext,
}

impl UDFContext {
    fn new(raw: *mut clips::UDFContext) -> Self {
        Self { raw }
    }

    pub fn get_next_argument(&'_ self, expected_type: Type) -> Option<ClipsValue<'_>> {
        let mut arg = std::mem::MaybeUninit::<clips::UDFValue>::uninit();
        if unsafe { clips::UDFNextArgument(self.raw, expected_type.0, arg.as_mut_ptr()) } { Some(unsafe { arg.assume_init().into() }) } else { None }
    }

    pub fn has_next_argument(&self) -> bool {
        unsafe { !(*self.raw).lastArg.is_null() }
    }
}

#[derive(Debug)]
pub enum ClipsValue<'env> {
    Symbol(Cow<'env, str>),
    String(Cow<'env, str>),
    Float(f64),
    Integer(i64),
    Void(),
    Multifield(Vec<ClipsValue<'env>>),
}

impl<'env> From<clips::clipsValue> for ClipsValue<'env> {
    fn from(value: clips::clipsValue) -> Self {
        match unsafe { (*value.__bindgen_anon_1.header).type_ as u32 } {
            clips::SYMBOL_TYPE => {
                let value = unsafe { CStr::from_ptr((*value.__bindgen_anon_1.lexemeValue).contents) }.to_string_lossy();
                ClipsValue::Symbol(value)
            }
            clips::STRING_TYPE => {
                let value = unsafe { CStr::from_ptr((*value.__bindgen_anon_1.lexemeValue).contents) }.to_string_lossy();
                ClipsValue::String(value)
            }
            clips::FLOAT_TYPE => ClipsValue::Float(unsafe { (*value.__bindgen_anon_1.floatValue).contents }),
            clips::INTEGER_TYPE => ClipsValue::Integer(unsafe { (*value.__bindgen_anon_1.integerValue).contents }),
            clips::VOID_TYPE => ClipsValue::Void(),
            clips::MULTIFIELD_TYPE => ClipsValue::Multifield((0..unsafe { (*value.__bindgen_anon_1.multifieldValue).length }).map(|index| unsafe { *(*value.__bindgen_anon_1.multifieldValue).contents.get_unchecked(index as usize) }.into()).collect::<Vec<_>>()),
            _ => unreachable!(),
        }
    }
}

impl<'env> From<clips::UDFValue> for ClipsValue<'env> {
    fn from(value: clips::UDFValue) -> Self {
        match unsafe { (*value.__bindgen_anon_1.header).type_ as u32 } {
            clips::SYMBOL_TYPE => {
                let value = unsafe { CStr::from_ptr((*value.__bindgen_anon_1.lexemeValue).contents) }.to_string_lossy();
                ClipsValue::Symbol(value)
            }
            clips::STRING_TYPE => {
                let value = unsafe { CStr::from_ptr((*value.__bindgen_anon_1.lexemeValue).contents) }.to_string_lossy();
                ClipsValue::String(value)
            }
            clips::FLOAT_TYPE => ClipsValue::Float(unsafe { (*value.__bindgen_anon_1.floatValue).contents }),
            clips::INTEGER_TYPE => ClipsValue::Integer(unsafe { (*value.__bindgen_anon_1.integerValue).contents }),
            clips::VOID_TYPE => ClipsValue::Void(),
            clips::MULTIFIELD_TYPE => ClipsValue::Multifield((0..unsafe { (*value.__bindgen_anon_1.multifieldValue).length }).map(|index| unsafe { *(*value.__bindgen_anon_1.multifieldValue).contents.get_unchecked(index as usize) }.into()).collect::<Vec<_>>()),
            _ => unreachable!(),
        }
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
        let env = Environment::new().unwrap();
        let result = env.clear();
        assert!(result.is_ok());
    }

    #[test]
    fn test_load_from_string() {
        let env = Environment::new().unwrap();
        let result = env.load_from_str("(deftemplate test_deftemplate)");
        assert!(result.is_ok());
    }

    #[test]
    fn test_load_from_string_error() {
        let env = Environment::new().unwrap();
        let result = env.load_from_str("(deftemplate test_deftemplate");
        assert!(result.is_err());
    }

    #[test]
    #[ignore]
    fn test_load_from_file() {
        let env = Environment::new().unwrap();
        let result = env.load(Path::new("test.clp"));
        assert!(result.is_ok());
    }

    #[test]
    fn test_load_from_file_error() {
        let env = Environment::new().unwrap();
        let result = env.load(Path::new("non_existent_file.clp"));
        assert!(result.is_err());
    }

    #[test]
    fn test_run() {
        let env = Environment::new().unwrap();
        env.load_from_str("(deffacts test_facts (initial-fact))").unwrap();
        let result = env.run(-1);
        assert_eq!(result, 0);
    }

    #[test]
    fn test_fact_builder() {
        let env = Environment::new().unwrap();
        env.load_from_str("(deftemplate test_template (slot test_slot))").unwrap();
        let mut fact_builder = env.fact_builder("test_template");
        let put_result = fact_builder.put_symbol("test_slot", "test_value");
        assert!(put_result.is_ok());
        let fact = fact_builder.assert();
        assert!(fact.raw.is_null() == false);
    }

    #[test]
    fn test_multifield_builder() {
        let env = Environment::new().unwrap();
        let mut multifield_builder = env.multifield_builder(3);
        multifield_builder.put_int(42);
        multifield_builder.put_float(3.14);
        multifield_builder.put_symbol("test_symbol");
        let multifield = multifield_builder.create();
        assert!(multifield.raw.is_null() == false);
    }
}
