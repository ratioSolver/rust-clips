//! # CLIPS - A Safe Rust Wrapper for the CLIPS Expert System
//!
//! This crate provides a safe, idiomatic Rust interface to the [CLIPS](https://clipsrules.net)
//! inference engine. CLIPS (C Language Integrated Production System) is a tool for building
//! expert systems and knowledge-based applications using rule-based reasoning.
//!
//! ## Overview
//!
//! CLIPS is a powerful expert system shell that allows you to:
//! - Define facts and rules using a Lisp-like syntax
//! - Build dynamic knowledge bases
//! - Execute inference engines to draw conclusions
//! - Integrate rule-based reasoning into Rust applications
//!
//! This crate wraps the low-level C API (`clips-sys`) with safe abstractions that handle
//! memory management, string conversions, and error handling automatically.
//!
//! ## Core Components
//!
//! - [`Environment`] - The main interface to a CLIPS inference engine instance
//! - [`FactBuilder`] - Constructs facts (database records) following the builder pattern
//! - [`Fact`] - Represents an asserted fact in the knowledge base
//! - [`MultifieldBuilder`] - Builds ordered collections of values
//! - [`Multifield`] - Represents a collection of values
//! - [`ClipsValue`] - An enum representing different CLIPS value types
//! - [`UDFContext`] - Context for user-defined functions to access arguments
//! - [`Type`] - Type specification for function arguments and return values
//! - [`ClipsError`] - Error types that can occur during operations
//!
//! ## Quick Start
//!
//! ### Creating an Environment
//!
//! ```
//! use clips::Environment;
//!
//! let mut env = Environment::new().unwrap();
//! ```
//!
//! ### Loading CLIPS Code
//!
//! You can load CLIPS constructs (templates, rules, facts) from strings or files:
//!
//! ```
//! # use clips::Environment;
//! # let mut env = Environment::new().unwrap();
//! // Load from a string
//! env.load_from_str("(deftemplate person (slot name) (slot age))").unwrap();
//!
//! // Or load from a file
//! // env.load(std::path::Path::new("knowledge.clp")).unwrap();
//! ```
//!
//! ### Working with Facts
//!
//! Facts are instances of templates. Use the builder pattern to create and assert facts:
//!
//! ```
//! # use clips::Environment;
//! # let mut env = Environment::new().unwrap();
//! # env.load_from_str("(deftemplate person (slot name) (slot age))").unwrap();
//! let fact = env.fact_builder("person").unwrap()
//!     .put_symbol("name", "Alice").unwrap()
//!     .put_int("age", 30).unwrap();
//!
//! env.assert_fact(fact).unwrap();
//! ```
//!
//! ### Running the Inference Engine
//!
//! ```
//! # use clips::Environment;
//! # let mut env = Environment::new().unwrap();
//! # env.load_from_str("(deffacts startup (initial-fact))").unwrap();
//! let rule_count = env.run(-1);  // Run all rules (-1 = unlimited)
//! println!("Fired {} rules", rule_count);
//! ```
//!
//! ### User-Defined Functions (UDFs)
//!
//! Register Rust functions to be callable from CLIPS:
//!
//! ```
//! # use clips::{Environment, Type, ClipsValue};
//! # let mut env = Environment::new().unwrap();
//! env.add_udf(
//!     "double",
//!     Some(Type(Type::INTEGER)),
//!     1,
//!     1,
//!     vec![Type(Type::INTEGER)],
//!     |_env, ctx| {
//!         if let Some(ClipsValue::Integer(n)) = ctx.get_next_argument(Type(Type::INTEGER)) {
//!             ClipsValue::Integer(n * 2)
//!         } else {
//!             ClipsValue::Void()
//!         }
//!     },
//! ).unwrap();
//!
//! env.load_from_str("(defrule test_rule => (printout t (double 21)))").unwrap();
//! ```
//!
//! ## Builder Pattern
//!
//! This crate uses the builder pattern extensively for ergonomic construction of complex objects:
//!
//! - **`FactBuilder`**: Chain method calls to set multiple slot values before asserting
//! - **`MultifieldBuilder`**: Chain method calls to add elements to a multifield collection
//!
//! Each builder method returns `self`, allowing you to chain calls:
//!
//! ```
//! # use clips::Environment;
//! # let mut env = Environment::new().unwrap();
//! # env.load_from_str("(deftemplate test_deftemplate (slot a) (slot b) (slot c))").unwrap();
//! let fact = env.fact_builder("test_deftemplate").unwrap()
//!     .put_int("a", 1).unwrap()
//!     .put_symbol("b", "x").unwrap()
//!     .put_float("c", 3.14).unwrap();
//! env.assert_fact(fact).unwrap();
//! ```
//!
//! ## Modifying Facts
//!
//! Use `FactModifier` to change slot values of an existing fact:
//!
//! ```
//! # use clips::Environment;
//! # let mut env = Environment::new().unwrap();
//! # env.load_from_str("(deftemplate test_deftemplate (slot a) (slot b))").unwrap();
//! # let builder = env.fact_builder("test_deftemplate").unwrap()
//! #     .put_int("a", 1).unwrap()
//! #     .put_symbol("b", "x").unwrap();
//! # let fact = env.assert_fact(builder).unwrap();
//! let modifier = env.fact_modifier(&fact).unwrap()
//!    .put_int("a", 42).unwrap()
//!    .put_symbol("b", "y").unwrap();
//! env.modify_fact(modifier).unwrap();
//! ```
//!
//! ## Value Types
//!
//! CLIPS supports several primitive types:
//!
//! - **Symbol**: Unquoted atoms (e.g., `red`, `john`)
//! - **String**: Quoted text (e.g., `"hello world"`)
//! - **Integer**: Whole numbers
//! - **Float**: Decimal numbers
//! - **Multifield**: Ordered collections of values
//! - **Void**: No return value or empty result
//!
//! The [`ClipsValue`] enum in Rust mirrors these types.
//!
//! ## Memory Management
//!
//! This crate handles memory management automatically:
//!
//! - **`Environment`**: Calls `DestroyEnvironment` in its `Drop` implementation
//! - **`Fact`**: Automatically retracts itself when dropped (via `Retract`)
//! - **Builders**: Dispose of resources when dropped
//!
//! This ensures no memory leaks when values go out of scope.
//!
//! ## Error Handling
//!
//! Most operations return `Result<T, ClipsError>`. Use standard Rust error handling:
//!
//! ```
//! # use clips::Environment;
//! # let mut env = Environment::new().unwrap();
//! match env.load_from_str("(deftemplate foo (slot x))") {
//!     Ok(_) => println!("Template loaded"),
//!     Err(e) => eprintln!("Error: {}", e),
//! }
//! ```
//!
//! ## Thread Safety
//!
//! **Important**: CLIPS is not thread-safe by default. Each CLIPS environment should be
//! used by a single thread. If you need CLIPS in a multi-threaded application:
//!
//! - Create separate `Environment` instances for each thread
//! - Use synchronization primitives (mutexes, channels) to coordinate access
//! - Do not share `Environment` pointers between threads across thread boundaries
//!
//! ## Limitations and Considerations
//!
//! - String operations use UTF-8 encoding; non-UTF-8 strings may cause panics
//! - CLIPS syntax is case-insensitive in most contexts
//! - Template and function names must be valid CLIPS identifiers
//! - Type checking for UDFs happens at the CLIPS level; ensure your Rust code
//!   handles all specified argument types correctly
//!
//! ## Working with Multifields
//!
//! Multifields are collections that can hold mixed types:
//!
//! ```
//! # use clips::Environment;
//! # let mut env = Environment::new().unwrap();
//! let mf = env.multifield_builder(3).unwrap()
//!     .put_int(42)
//!     .put_symbol("test")
//!     .put_float(3.14)
//!     .create();
//!
//! println!("Multifield length: {}", mf.len());
//! ```
//!
//! ## Examples
//!
//! ### Example: A Simple Expert System
//!
//! ```no_run
//! use clips::Environment;
//!
//! fn main() -> Result<(), clips::ClipsError> {
//!     let mut env = Environment::new()?;
//!
//!     // Define a template for animals
//!     env.load_from_str(
//!         "(deftemplate animal (slot species) (slot legs) (slot flies))"
//!     )?;
//!
//!     // Define rules for classification
//!     env.load_from_str(
//!         "(defrule classify-bird
//!             (animal (species ?name) (legs 2) (flies yes))
//!             =>
//!             (printout t ?name \" is a bird\" crlf))"
//!     )?;
//!
//!     // Add some facts
//!     env.assert_fact(
//!         env.fact_builder("animal")?
//!             .put_symbol("species", "sparrow")?
//!             .put_int("legs", 2)?
//!             .put_symbol("flies", "yes")?
//!     )?;
//!
//!     // Run the inference engine
//!     env.run(-1);
//!
//!     Ok(())
//! }
//! ```

use clips_sys::clips;
use std::{
    ffi::{CStr, CString},
    fmt::Display,
    path::Path,
};

/// Errors that can occur when using the CLIPS environment.
#[derive(Debug)]
pub enum ClipsError {
    /// Failed to create a new CLIPS environment.
    CreateEnvironmentError,
    /// Failed to clear the environment.
    ClearError,
    /// Failed to load constructs from a string.
    LoadFromStringError(String),
    /// Failed to build a construct (contains the construct string).
    BuildParsingError(String),
    /// Failed to open a file during load (contains the file path).
    LoadOpenFileError(String),
    /// Failed to parse a file or string during load (contains the source).
    LoadParsingError(String),
    /// Deftemplate not found when creating a fact builder (contains the template name).
    DeftemplateNotFoundError(String),
    /// A slot was not found in a fact template (contains the slot name).
    PutSlotSlotNotFoundError(String),
    /// Type mismatch when setting a slot value (contains the slot name).
    PutSlotTypeError(String),
    /// Failed to create a multifield builder.
    MultifieldBuilderError(String),
    /// Failed to assert a fact built with the fact builder.
    AssertFactError,
    /// Minimum number of arguments exceeds maximum for a UDF (contains the function name).
    AddUDFMinExceedsMaxError(String),
    /// Function name is already in use (contains the function name).
    AddUDFFunctionNameInUseError(String),
    /// Invalid argument type for a UDF (contains the function name).
    AddUDFInvalidArgumentTypeError(String),
    /// Invalid return type for a UDF (contains the function name).
    AddUDFInvalidReturnTypeError(String),
}

impl Display for ClipsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            ClipsError::CreateEnvironmentError => write!(f, "Failed to create environment"),
            ClipsError::ClearError => write!(f, "Failed to clear environment"),
            ClipsError::LoadFromStringError(s) => write!(f, "Failed to load from string: {s}"),
            ClipsError::BuildParsingError(s) => write!(f, "Failed to build construct: {s}"),
            ClipsError::LoadOpenFileError(s) => write!(f, "Failed to open file: {s}"),
            ClipsError::LoadParsingError(s) => write!(f, "Failed to parse file: {s}"),
            ClipsError::DeftemplateNotFoundError(s) => write!(f, "Deftemplate not found: {s}"),
            ClipsError::PutSlotSlotNotFoundError(s) => write!(f, "Slot not found: {s}"),
            ClipsError::PutSlotTypeError(s) => write!(f, "Type error for slot: {s}"),
            ClipsError::MultifieldBuilderError(s) => write!(f, "Failed to create multifield builder: {s}"),
            ClipsError::AssertFactError => write!(f, "Failed to assert fact"),
            ClipsError::AddUDFMinExceedsMaxError(s) => write!(f, "Minimum number of arguments exceeds maximum for UDF '{s}'"),
            ClipsError::AddUDFFunctionNameInUseError(s) => write!(f, "Function name '{s}' is already in use for UDF"),
            ClipsError::AddUDFInvalidArgumentTypeError(s) => write!(f, "Invalid argument type for UDF '{s}'"),
            ClipsError::AddUDFInvalidReturnTypeError(s) => write!(f, "Invalid return type for UDF '{s}'"),
        }
    }
}

/// A CLIPS rule engine environment.
///
/// The `Environment` is the main interface to the CLIPS inference engine.
/// It manages facts, rules, templates, and user-defined functions.
///
/// # Examples
///
/// ```
/// use clips::Environment;
///
/// let mut env = Environment::new().unwrap();
/// env.load_from_str("(deftemplate person (slot name))").unwrap();
/// ```
#[derive(Debug)]
pub struct Environment {
    raw: *mut clips::Environment,
}

impl Environment {
    /// Creates a new CLIPS environment.
    ///
    /// # Errors
    ///
    /// Returns `ClipsError::CreateEnvironmentError` if the environment cannot be created.
    pub fn new() -> Result<Self, ClipsError> {
        let raw = unsafe { clips::CreateEnvironment() };
        if raw.is_null() { Err(ClipsError::CreateEnvironmentError) } else { Ok(Self { raw }) }
    }

    /// Clears all constructs (facts, rules, templates) from the environment.
    ///
    /// # Errors
    ///
    /// Returns `ClipsError::ClearError` if the clear operation fails.
    pub fn clear(&mut self) -> Result<(), ClipsError> {
        if unsafe { clips::Clear(self.raw) } { Ok(()) } else { Err(ClipsError::ClearError) }
    }

    /// Loads CLIPS constructs from a string.
    ///
    /// # Arguments
    ///
    /// * `string` - A CLIPS language string containing deftemplate, defrule, or other constructs
    ///
    /// # Errors
    ///
    /// Returns `ClipsError::LoadFromStringError` if parsing fails.
    pub fn load_from_str(&mut self, string: &str) -> Result<(), ClipsError> {
        if unsafe { clips::LoadFromString(self.raw, string.as_ptr() as *const i8, string.len()) } { Ok(()) } else { Err(ClipsError::LoadFromStringError(string.to_owned()).into()) }
    }

    /// Loads CLIPS constructs from a file.
    ///
    /// # Arguments
    ///
    /// * `path` - Path to the CLIPS file
    ///
    /// # Errors
    ///
    /// Returns `ClipsError::LoadOpenFileError` if the file cannot be opened,
    /// or `ClipsError::LoadParsingError` if parsing fails.
    pub fn load(&mut self, path: &Path) -> Result<(), ClipsError> {
        let path_str = CString::new(path.to_str().unwrap()).unwrap();
        let load_error = unsafe { clips::Load(self.raw, path_str.as_ptr() as *const i8) };

        match load_error {
            clips::LoadError_LE_NO_ERROR => Ok(()),
            clips::LoadError_LE_OPEN_FILE_ERROR => Err(ClipsError::LoadOpenFileError(path.to_str().unwrap().to_owned()).into()),
            clips::LoadError_LE_PARSING_ERROR => Err(ClipsError::LoadParsingError(path.to_str().unwrap().to_owned()).into()),
            _ => unreachable!(),
        }
    }

    /// Builds a single construct from a string.
    ///
    /// Similar to `load_from_str`, but for a single construct.
    ///
    /// # Arguments
    ///
    /// * `construct` - A CLIPS construct string (e.g., "(deftemplate foo (slot x))")
    ///
    /// # Errors
    ///
    /// Returns `ClipsError::LoadParsingError` if the construct is invalid.
    pub fn build(&mut self, construct: &str) -> Result<(), ClipsError> {
        let construct_cstr = CString::new(construct).unwrap();
        let build_error = unsafe { clips::Build(self.raw, construct_cstr.as_ptr() as *const i8) };
        match build_error {
            clips::BuildError_BE_NO_ERROR => Ok(()),
            clips::BuildError_BE_PARSING_ERROR => Err(ClipsError::LoadParsingError(construct.to_owned()).into()),
            _ => unreachable!(),
        }
    }

    /// Resets the environment to its initial state.
    ///
    /// This executes deffacts and initial-fact, preparing the engine for rule execution.
    pub fn reset(&mut self) {
        unsafe { clips::Reset(self.raw) };
    }

    /// Runs the inference engine until no more rules fire or the limit is reached.
    ///
    /// # Arguments
    ///
    /// * `limit` - Maximum number of rule firings. Use -1 for no limit.
    ///
    /// # Returns
    ///
    /// The number of rules that fired.
    pub fn run(&mut self, limit: i64) -> i64 {
        unsafe { clips::Run(self.raw, limit) }
    }

    /// Creates a fact builder for the given template.
    ///
    /// # Arguments
    ///
    /// * `template_name` - The name of the fact template
    ///
    /// # Returns
    ///
    /// A builder that can be used to set slot values and assert the fact.
    ///
    /// # Example
    ///
    /// ```
    /// # use clips::Environment;
    /// # let mut env = Environment::new().unwrap();
    /// # env.load_from_str("(deftemplate person (slot name) (slot age))").unwrap();
    /// let fact = env.fact_builder("person").unwrap()
    ///     .put_symbol("name", "John").unwrap()
    ///     .put_int("age", 30).unwrap();
    /// let fact = env.assert_fact(fact).unwrap();
    /// ```
    pub fn fact_builder(&self, template_name: &str) -> Result<FactBuilder, ClipsError> {
        let template_name_cstr = CString::new(template_name).unwrap();
        let raw = unsafe { clips::CreateFactBuilder(self.raw, template_name_cstr.as_ptr() as *const i8) };
        if raw.is_null() { Err(ClipsError::DeftemplateNotFoundError(template_name.to_owned()).into()) } else { Ok(FactBuilder::new(raw)) }
    }

    /// Creates a fact modifier for an existing fact.
    ///
    /// # Arguments
    ///
    /// * `fact` - The fact to modify
    ///
    /// # Returns
    ///
    /// A builder that can be used to set new slot values and modify the fact.
    ///
    /// # Example
    ///
    /// ```
    /// # use clips::Environment;
    /// # let mut env = Environment::new().unwrap();
    /// # env.load_from_str("(deftemplate person (slot name) (slot age))").unwrap();
    /// # let builder = env.fact_builder("person").unwrap()
    /// #     .put_symbol("name", "John").unwrap()
    /// #     .put_int("age", 30).unwrap();
    /// # let fact = env.assert_fact(builder).unwrap();
    /// let modifier = env.fact_modifier(&fact).unwrap()
    ///     .put_int("age", 31).unwrap();
    /// env.modify_fact(modifier).unwrap();
    /// ```
    pub fn fact_modifier(&self, fact: &Fact) -> Result<FactModifier, ClipsError> {
        let raw = unsafe { clips::CreateFactModifier(self.raw, fact.raw) };
        if raw.is_null() { Err(ClipsError::DeftemplateNotFoundError("fact".to_string()).into()) } else { Ok(FactModifier::new(raw)) }
    }

    /// Creates a multifield builder.
    ///
    /// # Arguments
    ///
    /// * `size` - Initial capacity of the multifield
    ///
    /// # Returns
    ///
    /// A builder that can be used to populate multiple values.
    pub fn multifield_builder(&self, size: usize) -> Result<MultifieldBuilder, ClipsError> {
        let raw = unsafe { clips::CreateMultifieldBuilder(self.raw, size) };
        if raw.is_null() { Err(ClipsError::MultifieldBuilderError(format!("Failed to create multifield builder with size {size}")).into()) } else { Ok(MultifieldBuilder::new(raw)) }
    }

    /// Asserts a fact built with `fact_builder`.
    ///
    /// # Arguments
    ///
    /// * `builder` - The completed fact builder
    ///
    /// # Returns
    ///
    /// Some(fact) if assertion succeeds, None if it fails.
    pub fn assert_fact(&mut self, builder: FactBuilder) -> Result<Fact, ClipsError> {
        let raw = unsafe { clips::FBAssert(builder.raw) };
        if raw.is_null() { Err(ClipsError::AssertFactError.into()) } else { Ok(Fact::new(self.raw, raw)) }
    }

    /// Modifies a fact using a fact modifier built with `fact_modifier`.
    ///
    /// # Arguments
    ///
    /// * `modifier` - The completed fact modifier
    ///
    /// # Returns
    ///
    /// Some(fact) if modification succeeds, None if it fails.
    pub fn modify_fact(&mut self, modifier: FactModifier) -> Result<(), ClipsError> {
        let raw = unsafe { clips::FMModify(modifier.raw) };
        if raw.is_null() { Err(ClipsError::AssertFactError.into()) } else { Ok(()) }
    }

    /// Registers a user-defined function (UDF) in the environment.
    ///
    /// # Arguments
    ///
    /// * `name` - Function name as callable from CLIPS
    /// * `return_types` - Expected return type(s), or None for any type
    /// * `min_args` - Minimum number of arguments
    /// * `max_args` - Maximum number of arguments
    /// * `arg_types` - Vector of expected argument types
    /// * `function` - Rust closure implementing the function
    ///
    /// # Errors
    ///
    /// Returns various `ClipsError` variants if the UDF registration fails.
    ///
    /// # Example
    ///
    /// ```
    /// # use clips::{Environment, Type, ClipsValue};
    /// # let mut env = Environment::new().unwrap();
    /// env.add_udf(
    ///     "double",
    ///     Some(Type(Type::INTEGER)),
    ///     1,
    ///     1,
    ///     vec![Type(Type::INTEGER)],
    ///     |_env, ctx| {
    ///         if let Some(ClipsValue::Integer(n)) = ctx.get_next_argument(Type(Type::INTEGER)) {
    ///             ClipsValue::Integer(n * 2)
    ///         } else {
    ///             ClipsValue::Void()
    ///         }
    ///     },
    /// ).unwrap();
    /// ```
    pub fn add_udf<F>(&mut self, name: &str, return_types: Option<Type>, min_args: u16, max_args: u16, arg_types: Vec<Type>, function: F) -> Result<(), ClipsError>
    where
        F: FnMut(&mut Self, &mut UDFContext) -> ClipsValue + 'static,
    {
        let name_cstr = CString::new(name).unwrap();
        let return_types_cstr = CString::new(return_types.map_or("v".to_string(), |t| Type::format(&t))).unwrap();
        let arg_types_cstr = CString::new(if arg_types.is_empty() { "*".to_string() } else { ";".to_string() + &arg_types.iter().map(|t| Type::format(t)).collect::<Vec<_>>().join(";") }).unwrap();

        let boxed_f: Box<dyn FnMut(&mut Self, &mut UDFContext) -> ClipsValue> = Box::new(function);
        let user_data = Box::into_raw(Box::new(boxed_f)) as *mut std::ffi::c_void;

        let err = unsafe { clips::AddUDF(self.raw, name_cstr.as_ptr(), return_types_cstr.as_ptr(), min_args, max_args, arg_types_cstr.as_ptr(), Some(trampoline), name_cstr.as_ptr(), user_data) };
        match err {
            clips::AddUDFError_AUE_NO_ERROR => Ok(()),
            clips::AddUDFError_AUE_MIN_EXCEEDS_MAX_ERROR => Err(ClipsError::AddUDFMinExceedsMaxError(name.to_owned())),
            clips::AddUDFError_AUE_FUNCTION_NAME_IN_USE_ERROR => Err(ClipsError::AddUDFFunctionNameInUseError(name.to_owned())),
            clips::AddUDFError_AUE_INVALID_ARGUMENT_TYPE_ERROR => Err(ClipsError::AddUDFInvalidArgumentTypeError(name.to_owned())),
            clips::AddUDFError_AUE_INVALID_RETURN_TYPE_ERROR => Err(ClipsError::AddUDFInvalidReturnTypeError(name.to_owned())),
            _ => unreachable!(),
        }
    }
}

impl Drop for Environment {
    fn drop(&mut self) {
        unsafe { clips::DestroyEnvironment(self.raw) };
    }
}

/// A multifield value in CLIPS.
///
/// Multifields are ordered collections of values of potentially different types.
#[derive(Debug)]
pub struct Multifield {
    raw: *mut clips::Multifield,
}

impl Multifield {
    fn new(raw: *mut clips::Multifield) -> Self {
        Self { raw }
    }

    /// Returns the number of elements in the multifield.
    pub fn len(&self) -> usize {
        unsafe { (*self.raw).length as usize }
    }
}

/// Builder for constructing multifield values.
///
/// This builder allows you to populate a multifield with values of various types.
/// It uses method chaining for ergonomic construction.
#[derive(Debug)]
pub struct MultifieldBuilder {
    raw: *mut clips::MultifieldBuilder,
}

impl MultifieldBuilder {
    fn new(raw: *mut clips::MultifieldBuilder) -> Self {
        Self { raw }
    }

    /// Appends an integer value to the multifield.
    pub fn put_int(self, value: i64) -> Self {
        unsafe { clips::MBAppendInteger(self.raw, value) };
        self
    }

    /// Appends a float value to the multifield.
    pub fn put_float(self, value: f64) -> Self {
        unsafe { clips::MBAppendFloat(self.raw, value) };
        self
    }

    /// Appends a symbol (unquoted string) to the multifield.
    pub fn put_symbol(self, value: &str) -> Self {
        let value_cstr = CString::new(value).unwrap();
        unsafe { clips::MBAppendSymbol(self.raw, value_cstr.as_ptr() as *const i8) };
        self
    }

    /// Appends a string (quoted) value to the multifield.
    pub fn put_string(self, value: &str) -> Self {
        let value_cstr = CString::new(value).unwrap();
        unsafe { clips::MBAppendString(self.raw, value_cstr.as_ptr() as *const i8) };
        self
    }

    /// Appends a multifield to this multifield.
    pub fn put_multifield(self, value: Multifield) -> Self {
        unsafe { clips::MBAppendMultifield(self.raw, value.raw) };
        self
    }

    /// Finalizes the multifield and returns the result.
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

/// Builder for constructing facts.
///
/// A fact is an instance of a template with specific slot values.
/// This builder allows you to specify all slot values before asserting the fact.
/// It uses method chaining and supports error handling for type mismatches.
#[derive(Debug)]
pub struct FactBuilder {
    raw: *mut clips::FactBuilder,
}

impl FactBuilder {
    fn new(raw: *mut clips::FactBuilder) -> Self {
        Self { raw }
    }

    /// Sets an integer slot value.
    ///
    /// # Errors
    ///
    /// Returns an error if the slot doesn't exist or the type is mismatched.
    pub fn put_int(self, slot_name: &str, value: i64) -> Result<Self, ClipsError> {
        let slot_name_cstr = CString::new(slot_name).unwrap();
        let put_int_error = unsafe { clips::FBPutSlotInteger(self.raw, slot_name_cstr.as_ptr() as *const i8, value) };
        match put_int_error {
            clips::PutSlotError_PSE_NO_ERROR => Ok(self),
            clips::PutSlotError_PSE_SLOT_NOT_FOUND_ERROR => Err(ClipsError::PutSlotSlotNotFoundError(slot_name.to_owned()).into()),
            clips::PutSlotError_PSE_TYPE_ERROR => Err(ClipsError::PutSlotTypeError(slot_name.to_owned()).into()),
            _ => unreachable!(),
        }
    }

    /// Sets a float slot value.
    ///
    /// # Errors
    ///
    /// Returns an error if the slot doesn't exist or the type is mismatched.
    pub fn put_float(self, slot_name: &str, value: f64) -> Result<Self, ClipsError> {
        let slot_name_cstr = CString::new(slot_name).unwrap();
        let put_float_error = unsafe { clips::FBPutSlotFloat(self.raw, slot_name_cstr.as_ptr() as *const i8, value) };
        match put_float_error {
            clips::PutSlotError_PSE_NO_ERROR => Ok(self),
            clips::PutSlotError_PSE_SLOT_NOT_FOUND_ERROR => Err(ClipsError::PutSlotSlotNotFoundError(slot_name.to_owned()).into()),
            clips::PutSlotError_PSE_TYPE_ERROR => Err(ClipsError::PutSlotTypeError(slot_name.to_owned()).into()),
            _ => unreachable!(),
        }
    }

    /// Sets a symbol (unquoted string) slot value.
    ///
    /// # Errors
    ///
    /// Returns an error if the slot doesn't exist or the type is mismatched.
    pub fn put_symbol(self, slot_name: &str, value: &str) -> Result<Self, ClipsError> {
        let slot_name_cstr = CString::new(slot_name).unwrap();
        let value_cstr = CString::new(value).unwrap();
        let put_symbol_error = unsafe { clips::FBPutSlotSymbol(self.raw, slot_name_cstr.as_ptr() as *const i8, value_cstr.as_ptr() as *const i8) };
        match put_symbol_error {
            clips::PutSlotError_PSE_NO_ERROR => Ok(self),
            clips::PutSlotError_PSE_SLOT_NOT_FOUND_ERROR => Err(ClipsError::PutSlotSlotNotFoundError(slot_name.to_owned()).into()),
            clips::PutSlotError_PSE_TYPE_ERROR => Err(ClipsError::PutSlotTypeError(slot_name.to_owned()).into()),
            _ => unreachable!(),
        }
    }

    /// Sets a string (quoted) slot value.
    ///
    /// # Errors
    ///
    /// Returns an error if the slot doesn't exist or the type is mismatched.
    pub fn put_string(self, slot_name: &str, value: &str) -> Result<Self, ClipsError> {
        let slot_name_cstr = CString::new(slot_name).unwrap();
        let value_cstr = CString::new(value).unwrap();
        let put_string_error = unsafe { clips::FBPutSlotString(self.raw, slot_name_cstr.as_ptr() as *const i8, value_cstr.as_ptr() as *const i8) };
        match put_string_error {
            clips::PutSlotError_PSE_NO_ERROR => Ok(self),
            clips::PutSlotError_PSE_SLOT_NOT_FOUND_ERROR => Err(ClipsError::PutSlotSlotNotFoundError(slot_name.to_owned()).into()),
            clips::PutSlotError_PSE_TYPE_ERROR => Err(ClipsError::PutSlotTypeError(slot_name.to_owned()).into()),
            _ => unreachable!(),
        }
    }

    /// Sets a multifield slot value.
    ///
    /// # Errors
    ///
    /// Returns an error if the slot doesn't exist or the type is mismatched.
    pub fn put_multifield(self, slot_name: &str, value: Multifield) -> Result<Self, ClipsError> {
        let slot_name_cstr = CString::new(slot_name).unwrap();
        let put_multifield_error = unsafe { clips::FBPutSlotMultifield(self.raw, slot_name_cstr.as_ptr() as *const i8, value.raw) };
        match put_multifield_error {
            clips::PutSlotError_PSE_NO_ERROR => Ok(self),
            clips::PutSlotError_PSE_SLOT_NOT_FOUND_ERROR => Err(ClipsError::PutSlotSlotNotFoundError(slot_name.to_owned()).into()),
            clips::PutSlotError_PSE_TYPE_ERROR => Err(ClipsError::PutSlotTypeError(slot_name.to_owned()).into()),
            _ => unreachable!(),
        }
    }
}

impl Drop for FactBuilder {
    fn drop(&mut self) {
        unsafe { clips::FBDispose(self.raw) };
    }
}

/// Modifier for modifying facts.
///
/// A fact is an instance of a template with specific slot values.
/// This builder allows you to specify all slot values before modifying the fact.
/// It uses method chaining and supports error handling for type mismatches.
#[derive(Debug)]
pub struct FactModifier {
    raw: *mut clips::FactModifier,
}

impl FactModifier {
    fn new(raw: *mut clips::FactModifier) -> Self {
        Self { raw }
    }

    /// Sets an integer slot value.
    ///
    /// # Errors
    ///
    /// Returns an error if the slot doesn't exist or the type is mismatched.
    pub fn put_int(self, slot_name: &str, value: i64) -> Result<Self, ClipsError> {
        let slot_name_cstr = CString::new(slot_name).unwrap();
        let put_int_error = unsafe { clips::FMPutSlotInteger(self.raw, slot_name_cstr.as_ptr() as *const i8, value) };
        match put_int_error {
            clips::PutSlotError_PSE_NO_ERROR => Ok(self),
            clips::PutSlotError_PSE_SLOT_NOT_FOUND_ERROR => Err(ClipsError::PutSlotSlotNotFoundError(slot_name.to_owned()).into()),
            clips::PutSlotError_PSE_TYPE_ERROR => Err(ClipsError::PutSlotTypeError(slot_name.to_owned()).into()),
            _ => unreachable!(),
        }
    }

    /// Sets a float slot value.
    ///
    /// # Errors
    ///
    /// Returns an error if the slot doesn't exist or the type is mismatched.
    pub fn put_float(self, slot_name: &str, value: f64) -> Result<Self, ClipsError> {
        let slot_name_cstr = CString::new(slot_name).unwrap();
        let put_float_error = unsafe { clips::FMPutSlotFloat(self.raw, slot_name_cstr.as_ptr() as *const i8, value) };
        match put_float_error {
            clips::PutSlotError_PSE_NO_ERROR => Ok(self),
            clips::PutSlotError_PSE_SLOT_NOT_FOUND_ERROR => Err(ClipsError::PutSlotSlotNotFoundError(slot_name.to_owned()).into()),
            clips::PutSlotError_PSE_TYPE_ERROR => Err(ClipsError::PutSlotTypeError(slot_name.to_owned()).into()),
            _ => unreachable!(),
        }
    }

    /// Sets a symbol (unquoted string) slot value.
    ///
    /// # Errors
    ///
    /// Returns an error if the slot doesn't exist or the type is mismatched.
    pub fn put_symbol(self, slot_name: &str, value: &str) -> Result<Self, ClipsError> {
        let slot_name_cstr = CString::new(slot_name).unwrap();
        let value_cstr = CString::new(value).unwrap();
        let put_symbol_error = unsafe { clips::FMPutSlotSymbol(self.raw, slot_name_cstr.as_ptr() as *const i8, value_cstr.as_ptr() as *const i8) };
        match put_symbol_error {
            clips::PutSlotError_PSE_NO_ERROR => Ok(self),
            clips::PutSlotError_PSE_SLOT_NOT_FOUND_ERROR => Err(ClipsError::PutSlotSlotNotFoundError(slot_name.to_owned()).into()),
            clips::PutSlotError_PSE_TYPE_ERROR => Err(ClipsError::PutSlotTypeError(slot_name.to_owned()).into()),
            _ => unreachable!(),
        }
    }

    /// Sets a string (quoted) slot value.
    ///
    /// # Errors
    ///
    /// Returns an error if the slot doesn't exist or the type is mismatched.
    pub fn put_string(self, slot_name: &str, value: &str) -> Result<Self, ClipsError> {
        let slot_name_cstr = CString::new(slot_name).unwrap();
        let value_cstr = CString::new(value).unwrap();
        let put_string_error = unsafe { clips::FMPutSlotString(self.raw, slot_name_cstr.as_ptr() as *const i8, value_cstr.as_ptr() as *const i8) };
        match put_string_error {
            clips::PutSlotError_PSE_NO_ERROR => Ok(self),
            clips::PutSlotError_PSE_SLOT_NOT_FOUND_ERROR => Err(ClipsError::PutSlotSlotNotFoundError(slot_name.to_owned()).into()),
            clips::PutSlotError_PSE_TYPE_ERROR => Err(ClipsError::PutSlotTypeError(slot_name.to_owned()).into()),
            _ => unreachable!(),
        }
    }

    /// Sets a multifield slot value.
    ///
    /// # Errors
    ///
    /// Returns an error if the slot doesn't exist or the type is mismatched.
    pub fn put_multifield(self, slot_name: &str, value: Multifield) -> Result<Self, ClipsError> {
        let slot_name_cstr = CString::new(slot_name).unwrap();
        let put_multifield_error = unsafe { clips::FMPutSlotMultifield(self.raw, slot_name_cstr.as_ptr() as *const i8, value.raw) };
        match put_multifield_error {
            clips::PutSlotError_PSE_NO_ERROR => Ok(self),
            clips::PutSlotError_PSE_SLOT_NOT_FOUND_ERROR => Err(ClipsError::PutSlotSlotNotFoundError(slot_name.to_owned()).into()),
            clips::PutSlotError_PSE_TYPE_ERROR => Err(ClipsError::PutSlotTypeError(slot_name.to_owned()).into()),
            _ => unreachable!(),
        }
    }
}

impl Drop for FactModifier {
    fn drop(&mut self) {
        unsafe { clips::FMDispose(self.raw) };
    }
}

/// A fact in the CLIPS knowledge base.
///
/// A fact is an instance of a template with specific slot values.
/// Facts are automatically retracted when dropped.
#[derive(Debug)]
pub struct Fact {
    env: *mut clips::Environment,
    raw: *mut clips::Fact,
}

impl Fact {
    fn new(env: *mut clips::Environment, raw: *mut clips::Fact) -> Self {
        Self { env, raw }
    }
}

impl Drop for Fact {
    fn drop(&mut self) {
        unsafe { clips::Retract(self.raw) };
    }
}

impl Display for Fact {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        unsafe {
            let sb = clips::CreateStringBuilder(self.env, 128);
            clips::FactPPForm(self.raw, sb, false);
            let res = write!(f, "{}", CStr::from_ptr((*sb).contents).to_string_lossy());
            clips::SBDispose(sb);
            res
        }
    }
}

/// A CLIPS value type specification.
///
/// Used to specify expected argument and return types for user-defined functions.
/// Types can be combined using bitwise OR to specify multiple acceptable types.
pub struct Type(pub u32);
const CODES: &[(u32, char)] = &[(clips::CLIPSType_BOOLEAN_BIT, 'b'), (clips::CLIPSType_INTEGER_BIT, 'l'), (clips::CLIPSType_FLOAT_BIT, 'd'), (clips::CLIPSType_STRING_BIT, 's'), (clips::CLIPSType_SYMBOL_BIT, 'y'), (clips::CLIPSType_VOID_BIT, 'v'), (clips::CLIPSType_MULTIFIELD_BIT, 'm')];

impl Type {
    /// Boolean type
    pub const BOOLEAN: u32 = clips::CLIPSType_BOOLEAN_BIT;
    /// Symbol (unquoted atom) type
    pub const SYMBOL: u32 = clips::CLIPSType_SYMBOL_BIT;
    /// String (quoted) type
    pub const STRING: u32 = clips::CLIPSType_STRING_BIT;
    /// Float type
    pub const FLOAT: u32 = clips::CLIPSType_FLOAT_BIT;
    /// Integer type
    pub const INTEGER: u32 = clips::CLIPSType_INTEGER_BIT;
    /// Void (no return value) type
    pub const VOID: u32 = clips::CLIPSType_VOID_BIT;
    /// Multifield (collection) type
    pub const MULTIFIELD: u32 = clips::CLIPSType_MULTIFIELD_BIT;

    fn format(mask: &Type) -> String {
        if mask.0 == 0 {
            return "*".to_string();
        }
        CODES.iter().filter(|(bit, _)| (mask.0 & *bit) != 0).map(|(_, code)| *code).collect()
    }
}

/// Context for a user-defined function call.
///
/// Provides access to arguments passed to a UDF from CLIPS.
#[derive(Debug)]
pub struct UDFContext {
    raw: *mut clips::UDFContext,
}

impl UDFContext {
    fn new(raw: *mut clips::UDFContext) -> Self {
        Self { raw }
    }

    /// Retrieves the next argument from the UDF call.
    ///
    /// # Arguments
    ///
    /// * `expected_type` - The expected type of the argument
    ///
    /// # Returns
    ///
    /// Some(value) if an argument is available and matches the expected type, None otherwise.
    pub fn get_next_argument(&self, expected_type: Type) -> Option<ClipsValue> {
        let mut arg = std::mem::MaybeUninit::<clips::UDFValue>::uninit();
        if unsafe { clips::UDFNextArgument(self.raw, expected_type.0, arg.as_mut_ptr()) } { Some(unsafe { arg.assume_init().into() }) } else { None }
    }

    /// Checks if there are more arguments to retrieve.
    pub fn has_next_argument(&self) -> bool {
        unsafe { !(*self.raw).lastArg.is_null() }
    }
}

/// A value that can be used in CLIPS.
///
/// Represents the different types of values that CLIPS can work with,
/// returned from UDFs or retrieved from the environment.
#[derive(Debug)]
pub enum ClipsValue {
    /// An unquoted atom
    Symbol(String),
    /// A quoted string
    String(String),
    /// A floating-point number
    Float(f64),
    /// An integer
    Integer(i64),
    /// Void (no return value)
    Void(),
    /// An ordered collection of values
    Multifield(Vec<ClipsValue>),
}

impl From<clips::clipsValue> for ClipsValue {
    fn from(value: clips::clipsValue) -> Self {
        match unsafe { (*value.__bindgen_anon_1.header).type_ as u32 } {
            clips::SYMBOL_TYPE => {
                let value = unsafe { CStr::from_ptr((*value.__bindgen_anon_1.lexemeValue).contents) }.to_string_lossy().into_owned();
                ClipsValue::Symbol(value)
            }
            clips::STRING_TYPE => {
                let value = unsafe { CStr::from_ptr((*value.__bindgen_anon_1.lexemeValue).contents) }.to_string_lossy().into_owned();
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

impl From<clips::UDFValue> for ClipsValue {
    fn from(value: clips::UDFValue) -> Self {
        match unsafe { (*value.__bindgen_anon_1.header).type_ as u32 } {
            clips::SYMBOL_TYPE => {
                let value = unsafe { CStr::from_ptr((*value.__bindgen_anon_1.lexemeValue).contents) }.to_string_lossy().into_owned();
                ClipsValue::Symbol(value)
            }
            clips::STRING_TYPE => {
                let value = unsafe { CStr::from_ptr((*value.__bindgen_anon_1.lexemeValue).contents) }.to_string_lossy().into_owned();
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

unsafe extern "C" fn trampoline(env: *mut clips::Environment, context: *mut clips::UDFContext, return_value: *mut clips::UDFValue) {
    let closure = unsafe { &mut *(context.as_ref().unwrap().context as *mut Box<dyn FnMut(&mut Environment, &mut UDFContext) -> ClipsValue>) };
    let mut safe_env = std::mem::ManuallyDrop::new(Environment { raw: env });
    let mut safe_context = UDFContext::new(context);
    let ret = closure(&mut safe_env, &mut safe_context);
    unsafe {
        match ret {
            ClipsValue::Void() => {}
            ClipsValue::Symbol(s) => {
                let s_cstr = CString::new(s).unwrap();
                (*return_value).__bindgen_anon_1.lexemeValue = clips::CreateSymbol(env, s_cstr.as_ptr());
            }
            ClipsValue::String(s) => {
                let s_cstr = CString::new(s).unwrap();
                (*return_value).__bindgen_anon_1.lexemeValue = clips::CreateString(env, s_cstr.as_ptr());
            }
            ClipsValue::Float(f) => {
                (*return_value).__bindgen_anon_1.floatValue = clips::CreateFloat(env, f);
            }
            ClipsValue::Integer(i) => {
                (*return_value).__bindgen_anon_1.integerValue = clips::CreateInteger(env, i);
            }
            ClipsValue::Multifield(vals) => {
                let mb = safe_env.multifield_builder(vals.len()).unwrap();
                let mb = vals.iter().fold(mb, |mb, v| {
                    match v {
                        ClipsValue::Integer(i) => mb.put_int(*i),
                        ClipsValue::Float(f) => mb.put_float(*f),
                        ClipsValue::Symbol(s) => mb.put_symbol(s),
                        ClipsValue::String(s) => mb.put_string(s),
                        _ => mb, // Return builder unchanged for unsupported types
                    }
                });
                let mf = mb.create();
                (*return_value).__bindgen_anon_1.multifieldValue = mf.raw;
                std::mem::forget(mf);
            }
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

    #[test]
    fn test_load_from_string_error() {
        let mut env = Environment::new().unwrap();
        let result = env.load_from_str("(deftemplate test_deftemplate");
        assert!(result.is_err());
    }

    #[test]
    #[ignore]
    fn test_load_from_file() {
        let mut env = Environment::new().unwrap();
        let result = env.load(Path::new("test.clp"));
        assert!(result.is_ok());
    }

    #[test]
    fn test_load_from_file_error() {
        let mut env = Environment::new().unwrap();
        let result = env.load(Path::new("non_existent_file.clp"));
        assert!(result.is_err());
    }

    #[test]
    fn test_run() {
        let mut env = Environment::new().unwrap();
        env.load_from_str("(deffacts test_facts (initial-fact))").unwrap();
        let result = env.run(-1);
        assert_eq!(result, 0);
    }

    #[test]
    fn test_fact_builder() {
        let mut env = Environment::new().unwrap();
        env.load_from_str("(deftemplate test_template (slot test_slot))").unwrap();
        let fact_builder = env.fact_builder("test_template").unwrap().put_symbol("test_slot", "test_value").unwrap();
        let fact = env.assert_fact(fact_builder);
        assert!(fact.is_ok());
    }

    #[test]
    fn test_fact_modifier() {
        let mut env = Environment::new().unwrap();
        env.load_from_str("(deftemplate test_template (slot a) (slot b))").unwrap();

        let builder = env.fact_builder("test_template").unwrap().put_int("a", 1).unwrap().put_symbol("b", "x").unwrap();
        let fact = env.assert_fact(builder).unwrap();

        let modifier = env.fact_modifier(&fact).unwrap().put_int("a", 42).unwrap().put_symbol("b", "y").unwrap();
        let updated_fact = env.modify_fact(modifier);
        assert!(updated_fact.is_ok());
    }

    #[test]
    fn test_fact_modifier_slot_not_found() {
        let mut env = Environment::new().unwrap();
        env.load_from_str("(deftemplate test_template (slot a))").unwrap();

        let builder = env.fact_builder("test_template").unwrap().put_int("a", 1).unwrap();
        let fact = env.assert_fact(builder).unwrap();

        let result = env.fact_modifier(&fact).unwrap().put_int("missing", 2);
        assert!(matches!(result, Err(ClipsError::PutSlotSlotNotFoundError(_))));
    }

    #[test]
    fn test_multifield_builder() {
        let env = Environment::new().unwrap();
        let multifield = env.multifield_builder(3).unwrap().put_int(42).put_float(3.14).put_symbol("test_symbol").create();
        assert!(multifield.raw.is_null() == false);
    }

    #[test]
    fn test_add_udf() {
        let mut env = Environment::new().unwrap();
        let called = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        let called_clone = called.clone();

        env.add_udf("test_udf", Some(Type(Type::VOID)), 0, 0, vec![], move |_env, _ctx| {
            called_clone.store(true, std::sync::atomic::Ordering::SeqCst);
            ClipsValue::Void()
        })
        .unwrap();

        env.load_from_str("(defrule test_rule => (test_udf))").unwrap();
        env.run(-1);

        assert!(called.load(std::sync::atomic::Ordering::SeqCst));
    }

    #[test]
    fn test_add_udf_with_args() {
        let mut env = Environment::new().unwrap();
        let value = std::sync::Arc::new(std::sync::atomic::AtomicI64::new(0));
        let value_clone = value.clone();

        env.add_udf("test_udf_args", Some(Type(Type::VOID)), 1, 1, vec![Type(Type::INTEGER)], move |_env, ctx| {
            let arg = ctx.get_next_argument(Type(Type::INTEGER)).unwrap();
            if let ClipsValue::Integer(i) = arg {
                value_clone.store(i, std::sync::atomic::Ordering::SeqCst);
            }
            ClipsValue::Void()
        })
        .unwrap();

        env.load_from_str("(defrule test_rule_args => (test_udf_args 42))").unwrap();
        env.run(-1);

        assert_eq!(value.load(std::sync::atomic::Ordering::SeqCst), 42);
    }

    #[test]
    fn test_build() {
        let mut env = Environment::new().unwrap();
        let result = env.build("(deftemplate test_build_template (slot test_slot))");
        assert!(result.is_ok());
    }

    #[test]
    fn test_build_error() {
        let mut env = Environment::new().unwrap();
        let result = env.build("(deftemplate test_build_template");
        assert!(result.is_err());
    }
}
