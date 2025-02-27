// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

use super::{
    code_types::{self, AsCodeType, CodeType},
    BindingConfig, BindingGenerator, Bindings,
};
use anyhow::Context;
use heck::ToKebabCase;
use rinja::Template;
use std::{
    cell::RefCell,
    collections::{BTreeSet, HashSet},
    fmt::Debug,
};
use uniffi_bindgen::{
    interface::{
        Argument, AsType, Callable, ComponentInterface, Constructor, Enum, FfiArgument, FfiField,
        Field, Function, Literal, Method, Object, Record, Type, Variant,
    },
    VisitMut,
};

impl BindingConfig {
    /// The name of the Alicorn module containing the high-level foreign-language bindings.
    /// Panics if the module name hasn't been configured.
    pub fn module_name(&self) -> String {
        self.module_name
            .as_ref()
            .expect("module name should have been set in update_component_configs")
            .clone()
    }
}

impl BindingGenerator {
    pub fn generate_library(
        &self,
        config: &BindingConfig,
        ci: &mut ComponentInterface,
    ) -> anyhow::Result<String> {
        Wrapper::new(config.clone(), ci)
            .render()
            .context("failed to render Alicorn bindings")
    }

    /// Generate Alicorn bindings for the given ComponentInterface, as strings in memory.
    pub fn generate_bindings(
        &self,
        config: &BindingConfig,
        ci: &mut ComponentInterface,
    ) -> anyhow::Result<Bindings> {
        let library = self.generate_library(config, ci)?;
        Ok(Bindings { library })
    }
}

/// A struct to record an Alicorn import statement.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ImportRequirement {
    /// A magical module import.
    Magic { mod_name: String },
    /// A simple, actual module import.
    Module { mod_name: String },
}

impl ImportRequirement {
    /// Render the Alicorn import statement.
    fn render(&self) -> String {
        match &self {
            ImportRequirement::Magic { mod_name } => {
                let mod_name_literal = code_types::String::render(mod_name);
                format!("# magic-open (module {mod_name_literal})")
            }
            ImportRequirement::Module { mod_name } => {
                let mod_name_literal = code_types::String::render(mod_name);
                format!("let {mod_name} = module {mod_name_literal}")
            }
        }
    }
}

/// Renders Alicorn helper code for all types
///
/// This template is a bit different than others in that it stores internal state from the render
/// process.  Make sure to only call `render()` once.
#[derive(Template)]
#[template(syntax = "alc", escape = "none", path = "Types.alc")]
pub struct TypeRenderer<'a> {
    config: &'a BindingConfig,
    ci: &'a ComponentInterface,
    // Track included modules for the `include_once()` macro
    include_once_names: RefCell<HashSet<String>>,
    // Track imports added with the `add_import()` macro
    imports: RefCell<BTreeSet<ImportRequirement>>,
}

impl<'a> TypeRenderer<'a> {
    fn new(config: &'a BindingConfig, ci: &'a ComponentInterface) -> Self {
        Self {
            config,
            ci,
            include_once_names: RefCell::new(HashSet::new()),
            imports: RefCell::new(BTreeSet::new()),
        }
    }
}

#[derive(Template)]
#[template(syntax = "alc", escape = "none", path = "wrapper.alc")]
pub struct Wrapper<'a> {
    ci: &'a ComponentInterface,
    config: BindingConfig,
    type_helper_code: String,
    type_imports: BTreeSet<ImportRequirement>,
}

impl<'a> Wrapper<'a> {
    pub fn new(config: BindingConfig, ci: &'a mut ComponentInterface) -> Self {
        ci.visit_mut(&CodeOracle);

        let type_renderer = TypeRenderer::new(&config, ci);
        let type_helper_code = type_renderer.render().unwrap();
        let type_imports = type_renderer.imports.into_inner();

        Self {
            config,
            ci,
            type_helper_code,
            type_imports,
        }
    }

    pub fn imports(&self) -> Vec<ImportRequirement> {
        self.type_imports.iter().cloned().collect()
    }
}

#[derive(Clone, Default)]
pub struct CodeOracle;

impl CodeOracle {
    pub fn find(&self, type_: &Type) -> Box<dyn CodeType> {
        type_.clone().as_type().as_code_type()
    }

    /// Get the idiomatic Alicorn rendering of a class name.
    pub fn class_name(&self, nm: &str) -> String {
        nm.to_kebab_case()
    }

    /// Get the idiomatic Alicorn rendering of an individual enum variant.
    fn enum_variant_name<S: AsRef<str>>(&self, nm: S) -> String {
        nm.as_ref().to_string().to_kebab_case()
    }

    /// Get the idiomatic Alicorn rendering of a function name.
    pub fn fn_name(&self, nm: &str) -> String {
        nm.to_kebab_case()
    }

    /// Get the idiomatic Alicorn rendering of a variable name.
    pub fn var_name(&self, nm: &str) -> String {
        nm.to_kebab_case()
    }

    /// Get the idiomatic Alicorn rendering of a type name.
    pub fn type_name(&self, nm: &str) -> String {
        nm.to_kebab_case()
    }
}

impl VisitMut for CodeOracle {
    fn visit_record(&self, record: &mut Record) {
        record.rename(self.class_name(record.name()));
    }

    fn visit_object(&self, object: &mut Object) {
        object.rename(self.class_name(object.name()));
        for i in object.trait_impls_mut() {
            i.trait_name = self.class_name(&i.trait_name);
            // should i.tr_module_path be fixed?
        }
    }

    fn visit_field(&self, field: &mut Field) {
        field.rename(self.var_name(field.name()));
    }

    fn visit_ffi_field(&self, ffi_field: &mut FfiField) {
        ffi_field.rename(self.var_name(ffi_field.name()));
    }

    fn visit_ffi_argument(&self, ffi_argument: &mut FfiArgument) {
        ffi_argument.rename(self.class_name(ffi_argument.name()));
    }

    fn visit_enum(&self, _is_error: bool, enum_: &mut Enum) {
        enum_.rename(self.class_name(enum_.name()));
    }

    fn visit_enum_key(&self, key: &mut String) -> String {
        self.class_name(key)
    }

    fn visit_variant(&self, is_error: bool, variant: &mut Variant) {
        if is_error {
            variant.rename(self.class_name(variant.name()));
        } else {
            variant.rename(self.enum_variant_name(variant.name()));
        }
    }

    fn visit_type(&self, type_: &mut Type) {
        // Renaming Types is a special case. We have simple types with names like
        // an Object, but we also have types which have inner_types and builtin types.
        // Which in turn have a different name. Therefore we pass the patterns as a
        // function down to the renaming operation of the type itself, which can apply it
        // to all its nested names if needed.
        let name_transformer = |name: &str| self.class_name(name);
        type_.rename_recursive(&name_transformer);
    }

    fn visit_method(&self, method: &mut Method) {
        method.rename(self.fn_name(method.name()));
    }

    fn visit_argument(&self, argument: &mut Argument) {
        argument.rename(self.var_name(argument.name()));
    }

    fn visit_constructor(&self, constructor: &mut Constructor) {
        if !constructor.is_primary_constructor() {
            constructor.rename(self.fn_name(constructor.name()));
        }
    }

    fn visit_function(&self, function: &mut Function) {
        // Conversions for wrapper.py
        //TODO: Renaming the function name in wrapper.py is not currently tested
        function.rename(self.fn_name(function.name()));
    }

    fn visit_error_name(&self, name: &mut String) {
        *name = self.class_name(name);
    }
}

mod filters {
    use super::*;
    pub use uniffi_bindgen::backend::filters::*;

    /// Get the idiomatic Alicorn rendering of a docstring
    pub fn docstring(docstring: &str, tabs: &i32) -> Result<String, rinja::Error> {
        let wrapped = textwrap::indent(&textwrap::dedent(docstring), "#? ");

        let tabs = usize::try_from(*tabs).unwrap_or_default();
        Ok(textwrap::indent(&wrapped, &"\t".repeat(tabs)))
    }

    pub fn ffi_error_converter_name(as_type: &impl AsType) -> Result<String, rinja::Error> {
        // special handling for types used as errors.
        let mut name = CodeOracle.find(&as_type.as_type()).ffi_converter_name();
        if matches!(&as_type.as_type(), Type::Object { .. }) {
            name.push_str("__as_error")
        }
        Ok(name)
    }

    /// Get the idiomatic Alicorn rendering of a function name.
    pub fn fn_name(nm: &str) -> Result<String, rinja::Error> {
        Ok(CodeOracle.fn_name(nm))
    }

    // See below re. `lower_fn`—we always use the public version for named types.
    pub fn lift_fn(as_type: &impl AsType) -> Result<String, rinja::Error> {
        let ty = &as_type.as_type();
        let ffi_converter_name = CodeOracle.find(ty).ffi_converter_name();
        Ok(match ty.name() {
            Some(_) => format!("{}_lift", ffi_converter_name),
            None => format!("{}.lift", ffi_converter_name),
        })
    }

    pub fn literal_alicorn(
        literal: &Literal,
        as_type: &impl AsType,
    ) -> Result<String, rinja::Error> {
        CodeOracle
            .find(&as_type.as_type())
            .literal(literal)
            .map_err(|e| to_rinja_error(&e))
    }

    // To better support external types, we always call the "public" lift and lower functions for
    // "named" types, regardless of whether they are being called from a type in the same crate
    // (ie, a "local" type) or from a different crate (ie, an "external" type)
    pub fn lower_fn(as_type: &impl AsType) -> Result<String, rinja::Error> {
        let ty = &as_type.as_type();
        let ffi_converter_name = CodeOracle.find(ty).ffi_converter_name();
        Ok(match ty.name() {
            Some(_) => format!("{}_lower", ffi_converter_name),
            None => format!("{}.lower", ffi_converter_name),
        })
    }

    pub fn type_name(as_type: &impl AsType) -> Result<String, rinja::Error> {
        Ok(CodeOracle.find(&as_type.as_type()).type_label())
    }

    /// Get the idiomatic Alicorn rendering of a variable name.
    pub fn var_name(nm: &str) -> Result<String, rinja::Error> {
        Ok(CodeOracle.var_name(nm))
    }

    pub fn write_fn(as_type: &impl AsType) -> Result<String, rinja::Error> {
        let ty = &as_type.as_type();
        let ffi_converter_name = CodeOracle.find(ty).ffi_converter_name();
        Ok(format!("{}.write", ffi_converter_name))
    }
}
