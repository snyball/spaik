//! # The **SPAIK**-LISP Programming Language
//!
//! This is the documentation for **SPAIK** an embeddable Lisp dialect for
//! Rust.
//!
//! ```lisp
//! (dolist (x '(this new unknown))
//!   (println "Hello, {x} World!"))
//! ```
//! ```text
//! Hello, this World!
//! Hello, new World!
//! Hello, unknown World!
//! ```
//!
//! ## Running SPAIK from Rust
//!
//! ```rust
//! use spaik::Spaik;
//!
//! let mut vm = Spaik::new();
//! vm.exec(r#"(println "code")"#).unwrap();
//! let res: f32 = vm.eval(r#"(sqrt (+ 1 2))"#).unwrap();
//! ```

#![allow(clippy::upper_case_acronyms)]
#![allow(clippy::option_map_unit_fn)]
#![allow(unused_imports)]

#[allow(unused_imports)]
#[macro_use]
extern crate log;
#[macro_use]
pub mod error;
#[macro_use]
pub(crate) mod utils;
#[macro_use]
pub(crate) mod chasm;
#[macro_use]
pub(crate) mod nkgc;
#[macro_use]
pub(crate) mod r8vm;
#[macro_use]
pub(crate) mod ast;
pub(crate) mod opt;
pub(crate) mod fmt;
pub(crate) mod tokit;
pub(crate) mod subrs;
pub(crate) mod builtins;
pub(crate) mod string_parse;
pub mod plug;
pub use plug::*;
pub use r8vm::Func;
use r8vm::NArgs;
pub use r8vm::OutStream;
pub use subrs::FromLisp3;
use subrs::IntoSubr;
pub use subrs::{Lispify, PList};
pub use tokit::minify;
pub(crate) mod tok;
#[macro_use]
pub(crate) mod nuke;
pub(crate) mod swym;
pub(crate) mod pmem;
pub(crate) mod stak;
pub(crate) mod lisp_test;
mod stack_gymnastics;
pub use lisp_test::run_tests;
#[cfg(feature = "modules")]
pub(crate) mod module;
#[cfg(feature = "serde")]
pub(crate) mod deserialize;
#[cfg(feature = "serde")]
pub(crate) mod limits;
#[cfg(feature = "math")]
pub(crate) mod math;
pub(crate) mod comp;
pub mod repl;
pub(crate) mod scratch;
/// SPAIK scratchpad for use in development of SPAIK itself.
pub use scratch::main as scratch_main;
pub(crate) mod stylize;
#[cfg(feature = "derive")]
pub mod records;

#[cfg(feature = "derive")]
pub use spaik_proc_macros::{Fissile, kebabify, methods, hooks, Obj};
pub use nkgc::SPV;
pub(crate) use nkgc::SymID;
pub(crate) use nkgc::ObjRef;
pub use nuke::Gc;
pub type Str = Arc<str>;
pub use nuke::Userdata;
pub use swym::SymRef as Sym;
#[cfg(feature = "derive")]
pub use records::{FieldAccess, MethodCall, KebabTypeName, Enum, MacroNewVariant, MacroNew, MethodSet, SubrSet};
#[cfg(test)]
pub mod logging;
#[macro_use]
pub mod events;
pub use events::LinkedEvents;

def_call_builder!();

/** This is NOT a public interface.
 * Dependencies for procedural macros (feature "derive".)
 *
 * Everything inside this module should be considered an implementation detail,
 * and can change between even semver patch versions.
 */
pub mod _deps {
    pub use crate::r8vm::{R8VM, ArgSpec, ObjMethod};
    pub use crate::nkgc::SymID;
    pub use crate::nkgc::{PV, ObjRef, Arena, Traceable};
    pub use crate::nuke::{NkAtom, PtrMap, Object, cast_mut_err};
    pub use crate::fmt::LispFmt;
    pub use crate::fmt::VisitSet;
    #[cfg(feature = "derive")]
    pub use crate::records::{into_init, into_macro_news, MacroNewVariant};
    pub use crate::error::{Error, Result, OpName};
}

use std::any::type_name;

use std::fmt::Debug;

use std::sync::Arc;

pub use crate::builtins::Builtin;
pub use crate::nuke::Fissile;
use crate::r8vm::R8VM;
pub use crate::r8vm::Args;
use crate::nkgc::PV;
pub use crate::subrs::{Subr, IntoLisp, FromLisp, Ignore, BoxSubr};
pub use crate::error::Error;
pub use crate::error::Result;

/// The easiest way to get started with SPAIK is `use spaik::prelude::*`
pub mod prelude {
    pub use super::{Subr, IntoLisp, FromLisp, Sym,
                    Ignore, BoxSubr, plug::SpaikPlug, Spaik, Gc};
    #[cfg(feature = "derive")]
    pub use spaik_proc_macros::Fissile;
}

#[cfg(feature = "math")]
pub use glam::{Vec2, Vec3, Vec4, vec2, vec3, vec4};

#[cfg(feature = "freeze")]
use serde::{Serialize, Deserialize};

/// Object for use in SPAIK examples
#[derive(Debug, Clone, PartialEq, PartialOrd)]
#[cfg_attr(feature = "freeze", derive(Serialize, Deserialize))]
pub struct ExampleObject {
    pub x: f32,
    pub y: f32,
}
trivial_trace!(ExampleObject);
impl Userdata for ExampleObject {}
impl fmt::LispFmt for ExampleObject {
    fn lisp_fmt(&self,
                _visited: &mut fmt::VisitSet,
                f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(ExampleObject :x {} :y {})", self.x, self.y)
    }
}
unsafe impl Subr for ExampleObject {
    fn call(&mut self, _vm: &mut R8VM, _args: &[PV]) -> std::result::Result<PV, Error> {
        todo!()
    }

    fn name(&self) -> &'static str {
        todo!()
    }
}
impl IntoLisp for ExampleObject {
    fn into_pv(self, mem: &mut _deps::Arena) -> Result<PV> {
        Ok(mem.put_pv(nuke::Object::new(self)))
    }
}

/// A SPAIK Context, this is the main way to use SPAIK
pub struct Spaik {
    vm: R8VM
}

unsafe impl Send for Spaik {}

pub trait AsFn {
    fn as_fn(&self, vm: &mut R8VM) -> Option<Func>;
}

impl AsFn for Func {
    #[inline(always)]
    fn as_fn(&self, _vm: &mut R8VM) -> Option<Func> {
        Some(*self)
    }
}

impl<T> AsFn for T where T: AsSym {
    #[inline(always)]
    fn as_fn(&self, vm: &mut R8VM) -> Option<Func> {
        let s = self.as_sym(vm);
        vm.get_func(s).copied()
    }
}

pub trait AsSym {
    fn as_sym(&self, vm: &mut R8VM) -> SymID;
}

impl AsSym for &str {
    fn as_sym(&self, vm: &mut R8VM) -> SymID {
        vm.mem.symdb.put_ref(self).id()
    }
}

impl AsSym for SymID {
    fn as_sym(&self, _vm: &mut R8VM) -> SymID {
        *self
    }
}

#[cfg(feature = "derive")]
#[macro_export]
macro_rules! defuns {
    ($vis:vis trait $tr:ident {
        $(fn $f:ident($($arg:ident : $t:ty),*) -> Result<$($e:ty),*>;)*
    }) => {
        $vis trait $tr {
            $(fn $f(&mut self, $($arg : $t),*) -> Result<$($e),*>;)*
        }
        impl $tr for Spaik {
            $(fn $f(&mut self, $($arg : $t),*) -> Result<$($e),*> {
                self.call($crate::kebabify!($f), ($($arg,)*)).map_err(|e| e.into())
            })*
        }
    };
    ($vis:vis trait $tr:ident {
        $(fn $f:ident($($arg:ident : $t:ty),*) -> $r:ty;)*
    }) => {
        $vis trait $tr {
            $(fn $f(&mut self, $($arg : $t),*) -> $r;)*
        }
        impl $tr for Spaik {
            $(fn $f(&mut self, $($arg : $t),*) -> $r {
                self.call($crate::kebabify!($f), ($($arg,)*)).unwrap()
            })*
        }
    };
}

#[cfg(feature = "derive")]
#[macro_export]
macro_rules! defevents {
    ($vis:vis trait $tr:ident {
        $(fn $f:ident($($arg:ident : $t:ty),*);)*
    }) => {
        $vis trait $tr<K> {
            $(fn $f(&mut self, $($arg : $t),*) -> K;)*
        }
        impl $tr<Result<()>> for Spaik {
            $(fn $f(&mut self, $($arg : $t),*) -> Result<()> {
                let _: Ignore = self.call($crate::kebabify!($f), ($($arg,)*))?;
                Ok(())
            })*
        }
        impl<T> $tr<()> for SpaikPlug<T> {
            $(fn $f(&mut self, $($arg : $t),*) {
                self.send($crate::kebabify!($f), ($($arg,)*))
            })*
        }
    };
}

impl Spaik {
    /// Create a new SPAIK VM
    #[inline]
    pub fn new() -> Spaik {
        Spaik { vm: R8VM::new() }
    }

    /// Create a new SPAIK VM
    #[inline]
    pub fn new_no_core() -> Spaik {
        Spaik { vm: R8VM::no_std() }
    }

    /// Register a subroutine (function) with the vm
    #[inline]
    pub fn register(&mut self, func: impl Subr) {
        self.set(func.name(), func.into_subr());
    }

    pub unsafe fn set_resource<T: Userdata>(&mut self, rf: &mut T) {
        self.vm.set_resource(rf)
    }

    pub fn set_stdout(&mut self, out: Box<dyn OutStream>) {
        self.vm.set_stdout(out)
    }

    #[cfg(feature = "derive")]
    fn set_subr_macro(&mut self, name: impl AsSym, macrobx: Box<dyn Subr>) {
        let name = name.as_sym(&mut self.vm);
        let macro_fn_name = format!("<ξ>::<wrap>::{}", name);
        let macro_subr_name = format!("<ζ/ξ>::{}", name);
        self.set(&macro_subr_name[..], macrobx);
        self.exec(format!("(define ({} &body <ζ>::body) (apply {} <ζ>::body))",
                          macro_fn_name, macro_subr_name))
            .expect("error in auto-generated code");
        let macro_fn_name = (&macro_fn_name[..]).as_sym(&mut self.vm);
        self.vm.set_macro(name, macro_fn_name);
    }

    #[cfg(feature = "derive")]
    pub fn defobj<T: records::Enum>(&mut self) {
        for cs in T::enum_constructors() {
            self.set(cs.name(), cs);
        }
        for mac in T::enum_macros() {
            let macbx = Box::new(mac);
            self.set_subr_macro(macbx.name(), macbx);
        }
    }

    #[cfg(feature = "derive")]
    pub fn defmethods<T: Userdata + MethodSet<K> + SubrSet<K>, K>(&mut self) {
        for (kwname, _spec, m) in T::methods() {
            self.vm.register_method::<T>(*kwname, *m)
        }
        for (kwname, _spec, m) in T::methods() {
            self.vm.register_method::<*mut T>(*kwname, *m)
        }
        self.defstatic::<T, K>();
    }

    #[cfg(feature = "derive")]
    pub fn bind_resource_fns<T, K>(&mut self, override_prefix: Option<&'static str>)
        where T: Userdata + MethodSet<K> + KebabTypeName
    {
        self.vm.bind_resource_fns::<T, K>(override_prefix)
    }

    #[cfg(feature = "derive")]
    pub fn defstatic<T: SubrSet<K>, K>(&mut self) {
        for s in T::subrs() {
            let name = s.name();
            self.set(name, s);
        }
    }

    #[inline]
    pub fn defun<A, R, F: IntoSubr<A, R>>(&mut self, func: F) {
        let t = type_name::<F>();
        let (_, name) = t.rsplit_once(':').unwrap_or(("", t));
        let name = name.replace('_', "-");
        self.set(&name[..], func.into_subr());
    }

    pub fn set<A, R, N>(&mut self, var: impl AsSym, obj: impl Lispify<A, R, N>) {
        let var = var.as_sym(&mut self.vm);
        self.vm.set(var, obj).unwrap();
        self.vm.mem.pop_borrows();
    }

    /// Return a clone of `var`
    #[inline]
    pub fn get<R,A>(&mut self, var: impl AsSym) -> Result<R>
        where PV: FromLisp3<R,A,()>
    {
        let name = var.as_sym(&mut self.vm);
        let idx = self.vm.get_env_global(name)
                         .ok_or(error!(UndefinedVariable, var: name.into()))?;
        self.vm.mem.get_env(idx)
                   .from_lisp_3(&mut self.vm.mem)
    }

    /// Return a function by `name`, or an error if it does not exist.
    #[inline]
    pub fn getfn(&mut self, name: impl AsSym) -> Result<Func> {
        let name = name.as_sym(&mut self.vm);
        self.vm.get_func(name).copied().ok_or(error!(UndefinedFunction, name: name.into()))
    }


    /// Get a reference to a user-defined object type stored in the vm.
    ///
    /// # Arguments
    ///
    /// - `var` : Variable name
    ///
    /// # Safety
    ///
    /// The returned pointer may not be dereferenced after a garbage-collection
    /// cycle runs, which also means that no SPAIK code may run on this VM before
    /// the pointer is dereferenced. A gc cycle may leave the returned pointer
    /// dangling.
    ///
    /// # Safe Alternative
    ///
    /// Use `Gc<T>`, like this:
    ///
    /// ```rust
    /// use spaik::prelude::*;
    /// use spaik::ExampleObject;
    /// let mut vm = Spaik::new_no_core();
    /// vm.set("obj", ExampleObject { x: 1.0, y: 3.3 });
    /// let mut obj: Gc<ExampleObject> = vm.get("obj").unwrap();
    /// assert_eq!(obj.with(|r| (r.x, r.y)), (1.0, 3.3));
    /// ```
    #[inline]
    pub unsafe fn objref<T>(&mut self, var: impl AsSym) -> Result<*const T>
        where T: Userdata
    {
        self.objref_mut(var).map(|rf| rf as *const T)
    }

    /// Retrieve a variable as a mutable reference.
    ///
    /// # Arguments
    ///
    /// - `var` : Variable name
    ///
    /// # Safety
    ///
    /// The returned pointer may not be dereferenced after a garbage-collection
    /// cycle runs, which also means that no SPAIK code may run on this VM before
    /// the pointer is dereferenced. A gc cycle may leave the returned pointer
    /// dangling.
    ///
    /// # Safe Alternative
    ///
    /// Use `Gc<T>`, like this:
    ///
    /// ```rust
    /// use spaik::prelude::*;
    /// use spaik::ExampleObject;
    /// let mut vm = Spaik::new_no_core();
    /// vm.set("obj", ExampleObject { x: 1.0, y: 3.3 });
    /// let mut obj: Gc<ExampleObject> = vm.get("obj").unwrap();
    /// assert_eq!(obj.with(|r| (r.x, r.y)), (1.0, 3.3));
    /// ```
    #[inline]
    pub unsafe fn objref_mut<T>(&mut self, var: impl AsSym) -> Result<*mut T>
        where T: Userdata
    {
        let name = var.as_sym(&mut self.vm);
        let idx = self.vm.get_env_global(name)
                         .ok_or(error!(UndefinedVariable, var: name.into()))?;
        let ObjRef(x): ObjRef<*mut T> = self.vm.mem.get_env(idx)
                                                   .try_into()?;
        Ok(x)
    }

    /// Run an expression.
    ///
    /// # Arguments
    ///
    /// - `expr` : Lisp expression
    #[inline]
    pub fn eval<R,A>(&mut self, expr: impl AsRef<str>) -> Result<R>
        where PV: FromLisp3<R,A,()>
    {
        self.vm.eval(expr.as_ref())
               .and_then(|pv| pv.from_lisp_3(&mut self.vm.mem))
    }

    pub fn take<T>(&mut self, var: impl AsSym) -> Result<T>
        where T: 'static
    {
        let sym = var.as_sym(&mut self.vm);
        self.vm.globals.remove(&sym)
                       .ok_or_else(|| error!(UndefinedVariable, var: sym.into()))
                       .and_then(|i| with_ref_mut!(self.vm.mem.env[i],
                                                   Object(s) => { (*s).take() }))
    }

    /// Run an expression and ignore the result (unless there was an error.)
    ///
    /// # Arguments
    ///
    /// - `expr` : Lisp expression
    #[inline]
    pub fn exec(&mut self, expr: impl AsRef<str>) -> Result<()> {
        let _: Ignore = self.eval(expr)?;
        Ok(())
    }

    pub fn trace_report(&self) {
        self.vm.count_trace_report()
    }

    /// Load library from the load-path
    ///
    /// # Arguments
    ///
    /// - `lib` : If the library is stored at `"<name>.lisp"`, then `lib` should be
    ///           `<name>` as either a string or symbol
    #[inline]
    pub fn load<R,A>(&mut self, lib: impl AsSym) -> Result<R> where PV: FromLisp3<R,A,()> {
        let lib = lib.as_sym(&mut self.vm);
        self.vm.load_eval(lib)
               .and_then(|pv| pv.from_lisp_3(&mut self.vm.mem))
    }

    /// Load a SPAIK library from a string, this is useful both for embedding code
    /// into your binary with e.g `load_with(x, y, include_str!(...))` or when
    /// loading from a virtual filesystem.
    ///
    /// # Arguments
    ///
    /// - `src_path` : File-system path to the `.lisp` file, needed for
    ///                source-file/line error messages.
    /// - `lib` : Library symbol name, i.e the argument to `(load ...)`
    /// - `code` : The source-code contents inside `src_path`
    #[inline]
    pub fn load_with<S>(&mut self, _src_path: S, _lib: Sym, _code: S) -> Result<Sym>
        where S: AsRef<str>
    {
        todo!()
    }

    /// Call a function by-name an args and return the result.
    ///
    /// Use `Spaik::run` if don't care about the result.
    #[inline]
    pub fn call<R, A, L>(&mut self, sym: impl AsSym, args: impl NArgs<A>) -> Result<R>
        where PV: FromLisp3<R,L,()>
    {
        let sym = sym.as_sym(&mut self.vm);
        self.vm.ncall(sym, args)
               .and_then(|pv| pv.from_lisp_3(&mut self.vm.mem))
    }

    /// Call a function by-name an args and return the result.
    ///
    /// Use `Spaik::run` if don't care about the result.
    #[inline]
    pub fn callfn<R, A, K>(&mut self, f: impl AsRef<Func>, args: impl NArgs<A>) -> Result<R>
        where PV: FromLisp3<R,K,()>
    {
        self.vm.callfn(f.as_ref(), args)
               .and_then(|pv| pv.from_lisp_3(&mut self.vm.mem))
    }

    /// Call a function by-name an args and ignore the result.
    ///
    /// Use `Spaik::call` if you need the result.
    #[inline]
    pub fn run<A>(&mut self, sym: impl AsSym, args: impl NArgs<A>) -> Result<()> {
        let _: Ignore = self.call(sym, args)?;
        Ok(())
    }

    /// Perform a full GC collection, this may finish a currently ongoing collection
    /// and start a new one afterwards.
    #[inline]
    pub fn gc(&mut self) {
        self.vm.mem.full_collection()
    }

    /// Fulfil a `Promise<T>` by running its continuation with value `ans`
    pub fn fulfil<R,A,T,O>/*🐀*/(&mut self,
                                 pr: Promise<T>,
                                 ans: A) -> Result<R>
        where PV: FromLisp3<R,O,()>,
              A: IntoLisp + Clone + Send + 'static,
    {
        if let Some(cont) = pr.cont {
            self.vm.apply_spv(cont, (ans,))
                   .and_then(|pv| pv.from_lisp_3(&mut self.vm.mem))

        } else {
            PV::Nil.from_lisp_3(&mut self.vm.mem)
        }
    }

    /// Add to load path, this influences where `Spaik::load` will search for
    /// spaik files.
    ///
    /// # Panics
    ///
    /// Panics if the `sys/load-path` variable is not defined, or is not a
    /// vector.
    pub fn add_load_path(&mut self, path: impl AsRef<str>) {
        let p = self.vm.var(Builtin::SysLoadPath.sym_id()).unwrap();
        let s = self.vm.mem.put_pv(path.as_ref().to_string());
        with_ref_mut!(p, Vector(v) => {
            (*v).push(s);
            Ok(())
        }).unwrap();
    }

    /// Move the VM off-thread and return a `SpaikPlug` handle for IPC.
    #[cfg(not(feature = "no-threading"))]
    pub fn fork<T>(mut self) -> SpaikPlug<T>
        where T: serde::de::DeserializeOwned + Send + Debug + Clone + 'static
    {
        use std::{sync::mpsc::channel, thread};

        if self.vm.has_mut_extrefs() {
            panic!("Cannot fork vm with existing mutable Gc reference");
        }

        let (rx_send, tx_send) = channel::<Promise<T>>();
        let (rx_run, tx_run) = channel();
        let handle = thread::spawn(move || {
            self.register(send_message { sender: rx_send });
            loop {
                let ev: Event = tx_run.recv().unwrap();
                match ev {
                    Event::Stop => break,
                    Event::Promise { res, cont } => {
                        let res = self.vm.apply_spv(cont, res);
                        if let Err(e) = res {
                            log::error!("{e}");
                        }
                    }
                    Event::Event { name, args } => {
                        let sym = name.as_sym(&mut self.vm);
                        let res = self.vm.call(sym, args).and_then(|pv| {
                            let r: Ignore = pv.try_into()?;
                            Ok(r)
                        });
                        if let Err(e) = res {
                            log::error!("{e}");
                        }
                    }
                }
            }
            self
        });
        SpaikPlug {
            promises: tx_send,
            events: rx_run,
            handle
        }
    }
}

impl Default for Spaik {
    fn default() -> Self {
        Self::new()
    }
}

pub struct Lambda(SPV);

pub struct PrepLambda<'a, 'b, 'c> {
    lambda: &'a Lambda,
    vm: &'b mut R8VM,
    _ph: std::marker::PhantomData<&'c ()>
}

impl<'q: 'c, 'a, 'b, 'c> PrepLambda<'a, 'b, 'c> {
    pub fn with_resource<G>(self, global: &'q mut G) -> PrepLambda<'a, 'b, 'q>
        where G: Userdata
    {
        unsafe { self.vm.set_resource(global) };
        PrepLambda { lambda: self.lambda, vm: self.vm, _ph: Default::default() }
    }

    pub fn call<R, A, O>(self, args: impl NArgs<A>) -> Result<R>
        where PV: FromLisp3<R,O,()>
    {
        self.vm.napply_pv(self.lambda.0.pv(&self.vm.mem), args)
               .and_then(|pv| pv.from_lisp_3(&mut self.vm.mem))
    }

    pub fn run<R, A>(self, args: impl NArgs<A>) -> Result<()>
        where PV: FromLisp<R>
    {
        self.vm.napply_pv(self.lambda.0.pv(&self.vm.mem), args)?;
        Ok(())
    }
}

impl FromLisp<Lambda> for PV {
    fn from_lisp(self, mem: &mut _deps::Arena) -> std::result::Result<Lambda, Error> {
        (self.bt_type_of() == Builtin::Lambda)
            .then(|| Lambda(mem.make_extref(self)))
            .ok_or_else(|| error!(TypeError,
                                  expect: Builtin::Lambda,
                                  got: self.bt_type_of()))
    }
}

impl IntoLisp for Lambda {
    fn into_pv(self, mem: &mut _deps::Arena) -> std::result::Result<PV, Error> {
        Ok(self.0.pv(mem))
    }
}

impl Lambda {
    pub fn on<'a, 'b>(&'a self, vm: &'b mut Spaik) -> PrepLambda<'a, 'b, 'b> {
        PrepLambda { lambda: self, vm: &mut vm.vm, _ph: Default::default() }
    }
}

#[cfg(test)]
mod tests {
    use serde::{Deserialize, Serialize};
    #[cfg(feature = "derive")]
    use spaik_proc_macros::Fissile;
    use std::sync::atomic::{AtomicI32, Ordering};

    use crate::error::ErrorKind;

    use super::*;

    #[cfg(not(feature = "no-threading"))]
    #[cfg(not(target_arch = "wasm32"))]
    #[test]
    fn spaik_fork_send_from_rust_to_lisp() {
        let mut vm = Spaik::new_no_core();
        defevents!(trait Events {
            fn event_0(x: i32);
        });
        vm.exec("(define init-var nil)").unwrap();
        vm.exec("(define (init) (set init-var 'init))").unwrap();
        vm.exec("(define (event-0 x) (set init-var (+ x 1)))").unwrap();
        vm.event_0(1).unwrap();
        let mut vm = vm.fork::<i32>();
        vm.event_0(123);
        let mut vm = vm.join();
        let init_var: i32 = vm.eval("init-var").unwrap();
        assert_eq!(init_var, 124);
    }

    #[cfg(not(feature = "no-threading"))]
    #[cfg(not(target_arch = "wasm32"))]
    #[test]
    fn spaik_fork_send_from_lisp_to_rust() {
        use std::time::Duration;

        #[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq)]
        #[serde(rename_all = "kebab-case")]
        enum Msg {
            Test { id: i32 },
        }
        let mut vm = Spaik::new();
        vm.exec("(define init-var nil)").unwrap();
        vm.exec("(defun init () (set init-var 'init))").unwrap();
        vm.exec(r#"(defun event-0 (x)
                     (let ((res (await '(test :id 1337))))
                       (set init-var (+ res x 1))))"#).unwrap();
        let vm = vm.fork::<Msg>();
        let ev0_arg = 123;
        vm.send("event-0", (ev0_arg,));
        let p = vm.recv_timeout(Duration::from_secs(10)).expect("timeout");
        assert_eq!(p.get(), &Msg::Test { id: 1337 });
        let fulfil_res = 31337;
        vm.fulfil(p, fulfil_res);
        let mut vm = vm.join();
        let init_var: i32 = vm.eval("init-var").unwrap();
        assert_eq!(init_var, fulfil_res + ev0_arg + 1);
    }

    #[test]
    fn api_eval_add_numbers() {
        let mut vm = Spaik::new_no_core();
        let result: i32 = vm.eval("(+ 2 3)").unwrap();
        assert_eq!(result, 5);
        let result: i16 = vm.eval("(+ 2 3)").unwrap();
        assert_eq!(result, 5);
        let result: f32 = vm.eval("(+ 2.0 3)").unwrap();
        assert_eq!(result, 5.0);
    }

    #[test]
    fn api_func_call() {
        let mut vm = Spaik::new();
        vm.exec(
            "(defun plus (&rest xs) (let ((s 0)) (dolist (x xs) (set s (+ s x))) s))"
        ).unwrap();
        let x = 1;
        let y = 2;
        let z = 3;
        let w = 4;
        let result: i32 = vm.call("plus", (x, y, z, w, 5)).unwrap();
        assert_eq!(result, 15);
    }

    #[cfg(feature = "derive")]
    #[test]
    fn register_fn() {
        fn funky_function(x: i32, y: i32) -> i32 {
            x + 2 + y
        }

        let mut vm = Spaik::new();
        vm.defun(funky_function);
        let result: i32 = vm.eval("(funky-function 2 8)").unwrap();
        assert_eq!(result, 12);

        // FIXME: The vm_call_with! macro should eventually support this:
        // let result: i32 = vm.call("funky-function", (4, 8)).unwrap();
        // assert_eq!(result, 14);
    }

    #[cfg(feature = "derive")]
    #[test]
    fn register_fn_mutate_struct() {
        use crate::error::ErrorKind;

        #[derive(Debug, Clone, PartialEq, PartialOrd, Fissile)]
        #[cfg_attr(feature = "freeze", derive(Serialize, Deserialize))]
        pub struct TestObj {
            x: f32,
            y: f32,
        }

        #[derive(Debug, Clone, PartialEq, PartialOrd, Fissile)]
        #[cfg_attr(feature = "freeze", derive(Serialize, Deserialize))]
        pub struct TestObj2 {
            x: f32,
            thing: String,
        }

        fn my_function(x: i32, y: i32, obj: &TestObj, obj2: &mut TestObj) -> i32 {
            let res = x + y.pow(2);
            obj2.x += obj.x;
            obj2.y += obj.y;
            res
        }

        fn obj_x(obj: &TestObj) -> f32 {
            obj.x
        }

        fn obj_y(obj: &TestObj) -> f32 {
            obj.y
        }

        let mut vm = Spaik::new_no_core();
        vm.defun(obj_x);
        vm.defun(obj_y);
        vm.defun(my_function);
        let src_obj = TestObj { x: 1.0, y: 3.0 };
        let dst_obj = TestObj { x: 1.0, y: 2.0 };
        let wrong_obj = TestObj2 { x: 10.0, thing: "test".to_string() };
        vm.set("wrong-obj", wrong_obj);
        vm.set("src-obj", src_obj.clone());
        vm.set("dst-obj", dst_obj.clone());
        let mut perst_ref: Gc<TestObj> = vm.get("dst-obj").unwrap();
        let _perst_ref_2: Gc<TestObj> = vm.get("dst-obj").unwrap();
        vm.exec("(my-function 1 1 src-obj dst-obj)").unwrap();
        let x: f32 = vm.eval("(obj-x dst-obj)").unwrap();
        let y: f32 = vm.eval("(obj-y dst-obj)").unwrap();
        assert_eq!(x, 2.0);
        assert_eq!(y, 5.0);
        // let dst_obj_2: TestObj = vm.obj("dst-obj").unwrap();
        // assert_eq!(dst_obj_2, TestObj { x: dst_obj.x + src_obj.x,
        //                                 y: dst_obj.y + src_obj.y });
        let expr = "(obj-y wrong-obj)";
        let e = match vm.exec(expr).map_err(|e| e.kind().clone()) {
            Ok(_) => panic!("Expression should fail: {expr}"),
            Err(ErrorKind::Traceback { tb }, ..) => tb.err.kind().clone(),
            Err(e) => panic!("Unexpected error for {expr}: {e:?}"),
        };
        dbg!(&e);
        assert!(matches!(e, ErrorKind::STypeError { .. }));
        drop(vm);
        dbg!(&perst_ref);
        perst_ref.with(|r| r.x = 3.0);
        dbg!(&perst_ref);
    }

    #[test]
    fn test_yield() {
        let mut vm = Spaik::new();
        vm.exec(r#"(defun test-yield () (+ (yield "value") 2))"#).unwrap();
        let pr: Promise<String> = vm.call("test-yield", ()).unwrap();
        assert_eq!(&*pr, "value");
        let res: i32 = vm.fulfil(pr, 5).unwrap();
        assert_eq!(res, 2 + 5);
    }

    #[test]
    fn test_yield_type_err() {
        let mut vm = Spaik::new();
        vm.exec(r#"(defun test-yield () (+ (yield 1) 2))"#).unwrap();
        let pr: Result<Promise<String>> = vm.call("test-yield", ());
        assert!(pr.is_err());
    }

    #[test]
    fn test_load_path() {
        let mut vm = Spaik::new();
        assert!(vm.load::<Ignore,_>("self").is_err());
        vm.add_load_path("lisp");
        let _: Ignore = vm.load("self").unwrap();
        vm.add_load_path("/usr/share/spaik/lib");
        let path: Vec<String> = vm.get("sys/load-path").unwrap();
        assert_eq!(&path, &["lisp", "/usr/share/spaik/lib"]);
        vm.set("sys/load-path", ());
        assert!(vm.get::<(),_>("sys/load-path").is_ok());
    }

    #[test]
    #[should_panic]
    fn test_load_path_illegal_value() {
        let mut vm = Spaik::new();
        vm.set("sys/load-path", ());
        assert!(vm.get::<(),_>("sys/load-path").is_ok());
        vm.add_load_path("lmao");
    }

    #[cfg(not(feature = "no-threading"))]
    #[cfg(not(target_arch = "wasm32"))]
    #[cfg(feature = "derive")]
    #[test]
    #[should_panic]
    fn test_illegal_fork() {
        #[derive(Debug, Clone, PartialEq, PartialOrd, Fissile)]
        #[cfg_attr(feature = "freeze", derive(Serialize, Deserialize))]
        pub struct TestObj {
            x: f32,
            y: f32,
        }

        let mut vm = Spaik::new_no_core();
        vm.set("test-obj", TestObj { x: 10.0, y: 20.0 });
        let _rf: Gc<TestObj> = vm.get("test-obj").unwrap();
        let mut _vm = vm.fork::<()>();
    }

    #[test]
    fn splat() {
        let mut vm = Spaik::new_no_core();
        vm.set("test", 1);
        vm.set("f", |x: i32| x + 2);
        assert_eq!(vm.eval("(f 2)"), Ok(4));
        let n = Arc::new(AtomicI32::new(0));
        let q = n.clone();
        vm.set("g", move || {
            q.fetch_add(1, Ordering::SeqCst);
        });
        vm.exec("(g)").unwrap();
        vm.exec("(g)").unwrap();
        assert_eq!(n.load(Ordering::SeqCst), 2);
    }

    #[test]
    fn give_and_take() {
        let mut vm = Spaik::new_no_core();
        vm.set("test", ExampleObject { x: 1.0, y: 2.0 });
        vm.exec("((lambda (x) x) test)").unwrap();
        let obj: ExampleObject = vm.take("test").unwrap();
        assert_eq!(ExampleObject { x: 1.0, y: 2.0 }, obj);
        assert!(matches!(vm.exec("(+ test 1)").map_err(|e| e.kind().clone()),
                         Err(ErrorKind::UndefinedVariable { .. })));
    }

    #[test]
    fn call_with_lambda() {
        let mut vm = Spaik::new_no_core();
        vm.exec("(define (f g) (g 1))").unwrap();
        assert_eq!(vm.call("f", (|x: i32| x + 2,)), Ok(3));
    }

    #[test]
    fn call_empty() {
        let mut vm = Spaik::new_no_core();
        vm.exec("(define (f) 2)").unwrap();
        assert_eq!(vm.call("f", ()), Ok(2));
    }

    #[test]
    fn call_mut_ref() {
        let mut obj = ExampleObject { x: 1.0, y: 2.0 };
        let mut vm = Spaik::new_no_core();
        vm.exec("(define *q* nil)").unwrap();
        vm.exec("(define (f q) (set *q* q) 2)").unwrap();
        assert_eq!(vm.call("f", (&mut obj,)), Ok(2));
    }

    #[cfg(feature = "derive")]
    #[test]
    #[should_panic]
    fn interface() {
        defuns!(trait C1 {
            fn f(x: i32, y: f32) -> bool;
            fn g(x: i32, y: f32) -> i32;
        });
        let mut vm = Spaik::new_no_core();
        vm.f(10, 32.0);
    }

    #[cfg(feature = "derive")]
    #[test]
    fn interface_2() {
        defuns!(trait C1 {
            fn funky_funk(x: i32, y: i32) -> i32;
            fn g(x: i32, y: i32) -> i32;
        });
        let mut vm = Spaik::new_no_core();
        vm.exec("(define (funky-funk x y) (+ x y))").unwrap();
        vm.exec("(define (g x y) (* x y))").unwrap();
        assert_eq!(vm.funky_funk(5, 5), 10);
        assert_eq!(vm.g(5, 5), 25);
    }

    #[cfg(feature = "derive")]
    #[test]
    fn interface_result() {
        defuns!(trait C1 {
            fn ayy_lmao(x: i32, y: i32) -> Result<i32>;
            fn g(x: i32, y: i32) -> Result<i32>;
        });
        let mut vm = Spaik::new_no_core();
        vm.exec("(define (ayy-lmao x y) (+ x y))").unwrap();
        assert_eq!(vm.ayy_lmao(5, 5), Ok(10));
        assert!(vm.g(5, 5).is_err());
    }

    #[test]
    fn take_lambda() {
        let mut vm = Spaik::new_no_core();
        let s: Lambda = vm.eval("(lambda (x) (+ x 1))").unwrap();
        assert_eq!(s.on(&mut vm).call((2,)), Ok(3));
        let s: Result<Lambda> = vm.eval("1");
        assert!(s.is_err());
    }

    #[cfg(feature = "math")]
    #[test]
    fn math_types() {
        use glam::{vec3, vec2, vec4};

        let mut vm = Spaik::new_no_core();
        let v: glam::Vec3 = vm.eval("(vec3 1 2 3)").unwrap();
        assert_eq!(v, vec3(1.0, 2.0, 3.0));
        assert_eq!(vm.eval("(vec2 2 3)"), Ok(vec2(2.0, 3.0)));
        assert_eq!(vm.eval("(vec4 2 3 5 8)"), Ok(vec4(2.0, 3.0, 5.0, 8.0)));
    }

    #[cfg(feature = "math")]
    #[test]
    fn readme() {
        fn inner() -> Result<()> {
            let mut vm = Spaik::new();
            vm.exec(r#"(println "Hello, World!")"#)?;

            vm.set("f", |x: i32| x + 2); // Functions are first-class at the API boundary!
            assert_eq!(vm.eval("(f 2)"), Ok(4));

            // Optional linear-algebra types from glam
            vm.exec("(defun funky (x y) (* x (vec3 1 y 3)))")?;
            assert_eq!(vm.call("funky", (2, 4)), Ok(glam::vec3(2.0, 8.0, 6.0))); // Call a spaik function

            // Define interfaces more formally
            defuns!(trait MyInterface {
                fn funky(x: f32, y: f32) -> glam::Vec3;
            });
            // This panics if the function `funky` does not match the spec
            assert_eq!(vm.funky(2.0, 4.0), glam::vec3(2.0, 8.0, 6.0));

            Ok(())
        }
        inner().unwrap();
    }

    #[test]
    fn callfn() {
        let mut vm = Spaik::new();
        vm.exec("(define (f x) (+ x 2))").unwrap();
        let f = vm.getfn("f").unwrap();
        assert_eq!(vm.callfn(f, (2,)), Ok(4));
    }

    #[test]
    fn sym_str_eq() {
        let mut vm = Spaik::new_no_core();
        let s: Sym = vm.eval("'x").unwrap();
        assert_eq!(s.as_ref(), "x");
    }
}
