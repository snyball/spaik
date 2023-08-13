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

#[macro_use]
extern crate lazy_static;
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
use subrs::Lispify;
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
// #[cfg(feature = "serde")]
pub(crate) mod deserialize;
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
pub use spaik_proc_macros::{EnumCall, spaikfn, Fissile};
pub use nkgc::SPV;
pub(crate) use nkgc::SymID;
pub(crate) use nkgc::ObjRef;
pub use nuke::Gc;
pub type Str = Arc<str>;
pub use nuke::Userdata;
pub use swym::SymRef as Sym;

/** This is NOT a public interface.
 * Dependencies for procedural macros (feature "derive".)
 *
 * Everything inside this module should be considered an implementation detail,
 * and can change between even semver patch versions.
 */
pub mod proc_macro_deps {
    pub use crate::r8vm::{R8VM, ArgSpec};
    pub use crate::nkgc::SymID;
    pub use crate::nkgc::{PV, ObjRef, Arena, Traceable};
}

use std::fmt::Debug;
use std::sync::Arc;
use std::sync::mpsc::{Sender, Receiver, TryRecvError, RecvTimeoutError};
use std::thread::JoinHandle;
use std::time::Duration;
use std::ops::{Deref, DerefMut};

use serde::de::DeserializeOwned;

pub use crate::builtins::Builtin;
pub use crate::nuke::Fissile;
use crate::r8vm::R8VM;
pub use crate::r8vm::{Args, EnumCall};
pub(crate) use crate::r8vm::ArgSpec;
use crate::nkgc::PV;
pub use crate::subrs::{Subr, IntoLisp, FromLisp, Ignore, BoxSubr};
pub use crate::error::Error;
pub use crate::error::Result;

/// The easiest way to get started with SPAIK is `use spaik::prelude::*`
pub mod prelude {
    pub use super::{Subr, IntoLisp, FromLisp, Sym,
                    Ignore, BoxSubr, SpaikPlug, Spaik, Gc};
    #[cfg(feature = "derive")]
    pub use spaik_proc_macros::{EnumCall, spaikfn, Fissile};
}

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
        write!(f, "(ExampleObject :x {} :y {}", self.x, self.y)
    }
}
impl IntoLisp for ExampleObject {
    fn into_pv(self, mem: &mut proc_macro_deps::Arena) -> Result<PV> {
        Ok(mem.put_pv(nuke::Object::new(self)))
    }
}

/// A SPAIK Context, this is the main way to use SPAIK
pub struct Spaik {
    vm: R8VM
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

    pub fn set<A, R, const N: usize>(&mut self, var: impl AsSym, obj: impl Lispify<A, R, N>) {
        let var = var.as_sym(&mut self.vm);
        self.vm.set(var, obj).unwrap();
    }

    /// Return a clone of `var`
    #[inline]
    pub fn get<R>(&mut self, var: impl AsSym) -> Result<R>
        where PV: FromLisp<R>
    {
        let name = var.as_sym(&mut self.vm);
        let idx = self.vm.get_env_global(name)
                         .ok_or(error!(UndefinedVariable, var: name))?;
        self.vm.mem.get_env(idx)
                   .from_lisp(&mut self.vm.mem)
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

    /// Get a clone of a user-defined object type stored in the vm.
    #[inline]
    pub fn obj<T: Userdata>(&mut self, var: impl AsSym) -> Result<T> {
        unsafe {
            self.objref_mut(var).map(|rf: *mut T| (*rf).clone())
        }
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
                         .ok_or(error!(UndefinedVariable, var: name))?;
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
    pub fn eval<R>(&mut self, expr: impl AsRef<str>) -> Result<R>
        where PV: FromLisp<R>
    {
        self.vm.eval(expr.as_ref())
               .and_then(|pv| pv.from_lisp(&mut self.vm.mem))
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

    /// Load library from the load-path, by default this is `./lisp/`.
    ///
    /// # Arguments
    ///
    /// - `lib` : If the library is stored at `"<name>.lisp"`, then `lib` should be
    ///           `<name>` as either a string or symbol
    #[inline]
    pub fn load(&mut self, lib: impl AsSym) -> Result<Sym> {
        let lib = lib.as_sym(&mut self.vm);
        self.vm.load(lib)
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

    /// Call a function by-enum and return the result
    ///
    /// Use `Spaik::cmd` if don't care about the result.
    #[inline]
    pub fn query<R>(&mut self, enm: impl EnumCall) -> Result<R>
        where PV: FromLisp<R>
    {
        self.vm.call_by_enum(enm)
               .and_then(|pv| pv.from_lisp(&mut self.vm.mem))
    }

    /// Call a function by-enum and ignore the result
    ///
    /// Use `Spaik::query` if you need the result.
    #[inline]
    pub fn cmd(&mut self, enm: impl EnumCall) -> Result<()> {
        let _: Ignore = self.query(enm)?;
        Ok(())
    }

    /// Call a function by-name an args and return the result.
    ///
    /// Use `Spaik::run` if don't care about the result.
    #[inline]
    pub fn call<R>(&mut self, sym: impl AsSym, args: impl Args) -> Result<R>
        where PV: FromLisp<R>
    {
        let sym = sym.as_sym(&mut self.vm);
        self.vm.call(sym, args)
               .and_then(|pv| pv.from_lisp(&mut self.vm.mem))
    }

    /// Call a function by-name an args and ignore the result.
    ///
    /// Use `Spaik::call` if you need the result.
    #[inline]
    pub fn run(&mut self, sym: impl AsSym, args: impl Args) -> Result<()> {
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
    pub fn fulfil<R,A,T>/*🐀*/(&mut self,
                               pr: Promise<T>,
                               ans: A) -> Result<R>
        where PV: FromLisp<R>,
              A: IntoLisp + Clone + Send + 'static,
    {
        if let Some(cont) = pr.cont {
            self.vm.apply_spv(cont, (ans,))
                   .and_then(|pv| pv.from_lisp(&mut self.vm.mem))

        } else {
            PV::Nil.from_lisp(&mut self.vm.mem)
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
        let p = self.vm.var(Builtin::SysLoadPath.sym()).unwrap();
        let s = self.vm.mem.put_pv(path.as_ref().to_string());
        with_ref_mut!(p, Vector(v) => {
            (*v).push(s);
            Ok(())
        }).unwrap();
    }

    /// Move the VM off-thread and return a `SpaikPlug` handle for IPC.
    #[cfg(not(feature = "no-threading"))]
    pub fn fork<T, Cmd>(mut self) -> SpaikPlug<T, Cmd>
        where T: DeserializeOwned + Send + Debug + Clone + 'static,
              Cmd: EnumCall + Send + 'static
    {
        use std::{sync::mpsc::channel, thread};

        if self.vm.has_mut_extrefs() {
            panic!("Cannot fork vm with existing mutable Gc reference");
        }

        let (rx_send, tx_send) = channel::<Promise<T>>();
        let (rx_run, tx_run) = channel();
        let handle = thread::spawn(move || {
            self.register(send_message { sender: rx_send });
            self.run("init", ()).unwrap();
            loop {
                let ev: Event<Cmd> = tx_run.recv().unwrap();
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
                    Event::Command(cmd) => if let Err(e) = self.cmd(cmd) {
                        log::error!("{}", e);
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

impl EnumCall for () {
    fn name(&self, _mem: &mut nkgc::Arena) -> SymID {
        unimplemented!()
    }

    fn pushargs(self, _args: &[SymID], _mem: &mut nkgc::Arena) -> Result<()> {
        unimplemented!()
    }
}

pub enum Event<Cmd: EnumCall + Send> {
    Promise { res: Box<dyn Args + Send>, cont: SPV },
    Event { name: Box<dyn AsSym + Send>,
            args: Box<dyn Args + Send> },
    Command(Cmd),
    Stop,
}

/// Promise made to `SpaikPlug`
#[derive(Debug)]
#[must_use = "A promise made should be a promise kept"]
pub struct Promise<T> {
    msg: Box<T>,
    cont: Option<SPV>,
}

impl<T> Deref for Promise<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.msg
    }
}

impl<T> DerefMut for Promise<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.msg
    }
}

// #[cfg(feature = "serde")]
impl<T> FromLisp<Promise<T>> for PV where T: DeserializeOwned {
    fn from_lisp(self, mem: &mut nkgc::Arena) -> Result<Promise<T>> {
        with_ref!(self, Cons(p) => {
            let msg = (*p).car;
            let cont = (*p).cdr;
            let msg = deserialize::from_pv(msg, &mem.symdb)?;
            if cont.type_of() != Builtin::Continuation.sym() {
                return err!(TypeError,
                            expect: Builtin::Continuation,
                            got: cont.bt_type_of());
            }
            let cont = Some(mem.make_extref(cont));
            Ok(Promise { msg, cont })
        })
    }
}

impl<T> Promise<T> {
    pub fn get(&self) -> &T {
        &self.msg
    }

    pub fn get_mut(&mut self) -> &mut T {
        &mut self.msg
    }
}

/// Asynchronous SPAIK, in another thread
pub struct SpaikPlug<T, Cmd>
    where Cmd: EnumCall + Send, T: Send
{
    promises: Receiver<Promise<T>>,
    events: Sender<Event<Cmd>>,
    handle: JoinHandle<Spaik>,
}

#[derive(Clone, Debug)]
#[allow(non_camel_case_types)]
struct send_message<T>
    where T: DeserializeOwned + Clone + Send
{
    sender: Sender<Promise<T>>,
}

unsafe impl<T> Subr for send_message<T>
    where T: DeserializeOwned + Clone + Send + 'static + Debug + Sized
{
    fn call(&mut self, vm: &mut R8VM, args: &[PV]) -> Result<PV> {
        let (msg, r, cont) = match args {
            [x, y] => (deserialize::from_pv(*x, &vm.mem.symdb)
                       .map_err(|e| e.argn(1).bop(Builtin::ZSendMessage))?,
                       *x,
                       Some(vm.mem.make_extref(*y))),
            [x] => (deserialize::from_pv(*x, &vm.mem.symdb)
                    .map_err(|e| e.argn(1).bop(Builtin::ZSendMessage))?,
                    *x,
                    None),
            _ => ArgSpec::opt(1, 1).check(args.len() as u16)
                                   .map_err(|e| e.bop(Builtin::ZSendMessage))
                                   .map(|_| -> ! { unreachable!() })?

        };
        self.sender.send(Promise { msg, cont })?;
        Ok(r)
    }
    fn name(&self) -> &'static str { "<ζ>-send-message" }
}

impl<T, Cmd> SpaikPlug<T, Cmd>
    where Cmd: EnumCall + Send, T: Send
{
    #[inline]
    pub fn recv(&self) -> Option<Promise<T>>
        where T: DeserializeOwned
    {
        match self.promises.try_recv() {
            Ok(e) => Some(e),
            Err(TryRecvError::Empty) => None,
            Err(TryRecvError::Disconnected) => {
                panic!("Spaik VM disconnected");
            }
        }
    }

    pub fn cmd(&self, cmd: Cmd) {
        self.events.send(Event::Command(cmd)).unwrap();
    }

    #[inline]
    pub fn recv_timeout(&self, timeout: Duration) -> Option<Promise<T>>
        where T: DeserializeOwned
    {
        match self.promises.recv_timeout(timeout) {
            Ok(e) => Some(e),
            Err(RecvTimeoutError::Timeout) => None,
            Err(RecvTimeoutError::Disconnected) => {
                panic!("Spaik VM disconnected");
            }
        }
    }

    #[inline]
    pub fn send<V, A>(&self, name: V, args: A)
        where V: AsSym + Send + 'static,
              A: Args + Send + 'static
    {
        self.events.send(Event::Event { name: Box::new(name),
                                        args: Box::new(args) }).unwrap();
    }

    #[inline]
    pub fn fulfil<R>(&self, promise: Promise<T>, ans: R)
        where R: IntoLisp + Clone + Send + 'static
    {
        if let Some(cont) = promise.cont {
            self.events.send(Event::Promise { res: Box::new((ans,)),
                                              cont }).unwrap();
        }
    }

    #[inline]
    pub fn join(self) -> Spaik {
        self.events.send(Event::Stop).unwrap();
        self.handle.join().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use serde::{Deserialize, Serialize};
    #[cfg(feature = "derive")]
    use spaik_proc_macros::{spaikfn, Fissile, EnumCall};
    use std::{sync::{Once, atomic::{AtomicI32, Ordering}}, ops::Add};

    fn setup() {
        static INIT: Once = Once::new();
        INIT.call_once(pretty_env_logger::init);
    }

    use super::*;

    #[cfg(not(feature = "no-threading"))]
    #[cfg(not(target_arch = "wasm32"))]
    #[test]
    fn spaik_fork_send_from_rust_to_lisp() {
        setup();
        let mut vm = Spaik::new_no_core();
        vm.exec("(define init-var nil)").unwrap();
        vm.exec("(define (init) (set init-var 'init))").unwrap();
        vm.exec("(define (event-0 x) (set init-var (+ x 1)))").unwrap();
        let vm = vm.fork::<i32, ()>();
        vm.send("event-0", (123,));
        let mut vm = vm.join();
        let init_var: i32 = vm.eval("init-var").unwrap();
        assert_eq!(init_var, 124);
    }

    #[cfg(not(feature = "no-threading"))]
    #[cfg(not(target_arch = "wasm32"))]
    #[test]
    fn spaik_fork_send_from_lisp_to_rust() {
        setup();
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
        let vm = vm.fork::<Msg, ()>();
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
        #[allow(non_camel_case_types)]
        struct fns;

        #[spaikfn(fns)]
        fn funky_function(x: i32, y: i32) -> i32 {
            x + 2 + y
        }

        let mut vm = Spaik::new();
        vm.register(fns::funky_function);
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

        #[allow(non_camel_case_types)]
        struct fns;

        #[spaikfn(fns)]
        fn my_function(x: i32, y: i32, obj: &TestObj, obj2: &mut TestObj) -> i32 {
            let res = x + y.pow(2);
            obj2.x += obj.x;
            obj2.y += obj.y;
            res
        }

        #[spaikfn(fns)]
        fn obj_x(obj: &TestObj) -> f32 {
            obj.x
        }

        #[spaikfn(fns)]
        fn obj_y(obj: &TestObj) -> f32 {
            obj.y
        }

        let mut vm = Spaik::new_no_core();
        vm.register(fns::my_function);
        vm.register(fns::obj_x);
        vm.register(fns::obj_y);
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
        let dst_obj_2: TestObj = vm.obj("dst-obj").unwrap();
        assert_eq!(dst_obj_2, TestObj { x: dst_obj.x + src_obj.x,
                                        y: dst_obj.y + src_obj.y });
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

    #[cfg(feature = "derive")]
    #[test]
    fn enum_call_test() {
        #[allow(dead_code)]
        #[derive(EnumCall)]
        pub enum CallSome {
            FuncA { arg0: u32, arg1: i64, arg2: String },
            FuncB { arg0: u32, arg1: i16, arg2: &'static str },
            FuncC(u32, i8, &'static str),
        }
        let mut vm = Spaik::new_no_core();
        vm.exec("(define (func-a arg-0 arg-1 arg-2) (+ arg-0 arg-1))").unwrap();
        vm.exec("(define global 10)").unwrap();
        vm.exec("(define (func-b arg-2) (set global arg-2))").unwrap();
        let (a, b) = (10, 20);
        let r: u32 = vm.query(CallSome::FuncA {
            arg0: a, arg1: b, arg2: "lmao".to_string()
        }).unwrap();
        assert_eq!(r, a + b as u32);
        vm.cmd(CallSome::FuncB { arg0: 0, arg1: 0, arg2: "lmao" }).unwrap();
        let s: String = vm.get("global").unwrap();
        assert_eq!("lmao", &s);
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
        assert!(vm.load("self").is_err());
        vm.add_load_path("lisp");
        vm.load("self").unwrap();
        vm.add_load_path("/usr/share/spaik/lib");
        let path: Vec<String> = vm.get("sys/load-path").unwrap();
        assert_eq!(&path, &["lisp", "/usr/share/spaik/lib"]);
        vm.set("sys/load-path", ());
        assert!(vm.get::<()>("sys/load-path").is_ok());
    }

    #[test]
    #[should_panic]
    fn test_load_path_illegal_value() {
        let mut vm = Spaik::new();
        vm.set("sys/load-path", ());
        assert!(vm.get::<()>("sys/load-path").is_ok());
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
        let mut _vm = vm.fork::<(), ()>();
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
}
