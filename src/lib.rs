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
//! fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     let mut vm = Spaik::new();
//!     // Evaluate strings
//!     vm.exec(r#"(println "code")"#)?;
//!     // Optionaly retrieve the result
//!     let res: f32 = vm.eval(r#"(sqrt (+ 1 2))"#)?;
//!     Ok(())
//! }
//! ```

#![allow(clippy::trivial_regex)]
#![allow(clippy::upper_case_acronyms)]
// FIXME: Write documentation for the unsafe functions.
#![allow(clippy::missing_safety_doc)]

// FIXME: DO NOT COMMIT THESE TO VERSION CONTROL
#![allow(unused_variables)]
#![allow(dead_code)]

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
pub(crate) mod perr;
#[macro_use]
pub(crate) mod chasm;
#[macro_use]
pub(crate) mod nkgc;
#[macro_use]
pub(crate) mod r8vm;
#[macro_use]
pub(crate) mod ast;
pub(crate) mod opt;
pub(crate) mod sintern;
pub(crate) mod fmt;
pub(crate) mod sym_db;
pub(crate) mod subrs;
pub(crate) mod compile;
pub(crate) mod sexpr_parse;
pub(crate) mod tok;
pub(crate) mod nuke;
pub(crate) mod module;
pub(crate) mod deserialize;
pub(crate) mod limits;
pub(crate) mod math;
pub(crate) mod comp;

#[cfg(feature = "repl")]
pub mod repl;
pub mod scratch;

pub use spaik_proc_macros::{EnumCall, spaikfn, Fissile};
pub use nkgc::{SPV, SymID, ObjRef};
pub use nuke::Gc;
pub type Str = Arc<str>;
pub use sym_db::SymDB;
pub use nuke::Userdata;

/// This module makes it possible to interact with SPAIK internals.
///
/// Everything in `raw::*` which is not re-exported by the top level spaik
/// module is implicitly marked as unstable and can change upon the next release
/// even in SemVer minor releases. `spaik::raw` is *not* a stable public API.
///
/// Using functions from this module incorrectly can cause memory-unsafety issues.
///
/// Now with that out of the way: Happy Hacking!
pub mod raw {
    /// # R8VM: The Rodent Virtual Machine
    ///
    /// Trivia: In Norwegian, R8 is pronounced as "rotte", which means "rat".
    pub mod r8vm { pub use crate::r8vm::*; }
    /// # The Nuclear Garbage Collector
    pub mod nkgc { pub use crate::nkgc::*; }
    /// # The Nuclear Allocator
    pub mod nuke { pub use crate::nuke::*; }
    /// # Subroutine routines
    pub mod subrs { pub use crate::subrs::*; }
    /// # Compiler
    pub mod compile { pub use crate::compile::*; }
    /// # String interning
    pub mod sintern { pub use crate::sintern::*; }
    /// # ChASM /ˈkæz(ə)m/, an assembler
    pub mod chasm { pub use crate::chasm::*; }
    /// # LispFmt and friends
    pub mod fmt { pub use crate::fmt::*; }
    /// # SymDB
    pub mod sym_db { pub use crate::sym_db::*; }
}

use std::borrow::Cow;
use std::fmt::Debug;
use std::sync::Arc;
use std::sync::mpsc::{Sender, channel, Receiver, TryRecvError, RecvTimeoutError};
use std::thread::{self, JoinHandle};
use std::time::Duration;
use std::ops::{Deref, DerefMut};

use serde::de::DeserializeOwned;

pub use crate::compile::Builtin;
pub use crate::nuke::Fissile;
pub use crate::error::Error as IError;
use crate::r8vm::R8VM;
pub use crate::r8vm::{Args, ArgSpec, EnumCall};
use crate::nkgc::PV;
pub use crate::subrs::{Subr, IntoLisp, FromLisp, Ignore, IntoSubr};

pub mod prelude {
    pub use super::{SymDB, SymID, Subr, IntoLisp, FromLisp,
                    Ignore, IntoSubr, SpaikPlug, Spaik, EnumCall};
}

pub trait FmtErr<T> where T: Sized {
    /// Format an internal VM runtime error as a string, by replacing symbol IDs
    /// with their strings.
    fn fmterr(self, db: &dyn SymDB) -> Result<T, Box<dyn std::error::Error>>;

    /// Like `Result::unwrap` but first runs `FmtErr::fmterr` on the error.
    fn fmt_unwrap(self, db: &dyn SymDB) -> T;
}

impl<T> FmtErr<T> for Result<T, IError> {
    #[inline]
    fn fmterr(self, db: &dyn SymDB) -> Result<T, Box<dyn std::error::Error>> {
        match self {
            Ok(x) => Ok(x),
            Err(e) => Err(e.to_string(db).into())
        }
    }

    #[inline]
    fn fmt_unwrap(self, db: &dyn SymDB) -> T {
        self.fmterr(db).unwrap()
    }
}

/// Formatted error message
pub struct Error {
    source: Box<IError>,
    message: String,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.message)
    }
}

impl Debug for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl Error {
    fn from_source(src: IError, db: &dyn SymDB) -> Error {
        Error {
            message: src.to_string(db),
            source: Box::new(src),
        }
    }

    pub fn src(&self) -> IError {
        (*self.source).clone()
    }
}

impl std::error::Error for Error {}

/// A SPAIK Context
pub struct Spaik {
    vm: R8VM
}

pub trait AsSym {
    fn as_sym(&self, vm: &mut R8VM) -> SymID;
}

impl AsSym for &str {
    fn as_sym(&self, vm: &mut R8VM) -> SymID {
        vm.mem.put_sym(self)
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

    /// Register a subroutine (function) with the vm
    #[inline]
    pub fn register(&mut self, func: impl Subr) {
        self.set(func.name(), func.into_subr());
    }

    /// Move `obj` into the vm as `var`.
    #[inline]
    pub fn set(&mut self, var: impl AsSym, obj: impl IntoLisp) {
        let var = var.as_sym(&mut self.vm);
        self.vm.set(var, obj).unwrap();
    }

    /// Return a clone of `var`
    #[inline]
    pub fn get<R>(&mut self, var: impl AsSym) -> Result<R, Error>
        where PV: FromLisp<R>
    {
        let name = var.as_sym(&mut self.vm);
        let idx = self.vm.get_env_global(name)
                         .ok_or(error!(UndefinedVariable, var: name))
                         .map_err(|e| Error::from_source(e, self))?;
        self.vm.mem.get_env(idx)
                   .from_lisp(&mut self.vm.mem)
                   .map_err(|e| Error::from_source(e, self))
    }

    /// Get a reference to a user-defined object type stored in the vm.
    #[inline]
    pub fn objref<T>(&mut self, var: impl AsSym) -> Result<*const T, Error>
        where T: Userdata
    {
        self.objref_mut(var).map(|rf| rf as *const T)
    }

    /// Get a clone of a user-defined object type stored in the vm.
    #[inline]
    pub fn obj<T: Userdata>(&mut self, var: impl AsSym) -> Result<T, Error> {
        self.objref_mut(var).map(|rf: *mut T| unsafe { (*rf).clone() })
    }

    /// Retrieve a variable as a mutable reference.
    ///
    /// # Arguments
    ///
    /// - `var` : Variable name
    #[inline]
    pub fn objref_mut<T>(&mut self, var: impl AsSym) -> Result<*mut T, Error>
        where T: Userdata
    {
        let name = var.as_sym(&mut self.vm);
        let idx = self.vm.get_env_global(name)
                         .ok_or(error!(UndefinedVariable, var: name))
                         .map_err(|e| Error::from_source(e, self))?;
        let ObjRef(x): ObjRef<*mut T> = self.vm.mem.get_env(idx)
                                                   .try_into()
                                                   .map_err(|e| Error::from_source(e, self))?;
        Ok(x)
    }

    /// Run an expression.
    ///
    /// # Arguments
    ///
    /// - `expr` : Lisp expression
    #[inline]
    pub fn eval<R>(&mut self, expr: impl AsRef<str>) -> Result<R, Error>
        where PV: FromLisp<R>
    {
        self.vm.eval(expr.as_ref())
               .and_then(|pv| pv.from_lisp(&mut self.vm.mem))
               .map_err(|e| Error::from_source(e, self))
    }

    /// Run an expression and ignore the result (unless there was an error.)
    ///
    /// # Arguments
    ///
    /// - `expr` : Lisp expression
    #[inline]
    pub fn exec(&mut self, expr: impl AsRef<str>) -> Result<(), Error> {
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
    pub fn load(&mut self, lib: impl AsSym) -> Result<SymID, Error> {
        let lib = lib.as_sym(&mut self.vm);
        self.vm.load(lib).map_err(|e| Error::from_source(e, self))
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
    pub fn load_with<S>(&mut self, src_path: S, lib: SymID, code: S) -> Result<SymID, Error>
        where S: AsRef<str>
    {
        let lib = lib.as_sym(&mut self.vm);
        self.vm.load_with(src_path, lib, code).map_err(|e| Error::from_source(e, self))
    }

    /// Call a function by-enum and return the result
    ///
    /// Use `Spaik::cmd` if don't care about the result.
    #[inline]
    pub fn query<R>(&mut self, enm: impl EnumCall) -> Result<R, Error>
        where PV: FromLisp<R>
    {
        self.vm.call_by_enum(enm)
               .and_then(|pv| pv.from_lisp(&mut self.vm.mem))
               .map_err(|e| Error::from_source(e, self))
    }

    /// Call a function by-enum and ignore the result
    ///
    /// Use `Spaik::query` if you need the result.
    #[inline]
    pub fn cmd(&mut self, enm: impl EnumCall) -> Result<(), Error> {
        let _: Ignore = self.query(enm)?;
        Ok(())
    }

    /// Call a function by-name an args and return the result.
    ///
    /// Use `Spaik::run` if don't care about the result.
    #[inline]
    pub fn call<R>(&mut self, sym: impl AsSym, args: impl Args) -> Result<R, Error>
        where PV: FromLisp<R>
    {
        let sym = sym.as_sym(&mut self.vm);
        self.vm.call(sym, args)
               .and_then(|pv| pv.from_lisp(&mut self.vm.mem))
               .map_err(|e| Error::from_source(e, self))
    }

    /// Call a function by-name an args and ignore the result.
    ///
    /// Use `Spaik::call` if you need the result.
    #[inline]
    pub fn run(&mut self, sym: impl AsSym, args: impl Args) -> Result<(), Error> {
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
                               ans: A) -> Result<R, Error>
        where PV: FromLisp<R>,
              A: IntoLisp + Clone + Send + 'static,
    {
        if let Some(cont) = pr.cont {
            self.vm.apply_spv(cont, (ans,))
                   .and_then(|pv| pv.from_lisp(&mut self.vm.mem))

        } else {
            PV::Nil.from_lisp(&mut self.vm.mem)
        }
        .map_err(|e| Error::from_source(e, self))
    }

    /// Add to load path, this influences where `Spaik::load` will search for
    /// spaik files.
    ///
    /// # Panics
    ///
    /// Panics if the `sys/load-path` variable is not defined, or is not a
    /// vector.
    pub fn add_load_path(&mut self, path: impl AsRef<str>) {
        let p = self.vm.var(Builtin::SysLoadPath.sym())
                       .fmt_unwrap(&self.vm);
        let s = self.vm.mem.put(path.as_ref().to_string());
        with_ref_mut!(p, Vector(v) => {
            (*v).push(s);
            Ok(())
        }).fmt_unwrap(&self.vm);
    }

    /// Move the VM off-thread and return a `SpaikPlug` handle for IPC.
    pub fn fork<T, Cmd>(mut self) -> SpaikPlug<T, Cmd>
        where T: DeserializeOwned + Send + Debug + Clone + 'static,
              Cmd: EnumCall + Send + 'static
    {
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
                            log::error!("{}", e.to_string(&self.vm));
                        }
                    }
                    Event::Event { name, args } => {
                        let sym = name.as_sym(&mut self.vm);
                        let res = self.vm.call(sym, args).and_then(|pv| {
                            let r: Ignore = pv.try_into()?;
                            Ok(r)
                        });
                        if let Err(e) = res {
                            log::error!("{}", e.to_string(&self.vm));
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

impl SymDB for Spaik {
    #[inline]
    fn name(&self, sym: SymID) -> std::borrow::Cow<str> {
        Cow::Borrowed(self.vm.mem.symdb.name(sym).unwrap())
    }

    #[inline]
    fn put_sym(&mut self, name: &str) -> SymID {
        self.vm.mem.symdb.put_sym(name)
    }
}

impl EnumCall for () {
    fn name(&self, _mem: &mut nkgc::Arena) -> SymID {
        unimplemented!()
    }

    fn pushargs(self, _args: &[SymID], _mem: &mut nkgc::Arena) -> Result<(), IError> {
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

impl<T> FromLisp<Promise<T>> for PV where T: DeserializeOwned {
    fn from_lisp(self, mem: &mut nkgc::Arena) -> Result<Promise<T>, IError> {
        with_ref!(self, Cons(p) => {
            let msg = (*p).car;
            let cont = (*p).cdr;
            let msg = deserialize::from_pv(msg, mem)?;
            if cont.type_of() != Builtin::Continuation.sym() {
                return err!(TypeError,
                            expect: Builtin::Continuation.sym(),
                            got: cont.type_of());
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
    fn call(&mut self, vm: &mut R8VM, args: &[PV]) -> Result<PV, IError> {
        let (msg, r, cont) = match args {
            [x, y] => (deserialize::from_pv(*x, &vm.mem)
                       .map_err(|e| e.argn(1).op(Builtin::ZSendMessage.sym()))?,
                       *x,
                       Some(vm.mem.make_extref(*y))),
            [x] => (deserialize::from_pv(*x, &vm.mem)
                    .map_err(|e| e.argn(1).op(Builtin::ZSendMessage.sym()))?,
                    *x,
                    None),
            _ => ArgSpec::opt(1, 1).check(Builtin::ZSendMessage.sym(),
                                          args.len() as u16)
                                   .map(|_| -> ! { unreachable!() })?

        };
        self.sender.send(Promise { msg, cont })?;
        Ok(r)
    }
    fn name(&self) -> &'static str { "<ζ>::send-message" }
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

#[macro_export]
macro_rules! args {
    ($($arg:expr),*) => {
        &[$(&$arg as &dyn RefIntoLisp),*]
    };
}

#[cfg(test)]
mod tests {
    use serde::Deserialize;
    use spaik_proc_macros::{spaikfn, Fissile, EnumCall};
    use std::sync::Once;

    fn setup() {
        static INIT: Once = Once::new();
        INIT.call_once(pretty_env_logger::init);
    }

    use crate::error::ErrorKind;

    use super::*;

    #[test]
    fn spaik_fork_send_from_rust_to_lisp() {
        setup();
        let mut vm = Spaik::new();
        vm.exec("(defvar init-var nil)").unwrap();
        vm.exec("(defun init () (set init-var 'init))").unwrap();
        vm.exec("(defun event-0 (x) (set init-var (+ x 1)))").unwrap();
        let vm = vm.fork::<i32, ()>();
        vm.send("event-0", (123,));
        let mut vm = vm.join();
        let init_var: i32 = vm.eval("init-var").unwrap();
        assert_eq!(init_var, 124);
    }

    #[test]
    fn spaik_fork_send_from_lisp_to_rust() {
        setup();
        #[derive(Debug, Deserialize, Clone, PartialEq, Eq)]
        #[serde(rename_all = "kebab-case")]
        enum Msg {
            Test { id: i32 },
        }
        let mut vm = Spaik::new();
        vm.exec("(defvar init-var nil)").unwrap();
        vm.exec("(defun init () (set init-var 'init))").unwrap();
        vm.exec(r#"(defun event-0 (x)
                     (let ((res (await '(test :id 1337))))
                       (set init-var (+ res x 1))))"#).unwrap();
        let vm = vm.fork::<Msg, ()>();
        let ev0_arg = 123;
        vm.send("event-0", (ev0_arg,));
        let p = vm.recv_timeout(Duration::from_secs(1)).expect("timeout");
        assert_eq!(p.get(), &Msg::Test { id: 1337 });
        let fulfil_res = 31337;
        vm.fulfil(p, fulfil_res);
        let mut vm = vm.join();
        let init_var: i32 = vm.eval("init-var").unwrap();
        assert_eq!(init_var, fulfil_res + ev0_arg + 1);
    }

    #[test]
    fn api_eval_add_numbers() {
        let mut vm = Spaik::new();
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

    #[test]
    fn register_fn_mutate_struct() {
        #[derive(Debug, Clone, PartialEq, PartialOrd, Fissile)]
        pub struct TestObj {
            x: f32,
            y: f32,
        }

        #[derive(Debug, Clone, PartialEq, PartialOrd, Fissile)]
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

        let mut vm = Spaik::new();
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
        vm.exec("(println dst-obj)").unwrap();
        let x: f32 = vm.eval("(obj-x dst-obj)").unwrap();
        let y: f32 = vm.eval("(obj-y dst-obj)").unwrap();
        assert_eq!(x, 2.0);
        assert_eq!(y, 5.0);
        let dst_obj_2: TestObj = vm.obj("dst-obj").unwrap();
        assert_eq!(dst_obj_2, TestObj { x: dst_obj.x + src_obj.x,
                                        y: dst_obj.y + src_obj.y });
        // let dst_obj_2: *const TestObj = vm.objref("dst-obj").unwrap();
        // assert_eq!(unsafe { *dst_obj_2 }, TestObj { x: dst_obj.x + src_obj.x,
        //                                  y: dst_obj.y + src_obj.y });
        // let dst_obj_2: *mut TestObj = vm.objref_mut("dst-obj").unwrap();
        // assert_eq!(unsafe { *dst_obj_2 }, TestObj { x: dst_obj.x + src_obj.x,
        //                                  y: dst_obj.y + src_obj.y });
        let expr = "(obj-y wrong-obj)";
        let e = match vm.exec(expr).map_err(|e| e.src()) {
            Ok(_) => panic!("Expression should fail: {expr}"),
            Err(IError {ty: ErrorKind::Traceback { tb }, .. }) => tb.err.ty,
            Err(e) => panic!("Unexpected error for {expr}: {}", e.to_string(&vm)),
        };
        dbg!(&e);
        assert!(matches!(e, ErrorKind::STypeError { .. }));
        drop(vm);
        dbg!(&perst_ref);
        perst_ref.with(|r| r.x = 3.0);
        dbg!(&perst_ref);
    }

    #[test]
    fn enum_call_test() {
        #[allow(dead_code)]
        #[derive(EnumCall)]
        pub enum CallSome {
            FuncA { arg0: u32, arg1: i64, arg2: String },
            FuncB { arg0: u32, arg1: i16, arg2: &'static str },
            FuncC(u32, i8, &'static str),
        }
        let mut vm = Spaik::new();
        vm.exec("(defun func-a (arg-0 arg-1 arg-2) (+ arg-0 arg-1))").unwrap();
        vm.exec("(defvar global 10)").unwrap();
        vm.exec("(defun func-b (arg-2) (set global arg-2))").unwrap();
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
        let pr: Result<Promise<String>, _> = vm.call("test-yield", ());
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

    #[test]
    #[should_panic]
    fn test_illegal_fork() {
        #[derive(Debug, Clone, PartialEq, PartialOrd, Fissile)]
        pub struct TestObj {
            x: f32,
            y: f32,
        }

        let mut vm = Spaik::new();
        vm.set("test-obj", TestObj { x: 10.0, y: 20.0 });
        let _rf: Gc<TestObj> = vm.get("test-obj").unwrap();
        let mut _vm = vm.fork::<(), ()>();
    }
}
