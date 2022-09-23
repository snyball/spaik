//! SPAIK public API

use std::borrow::Cow;
use std::fmt::Debug;
use std::sync::mpsc::{Sender, channel, Receiver, TryRecvError, RecvTimeoutError};
use std::thread::{self, JoinHandle};
use std::time::Duration;

use serde::de::DeserializeOwned;

use crate::compile::Builtin;
use crate::deserialize;
use crate::nuke::Fissile;
use crate::r8vm::{R8VM, Args, ArgSpec, EnumCall};
use crate::sym_db::SymDB;
use crate::error::Error;
use crate::nkgc::{SymID, PV, ObjRef, SPV};
use crate::subrs::{Subr, IntoLisp, Ignore, IntoSubr};

/// A Spaik Context
pub struct Spaik {
    vm: R8VM
}

pub trait VMInto<T> {
    fn vm_into(self, vm: &mut R8VM) -> T;
}

impl VMInto<SymID> for &str {
    fn vm_into(self, vm: &mut R8VM) -> SymID {
        vm.mem.put_sym(self)
    }
}

impl VMInto<SymID> for SymID {
    fn vm_into(self, _vm: &mut R8VM) -> SymID {
        self
    }
}

pub trait VMRefInto<T> {
    fn vm_into(&self, vm: &mut R8VM) -> T;
}

impl VMRefInto<SymID> for &str {
    fn vm_into(&self, vm: &mut R8VM) -> SymID {
        vm.mem.put_sym(self)
    }
}

impl VMRefInto<SymID> for SymID {
    fn vm_into(&self, _vm: &mut R8VM) -> SymID {
        *self
    }
}

impl Spaik {
    pub fn new() -> Spaik {
        let mut vm = Spaik {
            vm: R8VM::new()
        };
        vm.vm.load_stdlib();
        vm
    }

    pub fn register(&mut self, func: impl Subr) {
        self.set(func.name(), func.into_subr());
    }

    pub fn set<V, T>(&mut self, var: V, obj: T)
        where V: VMRefInto<SymID>, T: IntoLisp
    {
        let var = var.vm_into(&mut self.vm);
        self.vm.set(var, obj).unwrap();
    }

    pub fn get<V, R>(&mut self, var: V) -> Result<R, Error>
        where V: VMRefInto<SymID>, R: TryFrom<PV, Error = Error>
    {
        let name = var.vm_into(&mut self.vm);
        let idx = self.vm.get_env_global(name)
                         .ok_or(error!(UndefinedVariable, var: name))?;
        self.vm.mem.get_env(idx).try_into()
    }

    pub fn get_ref<V, T>(&mut self, var: V) -> Result<&T, Error>
        where V: VMRefInto<SymID>, T: Fissile
    {
        self.get_ref_mut(var).map(|rf| &*rf)
    }

    /**
     * Retrieve a variable as a mutable reference.
     *
     * # Arguments
     *
     * - `var` : Variable name
     */
    pub fn get_ref_mut<V, T>(&mut self, var: V) -> Result<&mut T, Error>
        where V: VMRefInto<SymID>, T: Fissile
    {
        let name = var.vm_into(&mut self.vm);
        let idx = self.vm.get_env_global(name)
                         .ok_or(error!(UndefinedVariable, var: name))?;
        let ObjRef(x): ObjRef<&mut T> = self.vm.mem.get_env(idx).try_into()?;
        Ok(x)
    }

    /**
     * Run an expression.
     *
     * # Arguments
     *
     * - `expr` : Lisp expression
     */
    pub fn eval<E, R>(&mut self, expr: E) -> Result<R, Error>
        where E: AsRef<str>,
              R: TryFrom<PV, Error = Error>
    {
        self.vm.eval(expr.as_ref())
               .and_then(|pv| pv.try_into())
    }

    /**
     * Run an expression and ignore the result (unless there was an error.)
     *
     * # Arguments
     *
     * - `expr` : Lisp expression
     */
    pub fn exec<E>(&mut self, expr: E) -> Result<(), Error>
        where E: AsRef<str>
    {
        let _: Ignore = self.eval(expr)?;
        Ok(())
    }

    /**
     * Load library from the load-path, by default this is `./lisp/`.
     *
     * # Arguments
     *
     * - `lib` : If the library is stored at `"<name>.lisp"`, then `lib` should be
     *           `<name>` as either a string or symbol
     */
    pub fn load<V>(&mut self, lib: V) -> Result<SymID, Error>
        where V: VMRefInto<SymID>
    {
        let lib = lib.vm_into(&mut self.vm);
        self.vm.load(lib)
    }

    /**
     * Load a SPAIK library from a string, this is useful both for embedding code
     * into your binary with e.g `load_with(x, y, include_str!(...))` or when
     * loading from a virtual filesystem.
     *
     * # Arguments
     *
     * - `src_path` : File-system path to the `.lisp` file, needed for
     *                source-file/line error messages.
     * - `lib` : Library symbol name, i.e the argument to `(load ...)`
     * - `code` : The source-code contents inside `src_path`
     */
    pub fn load_with<V, S>(&mut self, src_path: S, lib: SymID, code: S) -> Result<SymID, Error>
        where V: VMRefInto<SymID>,
              S: AsRef<str>
    {
        let lib = lib.vm_into(&mut self.vm);
        self.vm.load_with(src_path, lib, code)
    }

    pub fn query<R>(&mut self, enm: impl EnumCall) -> Result<R, Error>
        where R: TryFrom<PV, Error = Error>
    {
        self.vm.call_by_enum(enm).and_then(|pv| pv.try_into())
    }

    pub fn cmd(&mut self, enm: impl EnumCall) -> Result<(), Error> {
        let _: Ignore = self.query(enm)?;
        Ok(())
    }

    pub fn call<V, A, R>(&mut self, sym: V, args: A) -> Result<R, Error>
        where V: VMRefInto<SymID>,
              A: Args,
              R: TryFrom<PV, Error = Error>,
    {
        let sym = sym.vm_into(&mut self.vm);
        self.vm.call(sym, &args).and_then(|pv| pv.try_into())
    }

    pub fn run<V, A>(&mut self, sym: V, args: A) -> Result<(), Error>
        where V: VMRefInto<SymID>,
              A: Args,
    {
        let _: Ignore = self.call(sym, args)?;
        Ok(())
    }

    /**
     * Perform a full GC collection, this may finish a currently ongoing collection
     * and start a new one afterwards.
     */
    pub fn gc(&mut self) {
        self.vm.mem.full_collection()
    }

    pub fn fork<T: DeserializeOwned + Send + Debug + Clone + 'static>(mut self) -> SpaikPlug<T> {
        let (rx_send, tx_send) = channel::<Promise<T>>();
        let (rx_run, tx_run) = channel();
        let handle = thread::spawn(move || {
            self.register(send_message { sender: rx_send });
            self.run("init", ()).unwrap();
            loop {
                let ev: Event = tx_run.recv().unwrap();
                match ev {
                    Event::Stop => break,
                    Event::Promise { res, cont } => {
                        let res = self.vm.apply_spv(cont, &*res);
                        if let Err(e) = res {
                            log::error!("{}", e.to_string(&self.vm));
                        }
                    }
                    Event::Event { name, args } => {
                        let sym = name.vm_into(&mut self.vm);
                        let res = self.vm.call(sym, &*args).and_then(|pv| {
                            let r: Ignore = pv.try_into()?;
                            Ok(r)
                        });
                        if let Err(e) = res {
                            log::error!("{}", e.to_string(&self.vm));
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

impl SymDB for Spaik {
    fn name(&self, sym: SymID) -> std::borrow::Cow<str> {
        Cow::Borrowed(self.vm.mem.symdb.name(sym).unwrap())
    }

    fn put_sym(&mut self, name: &str) -> SymID {
        self.vm.mem.symdb.put_sym(name)
    }
}

pub enum Event {
    Promise { res: Box<dyn Args>, cont: SPV },
    Event { name: Box<dyn VMRefInto<SymID>>, args: Box<dyn Args> },
    // Ping(u64),
    Stop,
}
unsafe impl Send for Event {}

#[derive(Debug)]
#[must_use = "A promise made should be a promise kept"]
pub struct Promise<T> {
    msg: Box<T>,
    cont: Option<SPV>,
}

impl<T> Promise<T> {
    pub fn get(&self) -> &T {
        &self.msg
    }

    pub fn get_mut(&mut self) -> &mut T {
        &mut self.msg
    }
}

pub enum Ctrl {
    Pong(u64),
}

#[derive(Debug)]
#[must_use = "A promise made should be a promise kept"]
pub enum Response<T> {
    Promise(Promise<T>),
    Ctrl(),
}

pub struct SpaikPlug<T> {
    promises: Receiver<Promise<T>>,
    events: Sender<Event>,
    handle: JoinHandle<Spaik>,
}

#[derive(Clone, Debug)]
#[allow(non_camel_case_types)]
pub struct send_message<T>
    where T: DeserializeOwned + Clone + Send
{
    sender: Sender<Promise<T>>,
}

unsafe impl<'de, T> Subr for send_message<T>
    where T: DeserializeOwned + Clone + Send + 'static + Debug + Sized
{
    fn call(&mut self, vm: &mut R8VM, args: &[PV]) -> Result<PV, Error> {
        let (msg, r, cont) = match &args[..] {
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

impl<T> SpaikPlug<T> {
    pub fn recv(&mut self) -> Option<Promise<T>>
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

    pub fn recv_timeout(&mut self, timeout: Duration) -> Option<Promise<T>>
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

    pub fn send<V, A>(&mut self, name: V, args: A)
        where V: VMRefInto<SymID> + 'static,
              A: Args + 'static
    {
        self.events.send(Event::Event { name: Box::new(name),
                                        args: Box::new(args) }).unwrap();
    }

    pub fn fulfil<R>(&mut self, promise: Promise<T>, ans: R)
        where R: IntoLisp + Clone + 'static
    {
        if let Some(cont) = promise.cont {
            self.events.send(Event::Promise { res: Box::new((ans,)),
                                              cont }).unwrap();
        }
    }

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

pub trait LispUnwrap<T> {
    fn slap(self, db: &dyn SymDB) -> T;
}

impl<T> LispUnwrap<T> for Result<T, Error> {
    fn slap(self, db: &dyn SymDB) -> T {
        match self {
            Ok(x) => x,
            Err(e) => panic!("{}", e.to_string(db))
        }
    }
}

#[cfg(test)]
mod tests {
    use serde::Deserialize;
    use spaik_proc_macros::{spaikfn, Fissile, EnumCall};
    use std::{sync::Once};

    fn setup() {
        static INIT: Once = Once::new();
        INIT.call_once(pretty_env_logger::init);
    }

    use crate::{error::{Source, ErrorKind}, r8vm::Traceback};

    use super::*;

    #[test]
    fn spaik_fork_send_from_rust_to_lisp() {
        setup();
        let mut vm = Spaik::new();
        vm.exec("(defvar init-var nil)").unwrap();
        vm.exec("(defun init () (set init-var 'init))").unwrap();
        vm.exec("(defun event-0 (x) (set init-var (+ x 1)))").unwrap();
        let mut vm = vm.fork::<i32>();
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
        vm.exec("(load 'async)").unwrap();
        vm.exec("(defvar init-var nil)").unwrap();
        vm.exec("(defun init () (set init-var 'init))").unwrap();
        vm.exec(r#"(defun event-0 (x)
                     (let ((res (await '(test :id 1337))))
                       (set init-var (+ res x 1))))"#).unwrap();
        let mut vm = vm.fork::<Msg>();
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
        #[spaikfn]
        fn funky_function(x: i32, y: i32) -> i32 {
            x + 2 + y
        }

        let mut vm = Spaik::new();
        vm.register(funky_function_obj());
        let result: i32 = vm.eval("(funky-function 2 8)").unwrap();
        assert_eq!(result, 12);

        // FIXME: The vm_call_with! macro should eventually support this:
        // let result: i32 = vm.call("funky-function", (4, 8)).unwrap();
        // assert_eq!(result, 14);
    }

    #[test]
    fn register_fn_mutate_struct() {
        #[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Fissile)]
        pub struct TestObj {
            x: f32,
            y: f32,
        }

        #[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Fissile)]
        pub struct TestObj2 {
            x: f32,
        }

        #[spaikfn]
        fn my_function(x: i32, y: i32, obj: &TestObj, obj2: &mut TestObj) -> i32 {
            let res = x + y.pow(2);
            obj2.x += obj.x;
            obj2.y += obj.y;
            res
        }

        #[spaikfn]
        fn obj_x(obj: &TestObj) -> f32 {
            obj.x
        }

        #[spaikfn]
        fn obj_y(obj: &TestObj) -> f32 {
            obj.y
        }

        let mut vm = Spaik::new();
        vm.register(my_function_obj());
        vm.register(obj_x_obj());
        vm.register(obj_y_obj());
        let src_obj = TestObj { x: 1.0, y: 3.0 };
        let dst_obj = TestObj { x: 1.0, y: 2.0 };
        let wrong_obj = TestObj2 { x: 10.0 };
        vm.set("wrong-obj", wrong_obj);
        vm.set("src-obj", src_obj.clone());
        vm.set("dst-obj", dst_obj.clone());
        vm.exec("(my-function 1 1 src-obj dst-obj)").unwrap();
        vm.exec("(println dst-obj)").unwrap();
        let x: f32 = vm.eval("(obj-x dst-obj)").unwrap();
        let y: f32 = vm.eval("(obj-y dst-obj)").unwrap();
        assert_eq!(x, 2.0);
        assert_eq!(y, 5.0);
        let dst_obj_2: TestObj = vm.get_ref::<&str, TestObj>("dst-obj").unwrap().clone();
        assert_eq!(dst_obj_2, TestObj { x: dst_obj.x + src_obj.x,
                                        y: dst_obj.y + src_obj.y });
        let dst_obj_2: &TestObj = vm.get_ref("dst-obj").unwrap();
        assert_eq!(*dst_obj_2, TestObj { x: dst_obj.x + src_obj.x,
                                         y: dst_obj.y + src_obj.y });
        let dst_obj_2: &TestObj = vm.get_ref_mut("dst-obj").unwrap();
        assert_eq!(*dst_obj_2, TestObj { x: dst_obj.x + src_obj.x,
                                         y: dst_obj.y + src_obj.y });
        let expr = "(obj-y wrong-obj)";
        let e = match vm.exec(expr) {
            Ok(_) => panic!("Expression should fail: {expr}"),
            Err(Error {ty: ErrorKind::Traceback { tb }, .. }) => tb.err.ty,
            Err(e) => panic!("Unexpected error for {expr}: {}", e.to_string(&vm)),
        };
        dbg!(&e);
        assert!(matches!(e, ErrorKind::STypeError { .. }))
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
        vm.exec("(defun func-a (arg-0 arg-1 arg-2) (+ arg-0 arg-1))").slap(&vm);
        vm.exec("(defvar global 10)").slap(&vm);
        vm.exec("(defun func-b (arg-2) (set global arg-2))").slap(&vm);
        let (a, b) = (10, 20);
        let r: u32 = vm.query(CallSome::FuncA {
            arg0: a, arg1: b, arg2: "lmao".to_string()
        }).slap(&vm);
        assert_eq!(r, a + b as u32);
        vm.cmd(CallSome::FuncB { arg0: 0, arg1: 0, arg2: "lmao" }).slap(&vm);
        let s: String = vm.get("global").slap(&vm);
        assert_eq!("lmao", &s);
    }
}
