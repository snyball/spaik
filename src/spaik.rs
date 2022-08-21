//! SPAIK public API

use std::fmt::Debug;
use std::sync::mpsc::{Sender, channel, Receiver, TryRecvError, RecvTimeoutError};
use std::thread::{self, JoinHandle};
use std::time::Duration;

use serde::Deserialize;
use serde::de::DeserializeOwned;

use crate::compile::Builtin;
use crate::deserialize;
use crate::nuke::Fissile;
use crate::r8vm::{R8VM, Args, ArgSpec};
use crate::sym_db::SymDB;
use crate::error::Error;
use crate::nkgc::{SymID, PV, ObjRef, SPV};
use crate::subrs::{Subr, IntoLisp, Ignore, RefIntoLisp};

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
    fn vm_into(self, vm: &mut R8VM) -> SymID {
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
    fn vm_into(&self, vm: &mut R8VM) -> SymID {
        *self
    }
}

impl Spaik {
    pub fn new() -> Result<Spaik, Error> {
        let mut vm = Spaik {
            vm: R8VM::new()
        };
        vm.load("stdlib")?;
        Ok(vm)
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

    pub fn get_clone<V, T>(&mut self, var: V) -> Result<T, Error>
        where V: VMRefInto<SymID>, T: Fissile + 'static + Clone
    {
        self.get_ref_mut(var).map(|rf: &mut T| (*rf).clone())
    }

    pub fn get_ref<V, T>(&mut self, var: V) -> Result<&T, Error>
        where V: VMRefInto<SymID>, T: Fissile + 'static
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
        where V: VMRefInto<SymID>, T: Fissile + 'static
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
     * Load library
     *
     * # Arguments
     *
     * - `lib` : If the library is stored at "name.lisp", then `lib` should be
     *           "name" as either a string or symbol
     */
    pub fn load<V>(&mut self, lib: V) -> Result<SymID, Error>
        where V: VMRefInto<SymID>
    {
        let lib = lib.vm_into(&mut self.vm);
        self.vm.load(lib)
    }

    pub fn call<V, A, R>(&mut self, sym: V, args: A) -> Result<R, Error>
        where V: VMRefInto<SymID>,
              A: Args,
              R: TryFrom<PV, Error = Error>,
    {
        let sym = sym.vm_into(&mut self.vm);
        self.vm.call(sym, &args).and_then(|pv| {
            let r = pv.try_into()?;
            Ok(r)
        })
    }

    pub fn run<V, A>(&mut self, sym: V, args: A) -> Result<(), Error>
        where V: VMRefInto<SymID>,
              A: Args,
    {
        let _r: Ignore = self.call(sym, args)?;
        Ok(())
    }

    /**
     * Perform a full GC collection, this may finish a currently ongoing collection
     * and start a new one afterwards.
     */
    pub fn gc(&mut self) {
        self.vm.mem.full_collection()
    }

    // TODO
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

pub enum Event {
    Promise { res: Box<dyn Args>, cont: SPV },
    Event { name: Box<dyn VMRefInto<SymID>>, args: Box<dyn Args> },
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
    where T: DeserializeOwned + Clone + Send + 'static + Debug
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
    fn into_subr(self) -> Box<dyn Subr> { Box::new(self) }
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

#[cfg(test)]
mod tests {
    use spaik_proc_macros::{spaikfn, Fissile};
    use std::sync::Once;

    fn setup() {
        static INIT: Once = Once::new();
        INIT.call_once(pretty_env_logger::init);
    }

    use super::*;

    #[test]
    fn spaik_fork_send_from_rust_to_lisp() {
        setup();
        let mut vm = Spaik::new().unwrap();
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
        let mut vm = Spaik::new().unwrap();
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
        let mut vm = Spaik::new().unwrap();
        let result: i32 = vm.eval("(+ 2 3)").unwrap();
        assert_eq!(result, 5);
        let result: i16 = vm.eval("(+ 2 3)").unwrap();
        assert_eq!(result, 5);
        let result: f32 = vm.eval("(+ 2.0 3)").unwrap();
        assert_eq!(result, 5.0);
    }

    #[test]
    fn api_func_call() {
        let mut vm = Spaik::new().unwrap();
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

        let mut vm = Spaik::new().unwrap();
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

        let mut vm = Spaik::new().unwrap();
        vm.register(my_function_obj());
        vm.register(obj_x_obj());
        vm.register(obj_y_obj());
        let src_obj = TestObj { x: 1.0, y: 3.0 };
        let dst_obj = TestObj { x: 1.0, y: 2.0 };
        vm.set("src-obj", src_obj.clone());
        vm.set("dst-obj", dst_obj.clone());
        vm.exec("(my-function 1 1 src-obj dst-obj)").unwrap();
        vm.exec("(println dst-obj)").unwrap();
        let x: f32 = vm.eval("(obj-x dst-obj)").unwrap();
        let y: f32 = vm.eval("(obj-y dst-obj)").unwrap();
        assert_eq!(x, 2.0);
        assert_eq!(y, 5.0);
        let dst_obj_2: TestObj = vm.get_clone("dst-obj").unwrap();
        assert_eq!(dst_obj_2, TestObj { x: dst_obj.x + src_obj.x,
                                        y: dst_obj.y + src_obj.y });
        let dst_obj_2: &TestObj = vm.get_ref("dst-obj").unwrap();
        assert_eq!(*dst_obj_2, TestObj { x: dst_obj.x + src_obj.x,
                                         y: dst_obj.y + src_obj.y });
        let dst_obj_2: &TestObj = vm.get_ref_mut("dst-obj").unwrap();
        assert_eq!(*dst_obj_2, TestObj { x: dst_obj.x + src_obj.x,
                                         y: dst_obj.y + src_obj.y });
        // (set (dst-obj :x) )
        // (dst-obj :x)
    }
}
