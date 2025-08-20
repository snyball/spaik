use std::sync::mpsc::{Sender, Receiver, TryRecvError, RecvTimeoutError};
use std::thread::JoinHandle;
use std::time::Duration;
use std::ops::{Deref, DerefMut};
use std::fmt::Debug;

use serde::de::DeserializeOwned;

use crate::nkgc::PV;
use crate::r8vm::{R8VM, ArgSpec};
use crate::{Args, AsSym, SPV, Builtin, deserialize, nkgc, FromLisp, Subr, Result, Spaik, IntoLisp};

pub enum Event {
    Promise { res: Box<dyn Args + Send>, cont: SPV },
    Event { name: Box<dyn AsSym + Send>,
            args: Box<dyn Args + Send> },
    Stop,
}

/// Promise made to `SpaikPlug`
#[derive(Debug)]
#[must_use = "A promise made should be a promise kept"]
pub struct Promise<T> {
    pub(crate) msg: Box<T>,
    pub(crate) cont: Option<SPV>,
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
    fn from_lisp(self, mem: &mut nkgc::Arena) -> Result<Promise<T>> {
        with_ref!(self, Cons(p) => {
            let msg = (*p).car;
            let cont = (*p).cdr;
            let msg = deserialize::from_pv(msg)?;
            if cont.bt_type_of() != Builtin::Continuation {
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
pub struct SpaikPlug<T> {
    pub(crate) promises: Receiver<Promise<T>>,
    pub(crate) events: Sender<Event>,
    pub(crate) handle: JoinHandle<Spaik>,
}

impl<T> SpaikPlug<T> {
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
