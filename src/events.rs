use std::marker::PhantomData;

use crate::{Spaik, Userdata, Ignore, nkgc::PV};

#[derive(Debug, Default)]
struct Example {
    dead: Option<crate::Func>,
    ready: Option<crate::Func>,
}

pub trait LinkedEvents {
    fn link_events(&mut self, vm: &mut Spaik);
}

trait CallSetup<'q: 'c, 'a, 'b, 'c> {
    type Out: Interface<'q, 'a, 'b, 'q>;
    fn with<G>(self, global: &'q mut G) -> Self::Out where G: Userdata;
}

trait Interface<'q: 'c, 'a, 'b, 'c>: CallSetup<'q, 'a, 'b, 'c> {
    fn dead(&mut self, id: u32) -> crate::Result<()>;
    fn ready(&mut self) -> crate::Result<()>;
}

impl LinkedEvents for Example {
    fn link_events(&mut self, vm: &mut Spaik) {
        self.dead = vm.getfn("event/dead").ok();
        self.ready = vm.getfn("event/ready").ok();
    }
}

impl Example {
    fn on<'a, 'b>(&'a mut self, vm: &'b mut Spaik)
                  -> impl Interface<'b, 'a, 'b, 'b>
    {
        struct On<'a, 'b, 'c> {
            fns: &'a mut Example,
            vm: &'b mut Spaik,
            _ph: PhantomData<&'c ()>
        }
        impl<'q: 'c, 'a, 'b, 'c> Interface<'q, 'a, 'b, 'c> for On<'a, 'b, 'c> {
            fn dead(&mut self, id: u32) -> crate::Result<()> {
                if let Some(f) = self.fns.dead {
                    self.vm.callfn(f, (id,))
                } else {
                    PV::Nil.try_into()
                }
            }

            fn ready(&mut self) -> crate::Result<()> {
                if let Some(f) = self.fns.ready {
                    self.vm.callfn(f, ())
                } else {
                    PV::Nil.try_into()
                }
            }
        }
        impl<'q: 'c, 'a, 'b, 'c> CallSetup<'q, 'a, 'b, 'c> for On<'a, 'b, 'c> {
            type Out = On<'a, 'b, 'q>;
            fn with<G>(self, global: &'q mut G) -> Self::Out where G: Userdata {
                self.vm.set_resource(global);
                On { fns: self.fns, vm: self.vm, _ph: Default::default() }
            }
        }
        On { fns: self, vm, _ph: Default::default() }
    }
}

#[cfg(test)]
mod tests {
    use spaik_proc_macros::Obj;

    use super::*;

    #[test]
    fn call_builder() {
        #[derive(Debug, Obj)]
        #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
        struct Test { x: i32 }
        let mut ex = Example::default();
        let mut vm = Spaik::new_no_core();
        let mut test1 = Test { x: 1 };
        let mut test2 = Test { x: 2 };
        let mut v = ex.on(&mut vm)
                      .with(&mut test1)
                      .with(&mut test2);
        v.dead(1).ok();
    }
}
