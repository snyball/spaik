use std::marker::PhantomData;

use spaik_proc_macros::hooks;

use crate::{Spaik, Userdata, nkgc::PV};

pub struct CallBuilder<'a, 'b, 'c, T> {
    fns: &'a mut T,
    vm: &'b mut Spaik,
    _ph: PhantomData<&'c ()>
}

impl<'q: 'c, 'a, 'b, 'c, T> CallBuilder<'a, 'b, 'c, T> {
    pub fn with_resource<G>(self, global: &'q mut G) -> CallBuilder<'a, 'b, 'q, T>
        where G: Userdata
    {
        unsafe { self.vm.set_resource(global) };
        CallBuilder { fns: self.fns, vm: self.vm, _ph: Default::default() }
    }
}

pub trait IntoCallBuilder: Sized {
    fn on<'a, 'b>(&'a mut self, vm: &'b mut Spaik) -> CallBuilder<'a, 'b, 'b, Self>;
}

impl<T> IntoCallBuilder for T where T: LinkedEvents {
    fn on<'a, 'b>(&'a mut self, vm: &'b mut Spaik) -> CallBuilder<'a, 'b, 'b, T> {
        CallBuilder { fns: self, vm, _ph: Default::default() }
    }
}

#[hooks("events/")]
trait Example {
    fn dead(id: u32);
    fn ready();
    fn thing(x: i32) -> i32;
}

pub trait LinkedEvents {
    fn link_events(&mut self, vm: &mut Spaik);
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
        // let mut ex2 = Example2::default();
        let mut vm = Spaik::new_no_core();
        let mut test1 = Test { x: 1 };
        let mut test2 = Test { x: 2 };
        let mut v = ex.on(&mut vm)
                      .with_resource(&mut test1)
                      .with_resource(&mut test2);
        v.ready().ok();
        test1.x;
    }
}
