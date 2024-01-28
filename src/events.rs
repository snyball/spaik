use std::marker::PhantomData;

use crate::{Spaik, Userdata, nkgc::PV};

#[macro_export]
macro_rules! def_call_builder {
    () => {
        mod __spaik_call_builder {
            pub struct CallBuilder<'a, 'b, 'c, T> {
                pub fns: &'a mut T,
                pub vm: &'b mut $crate::Spaik,
                _ph: std::marker::PhantomData<&'c ()>
            }

            impl<'q: 'c, 'a, 'b, 'c, T> CallBuilder<'a, 'b, 'c, T> {
                pub fn with_resource<G>(self, global: &'q mut G) -> CallBuilder<'a, 'b, 'q, T>
                    where G: $crate::Userdata
                {
                    unsafe { self.vm.set_resource(global) };
                    CallBuilder { fns: self.fns, vm: self.vm, _ph: Default::default() }
                }
            }

            pub trait IntoCallBuilder: Sized {
                fn on<'a, 'b>(&'a mut self, vm: &'b mut $crate::Spaik) -> CallBuilder<'a, 'b, 'b, Self>;
            }

            impl<T> IntoCallBuilder for T where T: $crate::LinkedEvents {
                fn on<'a, 'b>(&'a mut self, vm: &'b mut $crate::Spaik) -> CallBuilder<'a, 'b, 'b, T> {
                    CallBuilder { fns: self, vm, _ph: Default::default() }
                }
            }
        }
    };
}

pub use crate::__spaik_call_builder::*;

pub trait LinkedEvents {
    fn link_events(&mut self, vm: &mut Spaik);
}

#[cfg(test)]
mod tests {
    use spaik_proc_macros::{Obj, methods};

    use super::*;

    #[cfg(feature = "derive")]
    #[test]
    fn call_builder() {
        use spaik_proc_macros::hooks;

        #[hooks("events/")]
        trait Example {
            fn dead(id: u32);
            fn ready();
            fn thing(x: i32) -> i32;
        }

        #[derive(Debug, Obj)]
        #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
        struct Test { x: i32 }
        const A: i32 = 1337;
        const B: i32 = 420;
        const C: i32 = 42;
        #[methods(())]
        impl Test {
            fn funk(&self, x: i32) -> i32 {
                x + A + self.x
            }
        }
        let mut ex = Example::default();
        // let mut ex2 = Example2::default();
        let mut vm = Spaik::new_no_core();
        let mut test1 = Test { x: 0 };
        let mut test2 = Test { x: C };
        vm.defmethods::<Test, ()>();
        vm.bind_resource_fns::<Test, ()>(None);
        vm.exec("(define (events/thing x) (test/funk x))").unwrap();
        ex.link_events(&mut vm);
        let v = ex.on(&mut vm)
                  .with_resource(&mut test1)
                  .with_resource(&mut test2);
        let res = v.thing(B).unwrap();
        assert_eq!(res, A + B + C);
        test1.x;
        assert!(vm.exec("(test/funk 2)").is_err());
    }
}
