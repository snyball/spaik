extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro2::Span;
use proc_macro_crate::{FoundCrate, crate_name};
use quote::{quote, format_ident};
use syn::{parse_macro_input, ItemFn, Signature, FnArg, PatType, Pat, Ident};

fn crate_root() -> proc_macro2::TokenStream {
    let found_crate = crate_name("spaik")
        .expect("my-crate is present in `Cargo.toml`");

    match found_crate {
        FoundCrate::Itself => quote!( crate ),
        FoundCrate::Name(name) => {
            let ident = Ident::new(&name, Span::call_site());
            quote!( #ident )
        }
    }
}

fn spaik_fn_impl(spaik_root: proc_macro2::TokenStream, item: TokenStream) -> TokenStream {
    let inp = parse_macro_input!(item as syn::ItemFn);
    let ItemFn { attrs, vis, sig, block } = inp;
    let Signature { ident, inputs, .. } = sig.clone();
    let obj_ident = format_ident!("{}_obj", ident);
    let ident_str = format!("{}", ident).replace('_', "-");
    let inputs_it = inputs.iter().map(|input| match input {
        FnArg::Receiver(_) => unimplemented!(),
        FnArg::Typed(PatType { pat, .. }) => match *pat.clone() {
            Pat::Ident(name) => name,
            _ => unimplemented!(),
        }
    });
    let inputs_it_2 = inputs_it.clone();
    let inputs_it_idx_1 = inputs_it.clone().enumerate().map(|(idx, _)| idx);
    let inputs_it_idx_2 = inputs_it.clone().enumerate().map(|(idx, _)| idx as u32);
    let nargs = inputs.len() as u16;
    let out = quote! {
        #(#attrs)* #vis #sig {
            #block
        }

        #[allow(non_camel_case_types)]
        #[derive(Clone)]
        struct #obj_ident {}

        impl #obj_ident {
            #[inline]
            pub fn new() -> Box<dyn #spaik_root::subrs::Subr> {
                Box::new(#obj_ident {})
            }
        }

        unsafe impl #spaik_root::subrs::Subr for #obj_ident {
            fn call(&mut self,
                    vm: &mut #spaik_root::r8vm::R8VM,
                    args: &[#spaik_root::nkgc::PV])
                    -> Result<#spaik_root::nkgc::PV,
                              #spaik_root::error::Error>
            {
                use #spaik_root::r8vm::ArgSpec;
                use #spaik_root::error::Error;
                const SPEC: ArgSpec = ArgSpec::normal(#nargs);
                SPEC.check(Default::default(), args.len() as u16)?;
                #(let #spaik_root::nkgc::ObjRef(#inputs_it)
                  =
                  args[#inputs_it_idx_1].try_into()
                  .map_err(|e: Error| e.argn(#inputs_it_idx_2))?;
                )*
                #ident(#(#inputs_it_2,)*).into_pv(&mut vm.mem)
            }

            fn name(&self) -> &'static str {
                #ident_str
            }
        }
    };

    out.into()
}

#[proc_macro_attribute]
pub fn spaikfn(_attr: TokenStream, item: TokenStream) -> TokenStream {
    spaik_fn_impl(crate_root(), item)
}
