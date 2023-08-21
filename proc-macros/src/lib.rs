extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro2::Span;
use proc_macro_crate::{FoundCrate, crate_name};
use quote::{quote, format_ident};
use syn::{parse_macro_input, ItemFn, Signature, FnArg, PatType, Pat, Ident, DeriveInput, Data, DataStruct, FieldsNamed, ImplItem, ItemImpl, DataEnum, ItemTrait};
use convert_case::{Case, Casing};

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

fn spaik_fn_impl(namespace: Ident, spaik_root: proc_macro2::TokenStream, item: TokenStream) -> TokenStream {
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
    use std::sync::atomic::AtomicUsize;
    use std::sync::atomic::Ordering;
    static COUNT: AtomicUsize = AtomicUsize::new(0);
    let count = COUNT.fetch_add(1, Ordering::SeqCst);
    let anon_namespace = format_ident!("__spaik_fn_anonymous_{count}");
    let out = quote! {
        #(#attrs)* #vis #sig {
            #block
        }

        mod #anon_namespace {
            #[allow(non_camel_case_types)]
            #[derive(Clone)]
            pub(super) struct #obj_ident;
        }

        impl #namespace {
            #[allow(non_upper_case_globals)]
            pub const #ident: #anon_namespace::#obj_ident =
                #anon_namespace::#obj_ident;
        }

        unsafe impl #spaik_root::Subr for #anon_namespace::#obj_ident {
            fn call(&mut self,
                    vm: &mut #spaik_root::_deps::R8VM,
                    args: &[#spaik_root::_deps::PV])
                    -> core::result::Result<#spaik_root::_deps::PV,
                                            #spaik_root::error::Error>
            {
                use #spaik_root::_deps::ArgSpec;
                use #spaik_root::error::Error;
                const SPEC: ArgSpec = ArgSpec::normal(#nargs);
                SPEC.check(args.len() as u16)?;
                #(let #spaik_root::_deps::ObjRef(#inputs_it)
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

        impl From<#anon_namespace::#obj_ident> for Box<dyn #spaik_root::Subr> {
            fn from(x: #anon_namespace::#obj_ident) -> Self {
                Box::new(x)
            }
        }
    };

    out.into()
}

#[proc_macro]
pub fn kebabify(inp: TokenStream) -> TokenStream {
    let ident = parse_macro_input!(inp as Ident);
    let kebab = format!("{ident}").to_case(Case::Kebab);
    quote!(#kebab).into()
}

#[proc_macro_attribute]
pub fn spaikfn(attr: TokenStream, item: TokenStream) -> TokenStream {
    let namespace = parse_macro_input!(attr as Ident);
    spaik_fn_impl(namespace, crate_root(), item)
}

#[proc_macro_attribute]
pub fn spaikiface(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemImpl);
    let _items = input.items
                      .clone()
                      .into_iter()
                      .filter_map(|i| match i {
                          ImplItem::Method(m) => Some(m),
                          _ => None,
                      })
                      .map(|_m| {
                      });

    let out = quote! {
        #input
    };
    out.into()
}

#[proc_macro_attribute]
pub fn spaiklib(_attr: TokenStream, _item: TokenStream) -> TokenStream {
    quote!().into()
}

#[proc_macro_derive(Fissile)]
pub fn derive_fissile(item: TokenStream) -> TokenStream {
    let root = crate_root();
    let input = parse_macro_input!(item as DeriveInput);
    let name = input.ident.clone();
    let data = input.data.clone();
    let fields = match data {
        Data::Struct(DataStruct {
            fields: syn::Fields::Named(FieldsNamed { named, .. }), ..
        }) => named,
        _ => unimplemented!()
    }.into_iter();
    let field_names = fields.clone().map(|f| f.ident.clone().expect("Identifier"));
    let field_kws = fields.map(|f| format!(":{}", f.ident.expect("Identifier")));

    let out = quote! {
        impl #root::_deps::Traceable for #name {
            fn trace(&self, _gray: &mut Vec<*mut #root::_deps::NkAtom>) {}
            fn update_ptrs(&mut self, _reloc: &#root::_deps::PtrMap) {}
        }

        impl #root::_deps::LispFmt for #name {
            fn lisp_fmt(&self,
                        _visited: &mut #root::_deps::VisitSet,
                        f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "({}", stringify!(#name))?;
                #( write!(f, " {} {:?}", #field_kws, self.#field_names)?; )*
                write!(f, ")")
            }
        }

        impl #root::Userdata for #name {}

        impl #root::IntoLisp for #name {
            fn into_pv(self, mem: &mut #root::_deps::Arena)
                       -> core::result::Result<#root::_deps::PV, #root::error::Error>
            {
                Ok(mem.put_pv(#root::_deps::Object::new(self)))
            }
        }
    };

    out.into()
}

#[proc_macro_attribute]
pub fn spaik_export(_attr: TokenStream, item: TokenStream) -> TokenStream {
    use convert_case::{Case, Casing};
    let root = crate_root();
    let input = parse_macro_input!(item as ItemImpl);
    let name = input.self_ty.clone();
    let methods = input.items.iter().filter_map(|x| if let ImplItem::Method(m) = x {
        Some(m)
    } else {
        None
    });
    let method_names = methods.clone().map(|x| x.sig.ident.clone());
    let method_names2 = method_names.clone();
    let method_lisp_names = methods.clone().map(|x| format!(":{}", x.sig.ident).to_case(Case::Kebab));
    let method_m_argc = methods.clone().map(|m| m.sig.inputs.len() as u16);
    let m_idents = methods.clone().map(|m| {
        m.sig.inputs.iter().filter_map(|i| match i {
            FnArg::Receiver(_) => None,
            FnArg::Typed(t) => if let Pat::Ident(i) = *t.pat.clone() {
                Some(i.ident)
            } else {
                None
            },
        })
    });
    let setargs = m_idents.clone().map(|idents| {
        let idents2 = idents.clone();
        quote! {
            #(let #idents = #idents2.from_lisp(&mut vm.mem)?;)*
        }
    });
    let args = m_idents.clone().map(|idents| quote!(#(#idents),*));
    let args2 = args.clone();

    let out = quote! {
        #input

        #[allow(non_camel_case_types)]
        unsafe impl #root::Subr for #name {
            fn call(&mut self, vm: &mut #root::_deps::R8VM, args: &[#root::_deps::PV]) -> std::result::Result<#root::_deps::PV, #root::error::Error> {
                use #root::{Lispify, FromLisp};
                enum M { #(#method_names),* }
                let op = args.get(0)
                             .ok_or_else(|| #root::error::Error::new(
                                 #root::error::ErrorKind::TypeError {
                                     expect: #root::Builtin::Callable,
                                     got: #root::Builtin::Struct
                                 }
                             ).bop(#root::Builtin::Apply))?
                             .sym()
                             .map_err(|e| e.bop(#root::Builtin::MethodCall))?;
                match op.as_ref() {
                    #(
                        #method_lisp_names => match &args[1..] {
                            &[#args] => {
                                #setargs
                                self.#method_names2(#args2).lispify(&mut vm.mem)
                            }
                            _ => Err(#root::error::Error::new(
                                #root::error::ErrorKind::ArgError {
                                    expect: #root::_deps::ArgSpec::normal(#method_m_argc),
                                    got_num: (args.len()-1) as u32
                                }
                            ))
                        }
                    ),*
                    _ => return Err(#root::error::Error::new(
                        #root::error::ErrorKind::NoSuchMethod {
                            strucc: self.name(), method: op.into()
                        }
                    ))
                }
            }

            fn name(&self) -> &'static str {
                std::any::type_name::<Self>()
            }
        }
    };

    out.into()
}

#[proc_macro_attribute]
pub fn interface(_attr: TokenStream, item: TokenStream) -> TokenStream {
    
    let _root = crate_root();
    let input = parse_macro_input!(item as ItemTrait);

    let out = quote! {
        #input
    };

    out.into()
}
