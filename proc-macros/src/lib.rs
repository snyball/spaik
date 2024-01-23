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

#[proc_macro_derive(Record)]
pub fn derive_record(item: TokenStream) -> TokenStream {
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
    let field_kws = fields.clone().map(|f| format!(":{}", f.ident.expect("Identifier")));
    let field_try_set = field_names.clone().enumerate().map(|(i, f)| {
        let f_s = format!("{f}");
        quote! {
            args[#i].try_into()
                    .map_err(|e: Error| e.arg_name(OpName::OpStr(#f_s)))?
        }
    });
    let field_inits = fields.clone().map(|_| quote! { None });
    let argn: usize = fields.clone().count();
    let argn_u16: u16 = argn.try_into().expect("too many arguments");
    let sp_name = format!("{name}").to_case(Case::Kebab);
    let make_s = format!("<ζ>::make-{sp_name}");
    let macro_s = format!("<ξζ>::make-{sp_name}");
    let name_s = format!("{sp_name}");
    let name_s_2 = name_s.clone();
    let out = quote! {
        impl #root::FieldAccess for #name {} // TODO
        impl #root::MethodCall for #name {} // TODO
        impl #root::KebabTypeName for #name {
            fn kebab_type_name() -> &'static str { #name_s_2 }
        }
        impl TryFrom<#root::PV> for #name {
            type Error = #root::error::Error;
            fn try_from(pv: #root::_deps::PV) -> std::result::Result<Self, Self::Error> {
                let p = pv.ref_inner()?;
                unsafe {
                    let obj = #root::_deps::cast_mut_err::<#root::_deps::Object>(p)?;
                    (*obj).take()
                }
            }
        }
        impl #root::Record for #name {
            fn record_macro() -> impl #root::Subr {
                use #root::_deps::*;
                #[derive(Default)]
                struct Construct {
                    keys: Vec<SymRef>,
                    make_fn: Option<SymRef>,
                }
                unsafe impl #root::Subr for Construct {
                    fn call(&mut self, vm: &mut R8VM, args: &[PV]) -> #root::Result<PV> {
                        if self.keys.is_empty() {
                            self.keys = (&[#(#field_kws),*]).into_iter().map(|key| {
                                vm.sym(key)
                            }).collect();
                        }
                        let name = self.make_fn.get_or_insert_with(|| vm.sym(#make_s));
                        let mut out: [Option<PV>; #argn] = [#(#field_inits),*];
                        into_init(vm, #name_s, name, args, &self.keys[..], &mut out)
                    }

                    fn name(&self) -> &'static str {
                        #macro_s
                    }
                }
                Construct::default()
            }

            fn record_constructor() -> impl #root::Subr {
                use #root::_deps::*;
                struct Construct;
                unsafe impl #root::Subr for Construct {
                    fn call(&mut self, vm: &mut R8VM, args: &[PV]) -> #root::Result<PV> {
                        ArgSpec::normal(#argn_u16).check(args.len().try_into()?)?;
                        let common_err = |e: Error| e.sop(#name_s);
                        let make_obj = || Ok(Object::new(#name {
                            #(#field_names : #field_try_set),*
                        }));
                        Ok(vm.mem.put_pv(make_obj().map_err(common_err)?))
                    }

                    fn name(&self) -> &'static str {
                        #make_s
                    }
                }
                Construct
            }
        }
    };

    out.into()
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
                write!(f, "{:?}", self)
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
pub fn export(_attr: TokenStream, item: TokenStream) -> TokenStream {
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
