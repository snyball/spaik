extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro2::Span;
use proc_macro_crate::{FoundCrate, crate_name};
use quote::{quote, format_ident};
use syn::{parse_macro_input, ItemFn, Signature, FnArg, PatType, Pat, Ident, DeriveInput, Data, DataStruct, FieldsNamed, ImplItem, ItemImpl, ItemTrait, DataEnum, Fields, Field, Type};
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

    let out = quote! {
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

fn maker(p: proc_macro2::TokenStream,
         rs_struct_name: Ident,
         name: &str,
         z_name: &str,
         fields: Fields) -> proc_macro2::TokenStream
{
    let root = crate_root();
    let fields_it = fields.iter();
    let num_fields: u16 = fields_it.clone().count().try_into().expect("too many fields");
    let (z_name, obj_init) = match fields {
        Fields::Named(ref fields) => {
            let fields_it = fields.named.iter();
            let field_names = fields_it.clone().map(|f| f.ident.clone().expect("Identifier"));
            let field_try_set = field_names.clone().enumerate().map(|(i, f)| {
                let f_s = format!("{f}");
                quote! {
                    args[#i].try_into()
                            .map_err(|e: Error| e.arg_name(OpName::OpStr(#f_s)))?
                }
            });
            (z_name,
             quote! {
                 #p {#(#field_names : #field_try_set),*}
             })
        },
        Fields::Unnamed(ref fields) => {
            let fields_try = fields.unnamed.iter().enumerate().map(|(i, f)| quote! {
                args[#i].try_into().map_err(|e: Error| e.argn(#i as u32))?
            });
            (name, quote! { #p(#(#fields_try),*) })
        },
        Fields::Unit => (name, quote! { #p }),
    };
    quote! {
        struct #rs_struct_name;
        unsafe impl #root::Subr for #rs_struct_name {
            fn call(&mut self, vm: &mut #root::_deps::R8VM,
                    args: &[#root::_deps::PV]) -> #root::Result<#root::_deps::PV> {
                use #root::_deps::*;
                ArgSpec::normal(#num_fields).check(args.len().try_into()?)?;
                let common_err = |e: Error| e.sop(#name);
                let make_obj = || Ok(Object::new(#obj_init));
                Ok(vm.mem.put_pv(make_obj().map_err(common_err)?))
            }
            fn name(&self) -> &'static str {
                #z_name
            }
        }
    }
}

struct DataRepr {
    ident: Ident,
    fields: Fields
}

#[proc_macro_derive(Obj)]
pub fn derive_obj(item: TokenStream) -> TokenStream {
    let root = crate_root();
    let input = parse_macro_input!(item as DeriveInput);
    let name = input.ident.clone();
    let data = input.data.clone();
    let name_s = format!("{}", name).to_case(Case::Kebab);
    let (prefix, mkpath, data_reprs): (_, _, Vec<_>) = match data {
        Data::Enum(DataEnum {variants, ..}) => (
            format!("{name_s}/"),
            Some(|var_ident| quote! { #name::#var_ident }),
            variants.into_iter().map(|v| DataRepr {
                ident: v.ident,
                fields: v.fields
            }).collect()
        ),
        Data::Struct(DataStruct {fields, ..}) => (
            "".to_string(),
            None,
            vec![DataRepr { fields, ident: name.clone() }]
        ),
        Data::Union(_) => unimplemented!("Bare unions cannot be shared with SPAIK"),
    };
    let variants = data_reprs.iter();
    let variant_macro_strs = variants.clone().filter_map(|v| {
        if let Fields::Named(fs) = &v.fields {
            let keys = fs.named.iter().map(|i| {
                format!(":{}", i.ident.clone().unwrap())
            });
            let variant = format!("{prefix}{}",
                                  format!("{}", v.ident).to_case(Case::Kebab));
            let maker_fn = format!("<ζ>::make-{variant}");
            Some(quote! {
                #root::_deps::MacroNewVariant {
                    variant: #variant,
                    variant_maker: #maker_fn,
                    key_strings: &[#(#keys),*]
                }
            })
        } else {
            None
        }
    });
    let num_macros = variants.clone()
                             .filter(|v| matches!(v.fields, Fields::Named(_)))
                             .count();
    let num_variants = variants.clone().count();
    let maker_rs_names = variants.clone().map(|var| {
        format_ident!("Make{}", var.ident)
    });
    let makers = variants.clone().zip(maker_rs_names.clone()).map(|(var, rs_name)| {
        let nicename = format!("{prefix}{}", var.ident.to_string().to_case(Case::Kebab));
        let zname = format!("<ζ>::make-{nicename}");
        let var_ident = var.ident.clone();
        maker(mkpath.map(|f| f(var_ident)).unwrap_or(quote! { #name }),
              rs_name,
              &nicename,
              &zname,
              var.fields.clone())
    });

    let out = quote! {
        impl #root::KebabTypeName for #name {
            fn kebab_type_name() -> &'static str {
                #name_s
            }
        }

        impl #root::Enum for #name {
            fn enum_macros() -> impl Iterator<Item = #root::MacroNew> {
                const VARIANTS: [#root::_deps::MacroNewVariant; #num_macros] = [
                    #(#variant_macro_strs),*
                ];
                #root::_deps::into_macro_news(&VARIANTS)
            }

            fn enum_constructors() -> impl Iterator<Item = Box<dyn #root::Subr>> {
                use crate::_deps::*;
                #(#makers)*
                let boxes: [Box<dyn #root::Subr>; #num_variants] = [
                    #(Box::new(#maker_rs_names)),*
                ];
                boxes.into_iter()
            }
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
pub fn methods(attr: TokenStream, item: TokenStream) -> TokenStream {
    let root = crate_root();
    let input = parse_macro_input!(item as ItemImpl);
    let spec = parse_macro_input!(attr as syn::Type);
    let name = input.self_ty.clone();
    let methods = input.items.iter().filter_map(|x| if let ImplItem::Method(m) = x {
        m.sig.inputs.first().and_then(|arg| match arg {
            FnArg::Receiver(_) => Some(m),
            FnArg::Typed(_) => None,
        })
    } else {
        None
    });
    let nargs = methods.clone().map(|x| x.sig.inputs.len() as u16 - 1);
    let mnames = methods.clone().map(|x| x.sig.ident.clone());
    let kwnames = methods.clone().map(|x| format!(":{}", x.sig.ident).to_case(Case::Kebab));
    let args = nargs.clone().map(|nargs| {
        let idx = 0..(nargs as usize);
        quote!(#(args[#idx].try_into()?),*)
    });

    let out = quote! {
        #input

        unsafe impl #root::MethodSet<#spec> for #name {
            fn methods() -> &'static [(&'static str, #root::_deps::ObjMethod)] {
                use #root::{Lispify, FromLisp, _deps::*};
                &[#((#kwnames, |this: *mut u8, vm: &mut R8VM, args: &[PV]| unsafe {
                    ArgSpec::normal(#nargs).check(args.len() as u16)?;
                    (*(this as *mut #name)).#mnames(#args).lispify(&mut vm.mem)
                })),*]
            }
        }
    };

    out.into()
}

#[proc_macro_attribute]
pub fn export(_attr: TokenStream, item: TokenStream) -> TokenStream {
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
