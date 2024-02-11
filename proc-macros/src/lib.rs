extern crate proc_macro;

use std::fmt::{Display, format};

use proc_macro::TokenStream;
use proc_macro2::Span;
use proc_macro_crate::{FoundCrate, crate_name};
use quote::{quote, format_ident};
use syn::{parse_macro_input, ItemFn, Signature, FnArg, PatType, Pat, Ident, DeriveInput, Data, DataStruct, ImplItem, ItemImpl, ItemTrait, DataEnum, Fields, Type, ImplItemMethod};
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

#[proc_macro_attribute]
pub fn hooks(attr: TokenStream, item: TokenStream) -> TokenStream {
    let root = crate_root();
    let prefix = parse_macro_input!(attr as syn::LitStr);
    let input = parse_macro_input!(item as ItemTrait);
    let items = input.items.iter().filter_map(|item| {
        match item {
            syn::TraitItem::Method(m) => Some(m),
            _ => None,
        }
    });
    let fields = items.clone().map(|m| {
        let name = &m.sig.ident;
        quote!(#name: Option<#root::Func>)
    });
    let make_name = |ident: &Ident| format!("{}{}", prefix.value(),
                                            format!("{ident}").to_case(Case::Kebab));
    let set_fields = items.clone().map(|m| {
        let name = &m.sig.ident;
        let sname = make_name(name);
        quote!(self.#name = vm.getfn(#sname).ok())
    });
    let wrappers = items.clone().map(|m| {
        let name = &m.sig.ident;
        let fqn = make_name(name);
        let out = match &m.sig.output {
            syn::ReturnType::Default => quote!(#root::Result<#root::Ignore>),
            syn::ReturnType::Type(_, ty) => quote!(#root::Result<#ty>),
        };
        let args = m.sig.inputs.iter().map(|arg| {
            match arg {
                FnArg::Receiver(_) =>
                    unimplemented!("Cannot use self in SPAIK interface"),
                FnArg::Typed(syn::PatType { pat, ty, .. }) => if let Pat::Ident(arg) = &**pat {
                    (arg, ty)
                } else {
                    unimplemented!("Cannot use patterns in SPAIK interface")
                },
            }
        });
        let inp = args.clone().map(|(arg, ty)| quote!(#arg : #ty));
        let arg_idents = args.clone().map(|(arg, _ty)| arg);
        let body = match &m.sig.output {
            syn::ReturnType::Default => quote! {
                if let Some(f) = self.fns.#name {
                    self.vm.callfn(f, (#(#arg_idents,)*))
                } else {
                    #root::_deps::PV::Nil.try_into()
                }
            },
            syn::ReturnType::Type(_, ty) => quote! {
                if let Some(f) = self.fns.#name {
                    self.vm.callfn(f, (#(#arg_idents,)*))
                } else {
                    Err((#root::error::ErrorKind::UndefinedHook {
                        name: #root::_deps::OpName::OpStr(#fqn)
                    }).into())
                }
            },
        };
        quote! {
            pub fn #name(self, #(#inp),*) -> #out {
                #body
            }
        }
    });
    let name = input.ident;
    quote! {
        #[derive(Debug, Default)]
        struct #name {
            #(#fields),*
        }

        impl #root::LinkedEvents for #name {
            fn link_events(&mut self, vm: &mut #root::Spaik) {
                #(#set_fields);*
            }
        }

        impl<'q: 'c, 'a, 'b, 'c> crate::__spaik_call_builder::CallBuilder<'a, 'b, 'c, #name> {
            #(#wrappers)*
        }
    }.into()
}

#[proc_macro_derive(Userdata)]
pub fn derive_userdata(item: TokenStream) -> TokenStream {
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

        impl TryFrom<#root::_deps::PV> for #name {
            type Error = #root::error::Error;
            fn try_from(pv: #root::_deps::PV) -> std::result::Result<Self, Self::Error> {
                let p = pv.ref_inner()?;
                unsafe {
                    let obj = #root::_deps::cast_mut_err::<#root::_deps::Object>(p)?;
                    (*obj).take()
                }
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
                    args[#i].from_lisp_3(&mut vm.mem)
                            .map_err(|e: Error| e.arg_name(OpName::OpStr(#f_s)))?
                }
            });
            (z_name,
             quote! {
                 #p {#(#field_names : #field_try_set),*}
             })
        },
        Fields::Unnamed(ref fields) => {
            let fields_try = fields.unnamed.iter().enumerate().map(|(i, _f)| quote! {
                args[#i].from_lisp_3(&mut vm.mem).map_err(|e: Error| e.argn(#i as u32))?
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
                use #root::{_deps::*, FromLisp3};
                ArgSpec::normal(#num_fields).check(args.len().try_into()?)?;
                let common_err = |e: Error| e.sop(#name);
                let mut make_obj = || Ok(Object::new(#obj_init));
                let obj = make_obj().map_err(common_err)?;
                Ok(vm.mem.put_pv(obj))
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
                format!(":{}", i.ident.clone().unwrap()).to_case(Case::Kebab)
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
                use #root::_deps::*;
                #(#makers)*
                let boxes: [Box<dyn #root::Subr>; #num_variants] = [
                    #(Box::new(#maker_rs_names)),*
                ];
                boxes.into_iter()
            }
        }

        impl TryFrom<#root::_deps::PV> for #name {
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

struct KebabTypeName<'a>(&'a Type);

impl<'a> Display for KebabTypeName<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            Type::Array(_) => todo!(),
            Type::BareFn(_) => todo!(),
            Type::Group(_) => todo!(),
            Type::ImplTrait(_) => todo!(),
            Type::Infer(_) => todo!(),
            Type::Macro(_) => todo!(),
            Type::Never(_) => todo!(),
            Type::Paren(_) => todo!(),
            Type::Path(p) => {
                let mut had = false;
                for seg in p.path.segments.iter() {
                    if had { write!(f, "/")?; }
                    write!(f, "{}", format!("{}", seg.ident).to_case(Case::Kebab))?;
                    had = true;
                }
                Ok(())
            },
            Type::Ptr(_) => todo!(),
            Type::Reference(_) => todo!(),
            Type::Slice(_) => todo!(),
            Type::TraitObject(_) => todo!(),
            Type::Tuple(_) => todo!(),
            Type::Verbatim(_) => todo!(),
            _ => todo!(),
        }
    }
}

struct FnSig {
    nargs: usize,
    inputs: Vec<Type>,
    output: syn::ReturnType,
}

fn get_fn_type(arg: &FnArg) -> Option<FnSig> {
    match arg {
        FnArg::Receiver(_) => None,
        FnArg::Typed(pt) => match (*pt.ty).clone() {
            Type::ImplTrait(im) => match im.bounds.first().unwrap() {
                syn::TypeParamBound::Trait(tb) => {
                    let Some(tgt) = tb.path.segments.last() else { return None };
                    if tgt.ident == format_ident!("FnMut") {
                        match &tgt.arguments {
                            syn::PathArguments::None => None,
                            syn::PathArguments::AngleBracketed(_) => None,
                            syn::PathArguments::Parenthesized(s) =>
                                Some(FnSig { nargs: s.inputs.len(),
                                             inputs: s.inputs.iter().cloned().collect(),
                                             output: s.output.clone() }),
                        }
                    } else {
                        None
                    }
                },
                _ => None,
            },
            Type::Paren(_) => None,
            Type::Reference(_) => None,
            Type::TraitObject(_) => None,
            _ => None,
        },
    }
}

fn make_setargs(nargs: impl Iterator<Item = usize>) -> impl Iterator<Item = proc_macro2::TokenStream> {
     nargs.map(move |nargs| {
        let setarg = (0..nargs).map(|idx| {
            let name = format_ident!("arg_{idx}");
            quote!(let #name = args[#idx].from_lisp_3(&mut vm.mem)?;)
        });
        quote!(#(#setarg)*)
    })
}

fn make_wrappers(skip: usize, methods: impl Iterator<Item = ImplItemMethod>) -> impl Iterator<Item = proc_macro2::TokenStream> {
     methods.map(move |x: ImplItemMethod| {
        let wraps = x.sig.inputs.iter().skip(skip).enumerate().filter_map(|(idx, arg)| {
            get_fn_type(arg).map(|funk| {
                let name = format_ident!("arg_{idx}");
                let args = funk.inputs.iter().enumerate().map(|(i, ty)| {
                    let name = format_ident!("local_{i}");
                    quote!(#name : #ty)
                });
                let args_2 = (0..funk.nargs).map(|i| format_ident!("local_{i}"));
                quote! {
                    let #name: Lambda = #name;
                    let mut #name = |#(#args),*| {
                        vm.mem.lock_borrows();
                        let r = #name.on_raw(vm).call((#(#args_2,)*));
                        r
                    };
                }
            })
        });
        quote!(#(#wraps)*)
    })
}

fn make_getargs(skip: isize, methods: impl Iterator<Item = ImplItemMethod>) -> impl Iterator<Item = proc_macro2::TokenStream> {
    methods.map(move |x| {
        let nargs: u16 = (x.sig.inputs.len() as isize - skip).try_into().unwrap();
        let names = (0..nargs).map(|i| format_ident!("arg_{i}"));
        let getarg = x.sig.inputs.iter().skip(skip as usize).enumerate().map(|(idx, arg)| {
            let name = format_ident!("arg_{idx}");
            if get_fn_type(arg).is_some() {
                quote!(&mut #name)
            } else {
                quote!(#name)
            }
        });
        quote!(#(#getarg),*)
    })
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
        quote!(#(args[#idx].from_lisp_3(&mut vm.mem)?),*)
    });
    let set_args = make_setargs(methods.clone().map(|m| m.sig.inputs.len() - 1));
    let get_args = make_getargs(1, methods.clone().cloned());
    let wraps = make_wrappers(1, methods.clone().cloned());
    let num_methods = methods.clone().count();

    let st_methods = input.items.iter().filter_map(|x| if let ImplItem::Method(m) = x {
        if let Some(arg) = m.sig.inputs.first() {
            match arg {
                FnArg::Receiver(_) => None,
                FnArg::Typed(_) => Some(m),
            }
        } else {
            Some(m)
        }
    } else {
        None
    });
    let st_nargs = st_methods.clone().map(|x| x.sig.inputs.len() as u16);
    let st_mnames = st_methods.clone().map(|x| {
        let mname = x.sig.ident.clone();
        quote!(#name::#mname)
    });
    let st_rs_names = st_methods.clone().map(|x| format_ident!("{}_Subr", x.sig.ident.clone()));
    let st_rs_names_2 = st_rs_names.clone();
    let tmp_rs_names = st_methods.clone().map(|x| format_ident!("tmp_{}", x.sig.ident.clone()));
    let tmp_rs_names_2 = tmp_rs_names.clone();
    let st_names = st_methods.clone().map(|x| {
        format!("{}/{}",
                KebabTypeName(&name),
                format!("{}", x.sig.ident).to_case(Case::Kebab))
    });
    let st_args = st_nargs.clone().map(|nargs| {
        let idx = 0..(nargs as usize);
        quote!(#(args[#idx].from_lisp_3(&mut vm.mem)?),*)
    });
    let st_set_args = make_setargs(st_methods.clone().map(|m| m.sig.inputs.len()));
    let st_get_args = make_getargs(0, st_methods.clone().cloned());
    let st_wraps = make_wrappers(0, st_methods.clone().cloned());

    let out = quote! {
        #input

        unsafe impl #root::MethodSet<#spec> for #name {
            fn methods() -> &'static [(&'static str, #root::_deps::ArgSpec, #root::_deps::ObjMethod)] {
                use #root::{Lispify, FromLisp, FromLisp3, _deps::*};
                const METHODS: [(&'static str, #root::_deps::ArgSpec, #root::_deps::ObjMethod); #num_methods] =
                [#((#kwnames, ArgSpec::normal(#nargs), |this: *mut u8, vm: &mut R8VM, args: &[PV]| unsafe {
                    ArgSpec::normal(#nargs).check(args.len() as u16)?;
                    #set_args
                    #wraps
                    (*(this as *mut #name)).#mnames(#get_args).lispify(&mut vm.mem)
                })),*];
                &METHODS
            }
        }

        #[allow(non_camel_case_types)]
        impl #root::SubrSet<#spec> for #name {
            fn subrs() -> impl Iterator<Item = Box<dyn #root::Subr>> {
                use #root::{Lispify, FromLisp, FromLisp3, _deps::*};
                #(struct #st_rs_names;
                  unsafe impl #root::Subr for #st_rs_names {
                      fn call(&mut self, vm: &mut R8VM, args: &[PV]) -> #root::Result<PV> {
                          use #root::{Lispify, FromLisp, FromLisp3, _deps::*};
                          ArgSpec::normal(#st_nargs).check(args.len() as u16)?;
                          unsafe {
                              #st_set_args
                              #st_wraps
                              #st_mnames(#st_get_args).lispify(&mut vm.mem)
                          }
                      }
                      fn name(&self) -> &'static str {
                          #st_names
                      }
                  }
                )*
                #(let #tmp_rs_names: Box<dyn #root::Subr> = Box::new(#st_rs_names_2);)*
                [#(#tmp_rs_names_2),*].into_iter()
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
