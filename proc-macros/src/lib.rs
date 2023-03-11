extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro2::Span;
use proc_macro_crate::{FoundCrate, crate_name};
use quote::{quote, format_ident};
use syn::{parse_macro_input, ItemFn, Signature, FnArg, PatType, Pat, Ident, DeriveInput, Data, DataStruct, FieldsNamed, ImplItem, ItemImpl, DataEnum};

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

        unsafe impl #spaik_root::subrs::Subr for #anon_namespace::#obj_ident {
            fn call(&mut self,
                    vm: &mut #spaik_root::raw::r8vm::R8VM,
                    args: &[#spaik_root::raw::nkgc::PV])
                    -> core::result::Result<#spaik_root::raw::nkgc::PV,
                                            #spaik_root::error::Error>
            {
                use #spaik_root::raw::r8vm::ArgSpec;
                use #spaik_root::error::Error;
                const SPEC: ArgSpec = ArgSpec::normal(#nargs);
                SPEC.check(Default::default(), args.len() as u16)?;
                #(let #spaik_root::raw::nkgc::ObjRef(#inputs_it)
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

        impl From<#anon_namespace::#obj_ident> for Box<dyn #spaik_root::subrs::Subr> {
            fn from(x: #anon_namespace::#obj_ident) -> Self {
                Box::new(x)
            }
        }
    };

    out.into()
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

#[proc_macro_derive(EnumCall)]
pub fn derive_enum_call(item: TokenStream) -> TokenStream {
    use convert_case::{Case, Casing};
    let root = crate_root();
    let input = parse_macro_input!(item as DeriveInput);
    let name = input.ident.clone();
    let _name_s = input.ident.to_string().to_case(Case::Kebab);
    let data = input.data.clone();
    let fields = match data {
        Data::Enum(DataEnum {
            variants, ..
        }) => variants,
        _ => unimplemented!()
    }.into_iter();

    let variant = fields.clone().map(|f| f.ident.clone());
    let variant_2 = variant.clone();
    let variant_name_s = variant.clone()
                                .map(|id| id.clone().to_string().to_case(Case::Kebab));
    let variant_data = fields.clone().map(|f| {
        let idents = f.fields.clone()
                             .into_iter()
                             .enumerate()
                             .map(|(i, f)| f.ident.clone().unwrap_or_else(|| {
                                 format_ident!("arg{i}")
                             }));
        let is_tuple = f.fields.iter()
                               .next()
                               .and_then(|f| f.ident.clone())
                               .is_none();
        (is_tuple, idents)
    });
    let query_nil = variant_data.clone().map(|(is_tuple, _)| {
        if is_tuple {
            quote!(( .. ))
        } else {
            quote!({ .. })
        }
    });
    let query = variant_data.clone().map(|(is_tuple, idents)| {
        if is_tuple {
            quote!((#(#idents),*))
        } else {
            quote!({ #(#idents),* })
        }
    });
    let body = variant_data.clone().map(|(is_tuple, idents)| {
        if is_tuple {
            quote!({#(
                let pv = #idents .into_pv(mem).unwrap();
                mem.push(pv);
            )*})
        } else {
            let idents_lhs = idents.clone();
            let idents_rhs = idents.clone();
            let idents_str = idents.clone()
                                   .map(|ident| ident.to_string().to_case(Case::Kebab));
            let num_idents = idents.clone().count();
            let count = idents.clone().enumerate().map(|(i, _)| i);
            quote!({
                static strs: &'static [&'static str; #num_idents] = &[#(#idents_str),*];
                #(let mut #idents_lhs = Some(#idents_rhs));*;
                for arg in args {
                    let sym = &*mem.name(*arg);
                    let pv = match strs.iter().copied().position(|x| x == sym) {
                        #(Some(#count) => #idents
                          .take()
                                          .expect("Duplicate argument should not be possible")
                                          .into_pv(mem)
                                          .unwrap()),*,
                        Some(_) => unreachable!(),
                        None => return Err((#root::error::ErrorKind::UndefinedVariable
                                            {var: *arg}).into())
                    };
                    mem.push(pv)
                }
            })
        }
    });

    let out = quote! {
        impl #root::EnumCall for #name {
            fn pushargs(self, args: &[#root::raw::nkgc::SymID], mem: &mut #root::raw::nkgc::Arena)
                        -> core::result::Result<(), #root::error::Error>
            {
                use #root::IntoLisp;
                match self {
                    #(Self::#variant #query => #body),*
                }
                Ok(())
            }

            fn name(&self, mem: &mut #root::raw::nkgc::Arena) -> #root::raw::nkgc::SymID {
                use #root::IntoLisp;
                match self {
                    #(Self::#variant_2 #query_nil => mem.put_sym(#variant_name_s)),*
                }
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
        impl #root::raw::nkgc::Traceable for #name {
            fn trace(&self, _gray: &mut Vec<*mut #root::nuke::NkAtom>) {}
            fn update_ptrs(&mut self, _reloc: &#root::nuke::PtrMap) {}
        }

        impl #root::fmt::LispFmt for #name {
            fn lisp_fmt(&self,
                        _db: &dyn #root::sym_db::SymDB,
                        _visited: &mut #root::fmt::VisitSet,
                        f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "({}", stringify!(#name))?;
                #( write!(f, " {} {:?}", #field_kws, self.#field_names)?; )*
                write!(f, ")")
            }
        }

        impl Userdata for #name {}

        impl #root::subrs::IntoLisp for #name {
            fn into_pv(self, mem: &mut #root::raw::nkgc::Arena)
                       -> core::result::Result<#root::raw::nkgc::PV, #root::error::Error>
            {
                Ok(mem.put(#root::nuke::Object::new(self)))
            }
        }
    };

    out.into()
}
