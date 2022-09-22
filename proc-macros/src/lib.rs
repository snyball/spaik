extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro2::Span;
use proc_macro_crate::{FoundCrate, crate_name};
use quote::{quote, format_ident};
use syn::{parse_macro_input, ItemFn, Signature, FnArg, PatType, Pat, Ident, DeriveInput, Data, DataStruct, FieldsNamed, ImplItem, ItemImpl, AttributeArgs, DataEnum};

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
        struct #obj_ident();

        unsafe impl #spaik_root::subrs::Subr for #obj_ident {
            fn call(&mut self,
                    vm: &mut #spaik_root::r8vm::R8VM,
                    args: &[#spaik_root::nkgc::PV])
                    -> core::result::Result<#spaik_root::nkgc::PV,
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

            fn into_subr(self) -> Box<dyn #spaik_root::subrs::Subr> {
                Box::new(self)
            }
        }

        impl From<#obj_ident> for Box<dyn #spaik_root::subrs::Subr> {
            fn from(x: #obj_ident) -> Self {
                Box::new(x)
            }
        }
    };

    out.into()
}

#[proc_macro_attribute]
pub fn spaikfn(attr: TokenStream, item: TokenStream) -> TokenStream {
    let _meta = parse_macro_input!(attr as AttributeArgs);
    spaik_fn_impl(crate_root(), item)
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
    let root = crate_root();
    let input = parse_macro_input!(item as DeriveInput);
    let name = input.ident.clone();
    let name_s = input.ident.to_string();
    let data = input.data.clone();
    let fields = match data {
        Data::Enum(DataEnum {
            variants, ..
        }) => variants,
        x => unimplemented!()
    }.into_iter();

    let variant = fields.clone().map(|f| f.ident.clone());
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
            let idents_str = idents.clone().map(|ident| ident.to_string());
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
                        None => return err!(UndefinedVariable, var: *arg)
                    };
                    mem.push(pv)
                }
            })
        }
    });

    let out = quote! {
        impl #root::subrs::EnumCall for #name {
            fn pushargs(self, args: &[#root::nkgc::SymID], mem: &mut #root::nkgc::Arena)
                        -> core::result::Result<(), #root::error::Error>
            {
                match self {
                    #(Self::#variant #query => #body),*
                }
                Ok(())
            }

            fn name(&self, mem: &mut #root::nkgc::Arena) -> #root::nkgc::SymID {
                mem.put_sym(#name_s)
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
        impl #root::nkgc::Traceable for #name {
            fn trace(&self, _gray: &mut Vec<*mut #root::nuke::NkAtom>) {}
            fn update_ptrs(&mut self, _reloc: &#root::nuke::PtrMap) {}
        }

        impl #root::fmt::LispFmt for #name {
            fn lisp_fmt(&self,
                        _db: &dyn #root::sym_db::SymDB,
                        _visited: &mut #root::fmt::VisitSet,
                        f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "({}", stringify!(#name))?;
                #( write!(f, " {} {}", #field_kws, self.#field_names)?; )*
                write!(f, ")")
            }
        }

        impl #root::nuke::Fissile for #name {
            fn type_of() -> #root::nuke::NkT {
                #root::nuke::NkT::Struct
            }
        }

        impl #root::subrs::IntoLisp for #name {
            fn into_pv(self, mem: &mut #root::nkgc::Arena)
                       -> core::result::Result<#root::nkgc::PV, #root::error::Error>
            {
                Ok(mem.put(#root::nuke::Object::new(self)))
            }
        }
    };

    out.into()
}
