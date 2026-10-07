use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::{parse::Parser, parse_quote, spanned::Spanned, *};

#[derive(Default)]
struct Options {
    log: Option<Expr>,
    state: Option<Expr>,
    params: Option<Expr>,
    events: Option<Expr>,
    step: Option<Expr>,
}
fn options(tokens: proc_macro2::TokenStream) -> Result<Options> {
    let mut o = Options::default();
    let parser = syn::meta::parser(|m| {
        let slot = if m.path.is_ident("log") {
            &mut o.log
        } else if m.path.is_ident("state") {
            &mut o.state
        } else if m.path.is_ident("params") {
            &mut o.params
        } else if m.path.is_ident("events") {
            &mut o.events
        } else if m.path.is_ident("step") {
            &mut o.step
        } else {
            return Err(m.error("expected log, state, params, events or step"));
        };
        if slot.is_some() {
            return Err(m.error("duplicate option"));
        }
        *slot = Some(m.value()?.parse()?);
        Ok(())
    });
    parser.parse2(tokens)?;
    if o.events.is_some() && (o.params.is_some() || o.state.is_some()) {
        return Err(Error::new(proc_macro2::Span::call_site(), "events replaces params and state"));
    }
    Ok(o)
}
fn wrap(method: &mut ImplItemFn, o: &Options) -> Result<()> {
    let sig = &method.sig;
    if sig.constness.is_some() || sig.asyncness.is_some() || sig.unsafety.is_some() {
        return Err(Error::new(
            sig.span(),
            "trace_step requires a safe, synchronous, non-const method; use #[trace_skip] on impl members",
        ));
    }
    if !matches!(sig.receiver(), Some(r) if r.reference.is_some()) {
        return Err(Error::new(sig.span(), "trace_step requires &self or &mut self"));
    }
    // A post-call observation cannot safely coexist with a returned borrow.
    fn borrowed(ty: &Type) -> bool {
        match ty {
            Type::Reference(_) => true,
            Type::Tuple(t) => t.elems.iter().any(borrowed),
            Type::Path(p) => p.path.segments.iter().any(|s| match &s.arguments {
                PathArguments::AngleBracketed(a) => a.args.iter().any(|a| match a {
                    GenericArgument::Lifetime(_) => true,
                    GenericArgument::Type(t) => borrowed(t),
                    _ => false,
                }),
                _ => false,
            }),
            Type::ImplTrait(_) => true,
            _ => false,
        }
    }
    if matches!(&sig.output, ReturnType::Type(_, t) if borrowed(t)) {
        return Err(Error::new(
            sig.output.span(),
            "a returned borrow cannot be observed after the call; use an owned-result wrapper or #[trace_skip]",
        ));
    }
    let name = format!("t_{}", sig.ident);
    let step = o.step.clone().unwrap_or_else(|| parse_quote!(#name));
    let log = o.log.clone().unwrap_or_else(|| parse_quote!(self.trace.clone()));
    let params = if let Some(p) = &o.params {
        quote!(#p)
    } else if o.events.is_some() {
        quote!(::tla_trace::Value::object::<&str>([]))
    } else {
        let mut args = Vec::new();
        for arg in &sig.inputs {
            if let FnArg::Typed(a) = arg {
                let Pat::Ident(p) = a.pat.as_ref() else {
                    return Err(Error::new(a.span(), "use named parameters or explicit params"));
                };
                let id = &p.ident;
                let key = id.to_string();
                args.push(quote!((#key, ::tla_trace::Observe::observe(&#id, cx))));
            }
        }
        quote!(::tla_trace::Value::object::<&str>([#(#args),*]))
    };
    let body = &method.block;
    let complete = if let Some(events) = &o.events {
        quote! { if __tla_guard.is_outer() { __tla_guard.complete_events(#events); } }
    } else {
        let state = o
            .state
            .clone()
            .unwrap_or_else(|| parse_quote!(::tla_trace::Observe::observe(self, cx)));
        quote! { __tla_guard.complete(|cx| #state); }
    };
    method.block = parse_quote!({
        let __tla_log = #log;
        let __tla_guard = __tla_log.enter(#step, |cx| { let _ = &cx; #params });
        let result = (|| #body)();
        #complete
        result
    });
    Ok(())
}

/// Attribute form lives under tla_trace::instrument, preserving trace_step!.
#[proc_macro_attribute]
pub fn trace_step(args: TokenStream, item: TokenStream) -> TokenStream {
    let output = (|| {
        let o = options(args.into())?;
        let tokens: proc_macro2::TokenStream = item.into();
        if let Ok(mut block) = syn::parse2::<ItemImpl>(tokens.clone()) {
            for item in &mut block.items {
                if let ImplItem::Fn(m) = item {
                    let skip = m.attrs.iter().any(|a| a.path().is_ident("trace_skip"));
                    m.attrs.retain(|a| !a.path().is_ident("trace_skip"));
                    if !skip
                        && !m.attrs.iter().any(|a| {
                            a.path().segments.last().is_some_and(|s| s.ident == "trace_step")
                        })
                    {
                        wrap(m, &o)?;
                    }
                }
            }
            Ok(quote!(#block))
        } else {
            let mut m: ImplItemFn = syn::parse2(tokens)?;
            wrap(&mut m, &o)?;
            Ok(quote!(#m))
        }
    })();
    output.unwrap_or_else(|e: Error| e.to_compile_error()).into()
}

#[proc_macro_derive(Observe, attributes(observe))]
pub fn derive_observe(item: TokenStream) -> TokenStream {
    let output = (|| {
        let input: DeriveInput = syn::parse(item)?;
        let name = &input.ident;
        let mut generics = input.generics.clone();
        // Generic elements are interned by equality by default, without inspecting bytes.
        let generic_names: Vec<_> = generics.type_params().map(|p| p.ident.clone()).collect();
        for p in generics.type_params_mut() {
            p.bounds.push(parse_quote!(::core::clone::Clone));
            p.bounds.push(parse_quote!(::core::cmp::Eq));
            p.bounds.push(parse_quote!('static));
            p.bounds.push(parse_quote!(::core::marker::Send));
        }
        fn encode(
            ty: &Type,
            access: proc_macro2::TokenStream,
            names: &[Ident],
        ) -> proc_macro2::TokenStream {
            if let Type::Path(p) = ty
                && p.qself.is_none()
            {
                let s = p.path.segments.last().unwrap();
                if names.contains(&s.ident) {
                    return quote!(cx.intern(#access));
                }
                if let PathArguments::AngleBracketed(a) = &s.arguments {
                    let ts: Vec<_> =
                        a.args
                            .iter()
                            .filter_map(|a| {
                                if let GenericArgument::Type(t) = a { Some(t) } else { None }
                            })
                            .collect();
                    if ts.len() == 1
                        && ["Vec", "VecDeque", "HashSet", "BTreeSet", "Option"]
                            .iter()
                            .any(|n| s.ident == *n)
                    {
                        let inner = encode(ts[0], quote!(v), names);
                        return if s.ident == "Option" {
                            quote!(::tla_trace::Value::option((#access).as_ref().map(|v| #inner)))
                        } else {
                            quote!(::tla_trace::Value::Array((#access).iter().map(|v| #inner).collect()))
                        };
                    }
                    if ts.len() == 2 && (s.ident == "HashMap" || s.ident == "BTreeMap") {
                        let k = encode(ts[0], quote!(k), names);
                        let v = encode(ts[1], quote!(v), names);
                        return quote!(::tla_trace::Value::Array((#access).iter().map(|(k,v)| ::tla_trace::Value::Array(vec![#k, #v])).collect()));
                    }
                }
            }
            quote!(::tla_trace::Observe::observe(#access, cx))
        }
        let fields =
            |fs: &Fields,
             enum_mode: bool|
             -> Result<(Vec<proc_macro2::TokenStream>, Vec<proc_macro2::TokenStream>)> {
                let mut binds = Vec::new();
                let mut entries = Vec::new();
                for (i, f) in fs.iter().enumerate() {
                    let member = f
                        .ident
                        .clone()
                        .map(Member::Named)
                        .unwrap_or(Member::Unnamed(Index::from(i)));
                    let binding = format_ident!("__field_{i}");
                    let mut key =
                        f.ident.as_ref().map(ToString::to_string).unwrap_or(format!("v{i}"));
                    let mut skip = false;
                    let mut intern = false;
                    let mut with: Option<Expr> = None;
                    for a in &f.attrs {
                        if a.path().is_ident("observe") {
                            a.parse_nested_meta(|m| {
                                if m.path.is_ident("skip") {
                                    skip = true;
                                } else if m.path.is_ident("intern") {
                                    intern = true;
                                } else if m.path.is_ident("rename") {
                                    key = m.value()?.parse::<LitStr>()?.value();
                                } else if m.path.is_ident("with") {
                                    with = Some(m.value()?.parse()?);
                                } else {
                                    return Err(m.error("expected skip, intern, rename or with"));
                                }
                                Ok(())
                            })?;
                        }
                    }
                    binds.push(quote!(#member: #binding));
                    if skip {
                        continue;
                    }
                    let access = if enum_mode { quote!(#binding) } else { quote!(&self.#member) };
                    let value = if let Some(with) = with {
                        quote!((#with)(#access, cx))
                    } else if intern {
                        quote!(cx.intern(#access))
                    } else {
                        encode(&f.ty, access, &generic_names)
                    };
                    entries.push(quote!((#key, #value)));
                }
                Ok((binds, entries))
            };
        let body = match &input.data {
            Data::Struct(s) => {
                let (_, entries) = fields(&s.fields, false)?;
                quote!(::tla_trace::Value::object::<&str>([#(#entries),*]))
            }
            Data::Enum(e) => {
                let mut arms = Vec::new();
                for v in &e.variants {
                    let variant = &v.ident;
                    let tag = variant.to_string();
                    let (binds, entries) = fields(&v.fields, true)?;
                    arms.push(quote!(Self::#variant { #(#binds),* } => ::tla_trace::Value::object([("tag", ::tla_trace::Value::from(#tag)), #(#entries),*])));
                }
                quote!(match self { #(#arms),* })
            }
            Data::Union(u) => {
                return Err(Error::new(u.union_token.span(), "Observe cannot derive for unions"));
            }
        };
        let (imp, ty, wh) = generics.split_for_impl();
        Ok(quote! { impl #imp ::tla_trace::Observe for #name #ty #wh {
            fn observe(&self, cx: &mut ::tla_trace::Context) -> ::tla_trace::Value { #body }
        } })
    })();
    output.unwrap_or_else(|e: Error| e.to_compile_error()).into()
}
