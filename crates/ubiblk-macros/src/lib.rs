use proc_macro::TokenStream;
use quote::quote;
use syn::{
    parse::{Parse, ParseStream},
    parse_macro_input, parse_quote,
    punctuated::Punctuated,
    Expr, ItemFn, ReturnType, Token,
};

struct ErrorContextArgs {
    args: Punctuated<Expr, Token![,]>,
}

impl Parse for ErrorContextArgs {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let args = Punctuated::parse_terminated(input)?;
        Ok(Self { args })
    }
}

#[proc_macro_attribute]
pub fn error_context(attr: TokenStream, item: TokenStream) -> TokenStream {
    let ErrorContextArgs { args } = parse_macro_input!(attr as ErrorContextArgs);
    let message = if args.len() == 1 {
        let expr = args
            .first()
            .expect("error_context should have at least one argument");
        quote!(#expr)
    } else {
        quote!(format!(#args))
    };
    let mut function = parse_macro_input!(item as ItemFn);
    let output_type = match &function.sig.output {
        ReturnType::Type(_, ty) => ty,
        ReturnType::Default => {
            return syn::Error::new_spanned(
                &function.sig.ident,
                "error_context requires a return type",
            )
            .to_compile_error()
            .into();
        }
    };
    let block = function.block;

    function.attrs.push(parse_quote!(#[track_caller]));
    function.block = Box::new(parse_quote!({
        let __ubiblk_location = std::panic::Location::caller();
        let __ubiblk_result = (|| -> #output_type { #block })();
        __ubiblk_result.map_err(|__ubiblk_error| {
            __ubiblk_error.context_at(#message, __ubiblk_location)
        })
    }));

    TokenStream::from(quote!(#function))
}
