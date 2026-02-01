use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, parse_quote, Expr, ItemFn};

#[proc_macro_attribute]
pub fn error_context(attr: TokenStream, item: TokenStream) -> TokenStream {
    let message = parse_macro_input!(attr as Expr);
    let mut function = parse_macro_input!(item as ItemFn);
    let block = function.block;

    function.attrs.push(parse_quote!(#[track_caller]));
    function.block = Box::new(parse_quote!({
        let __ubiblk_location = std::panic::Location::caller();
        let __ubiblk_result: crate::Result<_> = (|| { #block })();
        __ubiblk_result.map_err(|__ubiblk_error| {
            __ubiblk_error.context_at(#message, __ubiblk_location)
        })
    }));

    TokenStream::from(quote!(#function))
}
