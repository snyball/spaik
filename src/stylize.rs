#[cfg(feature = "extra")]
use owo_colors::{OwoColorize, Styled, style};

macro_rules! def_styles {
    ($($name:ident $init:block)*) => {
        #[cfg(feature = "extra")]
        pub trait Stylize: OwoColorize {
            $(fn $name(&self) -> Styled<&Self>;)*
        }
        #[cfg(feature = "extra")]
        impl<T> Stylize for T where T: OwoColorize {
            $(fn $name(&self) -> Styled<&T> { self.style($init) })*
        }

        #[cfg(not(feature = "extra"))]
        pub trait Stylize {
            $(fn $name(&self) -> &Self;)*
        }
        #[cfg(not(feature = "extra"))]
        impl<T> Stylize for T {
            $(#[inline(always)]
              fn $name(&self) -> &T { self })*
        }
    };
}

def_styles! {
    style_ret { style().blue().bold() }
    style_asm_label_ref { style().yellow() }
    style_asm_label { style().yellow().bold() }
    style_asm_fn { style().cyan().bold() }
    style_asm_var { style().cyan().bold() }
    style_asm_op { style().cyan().bold() }
    style_warning { style().yellow().bold() }
    style_error { style().red().bold() }
    style_success { style().green().bold() }
    style_info { style().white().bold() }
    style_prompt { style().white().bold() }
}
