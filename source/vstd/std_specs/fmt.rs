use super::super::prelude::*;
use core::fmt::{Arguments, Error, Formatter};

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExError(Error);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExFormatter<'a>(Formatter<'a>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExArguments<'a>(Arguments<'a>);

// Rust has a specially handled private module core::fmt::rt,
// for which we can't directly declare specifications because it is private.
// To work around this, declare our own rt module,
// which Verus specially recognizes as a stand-in for core::fmt::rt:
#[verifier::external]
mod rt {
    #[verusfmt::skip]
    #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument")]
    pub struct Argument<'a>(&'a ());

    impl<'a> Argument<'a> {
        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_binary")]
        pub fn new_binary<'b, T: core::fmt::Binary>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_debug")]
        pub fn new_debug<'b, T: core::fmt::Debug>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_debug_noop")]
        pub fn new_debug_noop<'b, T: core::fmt::Debug>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_display")]
        pub fn new_display<'b, T: core::fmt::Display>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_lower_exp")]
        pub fn new_lower_exp<'b, T: core::fmt::LowerExp>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_lower_hex")]
        pub fn new_lower_hex<'b, T: core::fmt::LowerHex>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_octal")]
        pub fn new_octal<'b, T: core::fmt::Octal>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_pointer")]
        pub fn new_pointer<'b, T: core::fmt::Pointer>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_upper_exp")]
        pub fn new_upper_exp<'b, T: core::fmt::UpperExp>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::new_upper_hex")]
        pub fn new_upper_hex<'b, T: core::fmt::UpperHex>(x: &'b T) -> Argument<'b> {
            unimplemented!()
        }

        #[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::rt::Argument::from_usize")]
        pub fn from_usize<'b>(x: &'b usize) -> Argument<'b> {
            unimplemented!()
        }
    }

}

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExArgument<'a>(rt::Argument<'a>);

macro_rules! def_fmt_trait {
    ($trait:path, $extrait: ident, $spec_trait:ident, $impl_trait:ident, $new:ident) => {
        $crate::vstd::prelude::verus! {
            #[verifier::external_trait_specification]
            #[verifier::external_trait_extension($spec_trait via $impl_trait)]
            pub trait $extrait: core::marker::PointeeSized {
                type ExternalTraitSpecificationFor: $trait;

                fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>;
            }

            #[doc(hidden)]
            pub assume_specification<'a, 'b, T: $trait>[ rt::Argument::<'a>::$new ](x: &'b T) -> rt::Argument<'b>;
        }
};
}

def_fmt_trait!(core::fmt::Binary, ExBinary, BinarySpec, BinarySpecImpl, new_binary);

def_fmt_trait!(core::fmt::Debug, ExDebug, DebugSpec, DebugSpecImpl, new_debug);

def_fmt_trait!(core::fmt::Display, ExDisplay, DisplaySpec, DisplaySpecImpl, new_display);

def_fmt_trait!(core::fmt::LowerExp, ExLowerExp, LowerExpSpec, LowerExpSpecImpl, new_lower_exp);

def_fmt_trait!(core::fmt::LowerHex, ExLowerHex, LowerHexSpec, LowerHexSpecImpl, new_lower_hex);

def_fmt_trait!(core::fmt::Octal, ExOctal, OctalSpec, OctalSpecImpl, new_octal);

def_fmt_trait!(core::fmt::Pointer, ExPointer, PointerSpec, PointerSpecImpl, new_pointer);

def_fmt_trait!(core::fmt::UpperExp, ExUpperExp, UpperExpSpec, UpperExpSpecImpl, new_upper_exp);

def_fmt_trait!(core::fmt::UpperHex, ExUpperHex, UpperHexSpec, UpperHexSpecImpl, new_upper_hex);

#[doc(hidden)]
pub assume_specification<'a, 'b, T: core::fmt::Debug>[ rt::Argument::<'a>::new_debug_noop ](
    x: &'b T,
) -> rt::Argument<'b>
;

#[doc(hidden)]
pub assume_specification<'a, 'b>[ rt::Argument::<'a>::from_usize ](x: &'b usize) -> rt::Argument<'b>
    requires
        *x <= u16::MAX,
;

pub assume_specification<'a>[ Arguments::<'a>::from_str ](s: &'static str) -> Arguments<'a>
;

pub assume_specification<'a>[ Arguments::<'a>::from_str_nonconst ](s: &'static str) -> Arguments<'a>
;

// Specially handled stand-in for Arguments::new (because it uses the private Argument type)
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::fmt::Arguments::new")]
#[verifier::external]
#[doc(hidden)]
pub fn arguments_new<'a, const N: usize, const M: usize>(
    template: &'a [u8; N],
    args: &'a [rt::Argument<'a>; M],
) -> Arguments<'a> {
    unimplemented!()
}

#[doc(hidden)]
pub assume_specification<'a, const N: usize, const M: usize>[ arguments_new ](
    template: &'a [u8; N],
    args: &'a [rt::Argument<'a>; M],
) -> Arguments<'a>
;

pub assume_specification<'a>[ Formatter::<'a>::write_str ](
    f: &mut Formatter<'a>,
    data: &str,
) -> Result<(), Error>
;

pub assume_specification<'a, 'b>[ Formatter::<'a>::debug_tuple_field1_finish ](
    f: &'b mut Formatter<'a>,
    name: &str,
    value1: &dyn core::fmt::Debug,
) -> Result<(), Error>
;

pub assume_specification<'a, 'b>[ Formatter::<'a>::debug_struct_field1_finish ](
    f: &'b mut Formatter<'a>,
    name: &str,
    name1: &str,
    value1: &dyn core::fmt::Debug,
) -> Result<(), Error>
;

pub assume_specification<'a, 'b>[ Formatter::<'a>::debug_tuple_field2_finish ](
    f: &'b mut Formatter<'a>,
    name: &str,
    value1: &dyn core::fmt::Debug,
    value2: &dyn core::fmt::Debug,
) -> Result<(), Error>
;

pub assume_specification<'a, 'b>[ Formatter::<'a>::debug_struct_field2_finish ](
    f: &'b mut Formatter<'a>,
    name: &str,
    name1: &str,
    value1: &dyn core::fmt::Debug,
    name2: &str,
    value2: &dyn core::fmt::Debug,
) -> Result<(), Error>
;

pub assume_specification<'a, 'b>[ Formatter::<'a>::debug_tuple_field3_finish ](
    f: &'b mut Formatter<'a>,
    name: &str,
    value1: &dyn core::fmt::Debug,
    value2: &dyn core::fmt::Debug,
    value3: &dyn core::fmt::Debug,
) -> Result<(), Error>
;

pub assume_specification<'a, 'b>[ Formatter::<'a>::debug_struct_field3_finish ](
    f: &'b mut Formatter<'a>,
    name: &str,
    name1: &str,
    value1: &dyn core::fmt::Debug,
    name2: &str,
    value2: &dyn core::fmt::Debug,
    name3: &str,
    value3: &dyn core::fmt::Debug,
) -> Result<(), Error>
;

pub assume_specification<'a, 'b>[ Formatter::<'a>::debug_tuple_field4_finish ](
    f: &'b mut Formatter<'a>,
    name: &str,
    value1: &dyn core::fmt::Debug,
    value2: &dyn core::fmt::Debug,
    value3: &dyn core::fmt::Debug,
    value4: &dyn core::fmt::Debug,
) -> Result<(), Error>
;

pub assume_specification<'a, 'b>[ Formatter::<'a>::debug_struct_field4_finish ](
    f: &'b mut Formatter<'a>,
    name: &str,
    name1: &str,
    value1: &dyn core::fmt::Debug,
    name2: &str,
    value2: &dyn core::fmt::Debug,
    name3: &str,
    value3: &dyn core::fmt::Debug,
    name4: &str,
    value4: &dyn core::fmt::Debug,
) -> Result<(), Error>
;

pub assume_specification<'a, 'b>[ Formatter::<'a>::debug_tuple_field5_finish ](
    f: &'b mut Formatter<'a>,
    name: &str,
    value1: &dyn core::fmt::Debug,
    value2: &dyn core::fmt::Debug,
    value3: &dyn core::fmt::Debug,
    value4: &dyn core::fmt::Debug,
    value5: &dyn core::fmt::Debug,
) -> Result<(), Error>
;

pub assume_specification<'a, 'b>[ Formatter::<'a>::debug_struct_field5_finish ](
    f: &'b mut Formatter<'a>,
    name: &str,
    name1: &str,
    value1: &dyn core::fmt::Debug,
    name2: &str,
    value2: &dyn core::fmt::Debug,
    name3: &str,
    value3: &dyn core::fmt::Debug,
    name4: &str,
    value4: &dyn core::fmt::Debug,
    name5: &str,
    value5: &dyn core::fmt::Debug,
) -> Result<(), Error>
;

pub assume_specification<'a, 'b>[ Formatter::<'a>::debug_tuple_fields_finish ](
    f: &'b mut Formatter<'a>,
    name: &str,
    values: &[&dyn core::fmt::Debug],
) -> Result<(), Error>
;

pub assume_specification<'a, 'b>[ Formatter::<'a>::debug_struct_fields_finish ](
    f: &'b mut Formatter<'a>,
    name: &str,
    names: &[&str],
    values: &[&dyn core::fmt::Debug],
) -> Result<(), Error>
    requires
        names@.len() == values@.len(),
;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub assume_specification[ alloc::fmt::format ](args: Arguments<'_>) -> alloc::string::String
;

} // verus!
