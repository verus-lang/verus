use vir::ast::{
    Path, Ident, Expr, Typ, Datatype, Function, VirErr,
};
use smir::ast::{
    Field, LemmaPurpose, TransitionKind, Invariant, Lemma, Transition, ShardableType,
};
use crate::util::{err_span_str};
use rustc_hir::{VariantData};
use air::ast_util::str_ident;
use air::errors::{error};
use std::collections::HashMap;
use smir_vir::reinterpret::reinterpret_func_as_transition;
use crate::rust_to_vir_base::{AttrTree, VerifierAttrs};
use std::sync::Arc;

pub struct SMCtxt {
    sm_types: HashMap<Path, Vec<Field<Ident, Typ>>>,

    invariants: HashMap<Path, Invariant<Ident>>,
    lemmas: HashMap<Path, Lemma<Ident, Ident>>,
    transitions: HashMap<Path, Transition<Ident, Expr, Typ>>,
}

#[derive(Clone)]
pub enum StateMachineFnAttr {
    Init,
    Transition,
    Static,
    Invariant,
    Lemma(LemmaPurpose<Ident>),
}

pub(crate) fn parse_state_machine_fn_attr(t: &AttrTree) -> Result<StateMachineFnAttr, VirErr> {
    match t {
        AttrTree::Fun(_, arg, None) if arg == "transition" => {
            Ok(StateMachineFnAttr::Transition)
        }
        AttrTree::Fun(_, arg, None) if arg == "init" => {
            Ok(StateMachineFnAttr::Init)
        }
        AttrTree::Fun(_, arg, None) if arg == "static" => {
            Ok(StateMachineFnAttr::Static)
        }
        AttrTree::Fun(_, arg, None) if arg == "invariant" => {
            Ok(StateMachineFnAttr::Invariant)
        }
        AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, id, None)])) if arg == "lemma" => {
            let lp = LemmaPurpose { transition: Arc::new(id.clone()) };
            Ok(StateMachineFnAttr::Lemma(lp))
        }
        AttrTree::Fun(span, _, _) | AttrTree::Eq(span, _, _) => {
            return err_span_str(*span, "unrecognized state_machine_fn attribute");
        }
    }
}

impl SMCtxt {
    pub fn new() -> SMCtxt {
        SMCtxt {
            sm_types: HashMap::new(),
            invariants: HashMap::new(),
            lemmas: HashMap::new(),
            transitions: HashMap::new(),
        }
    }

    pub(crate) fn check_datatype<'tcx>(
        &mut self,
        attrs: &VerifierAttrs,
        variant_data: &'tcx VariantData<'tcx>,
        datatype: &Datatype
    ) -> Result<(), VirErr> {
        if attrs.state_machine_struct {
            if datatype.x.typ_params.len() > 0 {
                return Err(error("unsupported: state machine generics", &datatype.span));
            }

            match variant_data {
                VariantData::Struct(fields, _) => {
                    let mut sm_fields: Vec<Field<Ident, Typ>> = Vec::new();
                    for field in fields.iter() {
                        // TODO check for the attribute on the field
                        let field_ident = str_ident(&field.ident.as_str());
                        let vir_field = vir::ast_util::get_field(
                            &datatype.x.get_only_variant().a, &field_ident);
                        let vir_ty = vir_field.a.0.clone();
                        let sm_field = Field {
                            ident: field_ident,
                            stype: ShardableType::Variable(vir_ty), // TODO make this more general
                        };
                        sm_fields.push(sm_field);
                    }
                    self.sm_types.insert(datatype.x.path.clone(), sm_fields);
                }
                _ => {
                    // Shouldn't get here from macro output
                    panic!("unsupported; state machine type must be a struct");
                }
            }
        }

        return Ok(());
    }

    fn check_impl_item_transition(
        &mut self,
        func_path: Path,
        func: &Function,
        kind: TransitionKind) -> Result<(), VirErr>
    {
        let tr = reinterpret_func_as_transition(func.clone(), kind)?;
        self.transitions.insert(func_path, tr);
        Ok(())
    }

    pub(crate) fn check_impl_item(
        &mut self,
        state_machine_fn_attr: &Option<StateMachineFnAttr>,
        func: &Function,
    ) -> Result<(), VirErr> {
        let name = func.x.name.path.segments.last().expect("last");
        match state_machine_fn_attr {
            Some(StateMachineFnAttr::Init) => self.check_impl_item_transition(func.x.name.path.clone(), func, TransitionKind::Init),
            Some(StateMachineFnAttr::Transition) => self.check_impl_item_transition(func.x.name.path.clone(), func, TransitionKind::Transition),
            Some(StateMachineFnAttr::Static) => self.check_impl_item_transition(func.x.name.path.clone(), func, TransitionKind::Static),
            Some(StateMachineFnAttr::Invariant) => {
                let inv = Invariant { func: name.clone() };
                self.invariants.insert(func.x.name.path.clone(), inv);
                Ok(())
            }
            Some(StateMachineFnAttr::Lemma(purpose)) => {
                let lem = Lemma { func: name.clone(), purpose: purpose.clone() };
                self.lemmas.insert(func.x.name.path.clone(), lem);
                Ok(())
            }
            None => { Ok(()) }
        }
    }
}
