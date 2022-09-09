use std::cell::{Ref, RefCell};
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::Arc;

use anyhow::{bail, Result};
use chiselc::policies::{
    Actions, Cond, Policy, PolicyEvalContext, PolicyName, Predicate, Predicates, Values, Var,
};
use serde_json::Value as JsonValue;

use super::store::Store;
use super::type_policy::TypePolicy;
use crate::datastore::expr::{BinaryExpr, BinaryOp, Expr, PropertyAccess, Value};
use crate::deno::ChiselRequestContext;
use crate::types::Entity;

#[derive(Default)]
pub struct PolicyEngine {
    eval_context: Rc<RefCell<PolicyEvalContext>>,
    store: RefCell<Store>,
}

pub enum Action {
    Allow,
    Deny,
    Skip,
    Log,
}

impl Action {
    fn is_restrictive(&self) -> bool {
        match self {
            Action::Deny | Action::Skip => true,
            Action::Allow | Action::Log => false,
        }
    }
}

impl From<chiselc::policies::Action> for Action {
    fn from(other: chiselc::policies::Action) -> Self {
        match other {
            chiselc::policies::Action::Allow => Self::Allow,
            chiselc::policies::Action::Log => Self::Log,
            chiselc::policies::Action::Deny => Self::Deny,
            chiselc::policies::Action::Skip => Self::Skip,
        }
    }
}

struct Filter {
    predicates: Predicates,
    where_conds: Option<Cond>,
    entity_param_name: String,
    read_actions: Arc<Actions>,
    env: Values,
    eval_ctx: Rc<RefCell<PolicyEvalContext>>,
}

impl Filter {
    fn new(
        chisel_ctx: &ChiselRequestContext,
        read_policy: &Policy,
        eval_ctx: Rc<RefCell<PolicyEvalContext>>,
    ) -> Result<Self> {
        let entity_param_name = read_policy.params().get_positional_param_name(0).to_owned();
        let ctx_param_name = read_policy.params().get_positional_param_name(1).to_owned();

        let mut env = Values::new();
        let ctx_json = serde_json::to_value(chisel_ctx)?;
        env.insert(ctx_param_name, ctx_json);

        let predicates = read_policy.predicates.substitute(&env);
        let mut ctx = eval_ctx.borrow_mut();
        let predicates = predicates.eval(&mut ctx);
        drop(ctx);

        let where_conds = read_policy
            .where_conds
            .as_ref()
            .map(|conds| conds.simplify(&predicates));

        let read_actions = read_policy.actions.clone();

        Ok(Self {
            predicates,
            where_conds,
            entity_param_name,
            read_actions,
            env,
            eval_ctx,
        })
    }

    /// Returns the filter Expr for that Filter.
    fn get_fitler_expr(&self) -> Result<Option<Expr>> {
        self.where_conds
            .as_ref()
            .map(|w| Self::cond_to_expr(w, &self.predicates, &self.entity_param_name))
            .transpose()
    }

    fn get_action(
        &self,
        _entity: &Entity,
        value: &serde_json::Map<String, JsonValue>,
    ) -> Result<Action> {
        // TODO: this clone is not necessary, but we need to abstact a bit the evaluation
        // environment.
        // TODO: typecheck value
        // TODO: reccursive check
        let mut env = self.env.clone();
        env.insert(
            self.entity_param_name.clone(),
            JsonValue::Object(value.clone()),
        );

        let predicates = self.predicates.substitute(&env);
        let mut eval_ctx = self.eval_ctx.borrow_mut();
        let predicates = predicates.eval(&mut eval_ctx);

        for (action, cond) in self.read_actions.iter() {
            match cond.simplify(&predicates) {
                Cond::True => return Ok((*action).into()),
                Cond::False => continue,
                _ => bail!(
                    "invalid policy: all variables should be determined in the current context"
                ),
            }
        }

        bail!("at least one policy rule must match!");
    }

    fn cond_to_expr(cond: &Cond, preds: &Predicates, entity_param_name: &str) -> Result<Expr> {
        let val = match cond {
            Cond::And(left, right) => {
                let right = Self::cond_to_expr(right, preds, entity_param_name)?;
                let left = Self::cond_to_expr(left, preds, entity_param_name)?;
                Expr::Binary(BinaryExpr {
                    left: Box::new(left),
                    op: BinaryOp::And,
                    right: Box::new(right),
                })
            }
            Cond::Or(left, right) => {
                let right = Self::cond_to_expr(right, preds, entity_param_name)?;
                let left = Self::cond_to_expr(left, preds, entity_param_name)?;
                Expr::Binary(BinaryExpr {
                    left: Box::new(left),
                    op: BinaryOp::Or,
                    right: Box::new(right),
                })
            }
            Cond::Not(cond) => Expr::Not(Box::new(Self::cond_to_expr(
                cond,
                preds,
                entity_param_name,
            )?)),
            Cond::Predicate(id) => {
                let predicate = preds.get(*id);
                Self::predicate_to_expr(predicate, entity_param_name)?
            }
            Cond::True => Expr::Value {
                value: Value::Bool(true),
            },
            Cond::False => Expr::Value {
                value: Value::Bool(false),
            },
        };

        Ok(val)
    }

    fn predicate_to_expr(pred: &Predicate, entity_param_name: &str) -> Result<Expr> {
        let val = match pred {
            Predicate::Bin { op, lhs, rhs } => {
                let left = Box::new(Self::predicate_to_expr(lhs, entity_param_name)?);
                let right = Box::new(Self::predicate_to_expr(rhs, entity_param_name)?);
                Expr::Binary(BinaryExpr {
                    op: BinaryOp::from(*op),
                    left,
                    right,
                })
            }
            Predicate::Not(_) => todo!(),
            Predicate::Lit(val) => Expr::Value {
                value: Value::from(val),
            },
            Predicate::Var(var) => match var {
                Var::Ident(id) => bail!("unknow variable: `{id}`"),
                Var::Member(obj, prop) => {
                    match &**obj {
                        // at this point, the only unresolved variables should be our entities, and we
                        // have statically verified that the correct fields are being accessed.
                        Var::Ident(n) if n == entity_param_name => {
                            let property_chain = Expr::Parameter { position: 0 };
                            Expr::Property(PropertyAccess {
                                property: prop.to_string(),
                                object: Box::new(property_chain),
                            })
                        } //make_property_chain()?,
                        other => bail!("unknow variable: `{other:?}`"),
                    }
                }
            },
        };

        Ok(val)
    }
}

/// An evaluation context instance for a given type, in a given request context.
/// This instance allows to build the filter expression, or to test the filters against an entity
/// instance.
#[allow(dead_code)]
pub struct PolicyEvalInstance {
    filters: HashMap<FilterName, Filter>,
    chisel_ctx: ChiselRequestContext,
    ty_name: String,
    version: String,
}

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
enum FilterName {
    Read,
    Create,
}

impl Into<PolicyName> for FilterName {
    fn into(self) -> PolicyName {
        match self {
            FilterName::Read => PolicyName::Read,
            FilterName::Create => PolicyName::Create,
        }
    }
}

impl PolicyEvalInstance {
    pub fn new(ty_name: String, version: String, chisel_ctx: ChiselRequestContext) -> Self {
        Self {
            filters: Default::default(),
            chisel_ctx,
            ty_name,
            version,
        }
    }

    fn get_or_load_filter(
        &mut self,
        engine: &PolicyEngine,
        filter: FilterName,
    ) -> Result<Option<&Filter>> {
        match self.filters.entry(filter) {
            Entry::Occupied(e) => Ok(Some(e.into_mut())),
            Entry::Vacant(e) => {
                if let Some(tp) = engine.get_policy(&self.version, &self.ty_name) {
                    if let Some(ref p) = tp.policies.get(filter.into()) {
                        let filter = Filter::new(&self.chisel_ctx, p, engine.eval_context.clone())?;
                        return Ok(Some(e.insert(filter)));
                    }
                }
                Ok(None)
            }
        }
    }

    pub fn make_read_filter_expr(&mut self, engine: &PolicyEngine) -> Result<Option<Expr>> {
        self.get_or_load_filter(engine, FilterName::Read)?
            .and_then(|f| f.get_fitler_expr().transpose())
            .transpose()
    }

    pub fn get_read_action(
        &mut self,
        engine: &PolicyEngine,
        entity: &Entity,
        val: &serde_json::Map<String, JsonValue>,
    ) -> Result<Option<Action>> {
        self.get_or_load_filter(engine, FilterName::Read)?
            .map(|f| f.get_action(entity, val))
            .transpose()
    }

    pub fn get_create_action(
        &mut self,
        engine: &PolicyEngine,
        entity: &Entity,
        val: &serde_json::Map<String, JsonValue>,
    ) -> Result<Option<Action>> {
        match self.get_read_action(engine, entity, val)? {
            Some(action) if action.is_restrictive() => Ok(Some(action)),
            _ => self
                .get_or_load_filter(engine, FilterName::Create)?
                .map(|f| f.get_action(entity, val))
                .transpose(),
        }
    }
}

impl PolicyEngine {
    pub fn new(store: Store) -> Self {
        Self {
            eval_context: Default::default(),
            store: store.into(),
        }
    }

    pub fn with_store_mut(&self, f: impl FnOnce(&mut Store)) {
        let mut store = self.store.borrow_mut();
        f(&mut store);
    }

    pub fn get_policy(&self, version: &str, ty: &str) -> Option<Ref<TypePolicy>> {
        let store = self.store.borrow();
        // this is a trick to get an Option<Ref<T>> from a Option<&T>
        if store.get_policy(version, ty).is_some() {
            Some(Ref::map(store, |s| s.get_policy(version, ty).unwrap()))
        } else {
            None
        }
    }
}
