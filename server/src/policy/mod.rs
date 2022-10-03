#![allow(dead_code)]
use std::cell::{RefCell, RefMut};
use std::collections::{hash_map::Entry, HashMap};
use std::rc::Rc;
use std::str::FromStr;
use std::sync::Arc;

use anyhow::{bail, Result};

use crate::datastore::value::{EntityMap, EntityValue};
use crate::types::ObjectType;

use self::engine::{ChiselRequestContext, PolicyEngine};
use self::instances::PolicyEvalInstance;
use self::utils::{entity_map_to_js_value, js_value_to_entity_value};

pub mod engine;
mod instances;
mod interpreter;
pub mod store;
pub mod type_policy;
mod utils;

pub struct PolicyContext {
    pub cache: PolicyInstancesCache,
    pub engine: Rc<PolicyEngine>,
    pub request: Rc<dyn ChiselRequestContext>,
}

impl PolicyContext {
    pub fn new(engine: Rc<PolicyEngine>, request: Rc<dyn ChiselRequestContext>) -> Self {
        let cache = PolicyInstancesCache::default();
        Self {
            cache,
            engine,
            request,
        }
    }
}

#[derive(Clone, Debug, thiserror::Error)]
pub enum PolicyError {
    #[error("could not write `{}` to disk: Permission denied", .0.name())]
    WritePermissionDenied(Arc<ObjectType>),
    #[error("could not Read `{}`: Permission denied", .0.name())]
    ReadPermissionDenied(Arc<ObjectType>),
    #[error("could not write `{}`: Entity is dirty: it was transformed by a policy.", .0.name())]
    DirtyEntity(Arc<ObjectType>),
}

#[derive(Debug)]
#[repr(u8)]
pub enum Action {
    Allow = 0,
    Deny = 1,
    Skip = 2,
    Log = 3,
}

impl TryFrom<i32> for Action {
    type Error = anyhow::Error;

    fn try_from(value: i32) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(Self::Allow),
            1 => Ok(Self::Deny),
            2 => Ok(Self::Skip),
            3 => Ok(Self::Log),
            _ => bail!("invalid Action"),
        }
    }
}

impl Action {
    pub fn is_restrictive(&self) -> bool {
        match self {
            Action::Deny | Action::Skip => true,
            Action::Allow | Action::Log => false,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Location {
    UsEast1,
    UsWest,
    London,
    Germany,
}

impl FromStr for Location {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> anyhow::Result<Self, Self::Err> {
        match s {
            "us-east-1" => Ok(Self::UsEast1),
            "us-west" => Ok(Self::UsWest),
            "london" => Ok(Self::London),
            "germany" => Ok(Self::Germany),
            other => bail!("unknown region {other}"),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum WriteAction {
    Create,
    Update,
}

#[derive(Default)]
pub struct PolicyInstancesCache {
    inner: RefCell<HashMap<String, PolicyEvalInstance>>,
}

impl PolicyInstancesCache {
    pub fn get_or_create_policy_instance(
        &self,
        ctx: &PolicyContext,
        ty: &Arc<ObjectType>,
    ) -> RefMut<PolicyEvalInstance> {
        let inner = self.inner.borrow_mut();
        RefMut::map(inner, |inner| match inner.entry(ty.name().to_owned()) {
            Entry::Occupied(e) => e.into_mut(),
            Entry::Vacant(e) => {
                let instance = PolicyEvalInstance::new(ctx, ty.clone());
                e.insert(instance)
            }
        })
    }
}

pub struct PolicyProcessor {
    pub ty: Arc<ObjectType>,
    pub ctx: Rc<PolicyContext>,
}

impl PolicyProcessor {
    pub fn process_read(&self, value: EntityMap) -> anyhow::Result<Option<EntityMap>> {
        let mut instance = self
            .ctx
            .cache
            .get_or_create_policy_instance(&self.ctx, &self.ty);

        let js_value =
            entity_map_to_js_value(&mut self.ctx.engine.boa_ctx.borrow_mut(), &value, true);

        let js_value = match instance.get_read_action(&self.ctx, &js_value)? {
            Some(Action::Allow) | None => Some(js_value),
            Some(Action::Deny) => Err(PolicyError::ReadPermissionDenied(self.ty.clone()))?,
            Some(Action::Skip) => None,
            Some(Action::Log) => {
                info!("{value:?}");
                Some(js_value)
            }
        };

        if let Some(js_value) = js_value {
            instance.transform_on_read(&self.ctx, &js_value)?;
            let new_val = js_value_to_entity_value(&js_value).try_into_map()?;

            if new_val != value {
                instance.mark_dirty(value["id"].as_str().unwrap());
            }

            Ok(Some(new_val))
        } else {
            js_value
                .as_ref()
                .map(js_value_to_entity_value)
                .map(EntityValue::try_into_map)
                .transpose()
        }
    }

    pub fn process_write(
        &self,
        value: EntityMap,
        action: WriteAction,
    ) -> Result<(EntityMap, Option<Location>)> {
        let mut instance = self
            .ctx
            .cache
            .get_or_create_policy_instance(&self.ctx, &self.ty);
        let js_value =
            entity_map_to_js_value(&mut self.ctx.engine.boa_ctx.borrow_mut(), &value, true);
        let action = match action {
            WriteAction::Create => instance.get_create_action(&self.ctx, &js_value)?,
            WriteAction::Update => {
                if instance.is_dirty(value["id"].as_str().unwrap()) {
                    Err(PolicyError::DirtyEntity(self.ty.clone()))?
                }

                instance.get_update_action(&self.ctx, &js_value)?
            }
        };

        let geo_loc = instance.geo_loc(&self.ctx, &js_value)?;

        match action {
            Some(Action::Log) => {
                log::info!("{value:?}");
            }
            Some(Action::Deny) => {
                Err(PolicyError::WritePermissionDenied(self.ty.clone()))?;
            }
            Some(Action::Skip) => {
                // TODO: maybe that's not what we want?
                Err(PolicyError::WritePermissionDenied(self.ty.clone()))?;
            }
            _ => (),
        }

        instance.transform_on_write(&self.ctx, &js_value)?;
        let value = js_value_to_entity_value(&js_value).try_into_map()?;

        Ok((value, geo_loc))
    }
}
