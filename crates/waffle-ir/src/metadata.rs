//! WASM semantic metadata manifest carrier for Waffle modules.
//!
//! The map is source-neutral.  Consumers choose [`MetadataMode`] explicitly;
//! this adapter only imports and emits canonical WSMM bytes.

use alloc::vec::Vec;
use wax_meta::{Error, Manifest, MetadataMode, MetadataSnapshot, SECTION_NAME};

use crate::Module;

impl<'a> Module<'a> {
    /// Decode the v0.1 manifest custom section, if present.
    pub fn wsmm_manifest(&self) -> Result<Option<Manifest>, Error> {
        self.custom_sections
            .get(SECTION_NAME)
            .map(|bytes| Manifest::decode(bytes))
            .transpose()
    }

    /// Replace the v0.1 manifest section with its canonical payload.
    pub fn set_wsmm_manifest(&mut self, manifest: &Manifest) -> Result<(), Error> {
        self.custom_sections.insert(SECTION_NAME.into(), manifest.encode()?);
        Ok(())
    }

    /// Remove WSMM when a rewrite invalidates its semantic claims.
    pub fn clear_wsmm_manifest(&mut self) -> Option<Vec<u8>> {
        self.custom_sections.remove(SECTION_NAME)
    }

    /// Return a manifest only for a consumer that has opted in to respecting it.
    pub fn wsmm_for_mode(&self, mode: MetadataMode) -> Result<Option<(Manifest, MetadataSnapshot)>, Error> {
        if mode == MetadataMode::Ignore { return Ok(None); }
        let Some(manifest) = self.wsmm_manifest()? else { return Ok(None); };
        let snapshot = manifest.snapshot()?;
        Ok(Some((manifest, snapshot)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use wax_meta::Value;

    #[test]
    fn manifest_round_trips_through_custom_sections() {
        let mut module = Module::empty();
        let mut manifest = Manifest::new();
        manifest.insert("memory/0/maximum_pages".into(), Value::U64(1)).unwrap();
        module.set_wsmm_manifest(&manifest).unwrap();
        assert_eq!(module.wsmm_for_mode(MetadataMode::Ignore).unwrap(), None);
        assert_eq!(module.wsmm_manifest().unwrap(), Some(manifest));
    }
}