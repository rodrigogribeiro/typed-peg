{-# LANGUAGE CPP #-}

-- | What differs between the versions of template-haskell the quasi-quoters
-- build against.  Kept apart from "PEG.QQ" because CPP does not understand
-- Haskell's string gaps, which that module's error messages use.
module PEG.QQ.Compat
  ( requiredTV
  , requiredKindedTV
  ) where

import qualified Language.Haskell.TH as TH

-- | The binders of a data declaration.  template-haskell 2.21 (GHC 9.8) gave
-- them a visibility flag; before it they carry @()@.
#if MIN_VERSION_template_haskell(2,21,0)
requiredTV :: TH.Name -> TH.TyVarBndr TH.BndrVis
requiredTV n = TH.PlainTV n TH.BndrReq

requiredKindedTV :: TH.Name -> TH.Kind -> TH.TyVarBndr TH.BndrVis
requiredKindedTV n k = TH.KindedTV n TH.BndrReq k
#else
requiredTV :: TH.Name -> TH.TyVarBndr ()
requiredTV n = TH.PlainTV n ()

requiredKindedTV :: TH.Name -> TH.Kind -> TH.TyVarBndr ()
requiredKindedTV n k = TH.KindedTV n () k
#endif
