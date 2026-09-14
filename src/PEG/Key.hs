{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes     #-}

-- | What a non-terminal reference points at.
--
-- A 'PEG.Syntax.PExp' is indexed by a /key type/ @nt :: Type -> Type@: a
-- value of type @nt a@ names a rule returning @a@, and
-- @'PEG.Syntax.NT' :: nt a -> PExp s nt a@ is a reference to it.  Checking a
-- reference is then checking the type of one constructor, which costs the
-- type checker the same whatever the size of the grammar.
--
-- There are two kinds of key.
--
-- * A key type declared for one grammar, one constructor per rule:
--
--   @
--   data ArithEnv s a where
--     ArithEnv_expr :: ArithEnv s Exp
--     ArithEnv_term :: ArithEnv s Exp
--   @
--
--   This is what 'PEG.QQ.pegGrammar' generates in declaration position,
--   together with its 'Tabulate' instance, and it is what a grammar of any
--   size should use.
--
-- * @'InEnv' env@, a membership proof into a type-level list of rules
--   ('PEG.Type.Env').  This is what @'PEG.Syntax.nt' \@"expr"@,
--   'PEG.QQ.pegRules' and a hand-written environment go through.
--
-- == Why keys
--
-- The environment used to be the only index.  A reference carried a unary
-- proof, @There (There ... Here)@, of where its rule sits in a type-level
-- list, and the type checker's evidence for that proof is proportional to how
-- deep the rule is times how much of the list is left.  Summed over every
-- reference of a grammar, that was the whole of what compiling a large
-- grammar cost: 2.2 GB of heap at 128 rules and more than 8 GB at 256, even
-- with the proof supplied by the splice rather than searched for.  A declared
-- key costs 50 MB at 512 rules.  See @bench-compile/@.
module PEG.Key
  ( Tabulate (..)
  , Table (..)
  , InEnv (..)
  ) where

import Data.Kind (Type)

import PEG.Member
import PEG.Type

-- | A total function out of a key type, as a value.
newtype Table (nt :: Type -> Type) (f :: Type -> Type) =
  Table { lookupTable :: forall b. nt b -> f b }

-- | A key type whose rules can be enumerated.
--
-- This is what lets a grammar over declared keys be compiled with a knot:
-- 'PEG.Parse.compileGrammar' tabulates the compiled rule bodies once and
-- resolves every reference through the table.
class Tabulate (nt :: Type -> Type) where
  -- | Memoise a function out of the key type.
  --
  -- @'lookupTable' (tabulate f)@ must agree with @f@, and must evaluate
  -- @f k@ at most once for each key @k@ however often it is looked up.  The
  -- instance 'PEG.QQ.pegGrammar' generates binds @f k@ for every constructor
  -- in a @let@ outside the lookup.
  tabulate :: (forall b. nt b -> f b) -> Table nt f

  -- | The name of the rule a key refers to.
  ruleName :: nt b -> String

-- | A reference into a type-level environment: a proof that @env@ binds some
-- name to a rule returning @a@.
--
-- The name is not in the type.  It does not have to be: a reference is built
-- by 'PEG.Syntax.nt' or 'PEG.Syntax.ntw', which state the name and demand
-- that the environment agrees about the result type.
data InEnv (env :: Env) (a :: Type) where
  InEnv :: Member n env a -> InEnv env a
