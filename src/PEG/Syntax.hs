{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances   #-}

-- | The PEG expression GADT and combinator API.
--
-- 'PExp' is the core type: a GADT indexed by the grammar environment,
-- the 'PEG.Type.Ty' of the expression (nullability + FIRST set), and the
-- Haskell result type.  Combinators like '<*>.' and '.||.' propagate type
-- information at the kind level so that 'PEG.Grammar.Acyclic' can be checked
-- without running the parser.
--
-- Most users will not build 'PExp' values directly; instead they use the
-- quasi-quoter in "PEG.QQ".
module PEG.Syntax
  ( Name (..)
  , PExp (..)
  , nt
  , pureP
  , fmapP
  , indent
  , position
  , align
  , (<$>.)
  , (<*>.)
  , (.>>.)
  , (.||.)
  , opt
  , plus
  , oneOf
  , stringNE
  , SeqTy
  , ChoiceTy
  , NTTy
  ) where

import Data.Kind    (Type)
import GHC.TypeLits (Symbol, KnownSymbol)

import PEG.Indent (Rel)
import PEG.Type
import PEG.TyLevel
import PEG.Member

-- | A singleton witness for a non-terminal name @s@.
data Name (s :: Symbol) = Name

-- | The 'Ty' of a sequence @e1 e2@.
type SeqTy t1 t2 =
  'MkTy (And (Nullable t1) (Nullable t2))
        (Union (First t1) (If (Nullable t1) (First t2) '[]))

-- | The 'Ty' of an ordered choice @e1 \/ e2@.
type ChoiceTy t1 t2 =
  'MkTy (Or  (Nullable t1) (Nullable t2))
        (Union (First t1) (First t2))

-- | The 'Ty' of a non-terminal reference @s@ looked up in @env@.
type NTTy s env =
  'MkTy (Nullable (TyOf (Lookup s env)))
        (ConsIfAbsent s (First (TyOf (Lookup s env))))

-- | A typed PEG expression.
--
-- Constructors correspond to the standard PEG operators:
--
-- * 'Pure'   — succeed without consuming input, return a value
-- * 'Term'   — match a specific character
-- * 'AnyChar'— match any character
-- * 'NT'     — invoke a named non-terminal
-- * 'Seq'    — sequential composition (@e1 e2@)
-- * 'Choice' — ordered choice (@e1 \/ e2@)
-- * 'Star'   — Kleene star (@e*@)
-- * 'Not'    — negative lookahead (@!e@)
-- * 'Map'    — apply a function to the result
-- * 'Indent' — require the next token to satisfy an indentation relation
-- * 'Position'— set the column relation for tokens inside the sub-expression
-- * 'Align'  — require the next token to be aligned with the current position
data PExp (env :: Env) (ty :: Ty) (a :: Type) where
  Pure     :: a -> PExp env ('MkTy 'True '[]) a
  Term     :: Char -> PExp env ('MkTy 'False '[]) Char
  AnyChar  :: PExp env ('MkTy 'False '[]) Char
  NT       :: ( KnownSymbol s
              , KnownMember s env (TyOf (Lookup s env)) (ResOf (Lookup s env))
              )
           => Name s
           -> PExp env (NTTy s env) (ResOf (Lookup s env))
  Seq      :: PExp env t1 (a -> b)
           -> PExp env t2 a
           -> PExp env (SeqTy t1 t2) b
  Choice   :: PExp env t1 a
           -> PExp env t2 a
           -> PExp env (ChoiceTy t1 t2) a
  Star     :: PExp env ('MkTy 'False f) a
           -> PExp env ('MkTy 'True  f) [a]
  Not      :: PExp env ('MkTy n f) a
           -> PExp env ('MkTy 'True f) ()
  Map      :: (a -> b)
           -> PExp env ty a
           -> PExp env ty b
  Indent   :: Rel n
           -> PExp env ty a
           -> PExp env ty a
  Position :: Rel n
           -> PExp env ty a
           -> PExp env ty a
  Align    :: PExp env ty a
           -> PExp env ty a

instance Functor (PExp env ty) where
  fmap = Map

-- | Reference a non-terminal by name using a type application:
-- @nt \@\"ruleName\"@.
nt :: forall s env.
      ( KnownSymbol s
      , KnownMember s env (TyOf (Lookup s env)) (ResOf (Lookup s env))
      )
   => PExp env (NTTy s env) (ResOf (Lookup s env))
nt = NT (Name :: Name s)

-- | Succeed without consuming any input.
pureP :: a -> PExp env ('MkTy 'True '[]) a
pureP = Pure

-- | Apply a function to the result of an expression.
fmapP :: (a -> b) -> PExp env ty a -> PExp env ty b
fmapP = Map

-- | Require the sub-expression to satisfy the given column relation.
indent :: Rel n -> PExp env ty a -> PExp env ty a
indent = Indent

-- | Override the token mode for the sub-expression.
position :: Rel n -> PExp env ty a -> PExp env ty a
position = Position

-- | Require the sub-expression to start at the current alignment column.
align :: PExp env ty a -> PExp env ty a
align = Align

-- | Infix synonym for 'fmapP'.
(<$>.) :: (a -> b) -> PExp env ty a -> PExp env ty b
(<$>.) = Map
infixl 4 <$>.

-- | Infix sequential composition.
(<*>.) :: PExp env t1 (a -> b)
       -> PExp env t2 a
       -> PExp env (SeqTy t1 t2) b
(<*>.) = Seq
infixl 4 <*>.

-- | Sequence two expressions, discarding the result of the first.
(.>>.) :: PExp env t1 a
       -> PExp env t2 b
       -> PExp env (SeqTy t1 t2) b
e1 .>>. e2 = Map (\_ b -> b) e1 <*>. e2
infixl 6 .>>.

-- | Infix ordered choice (@e1 \/ e2@): try @e1@; if it fails, try @e2@.
(.||.) :: PExp env t1 a -> PExp env t2 a -> PExp env (ChoiceTy t1 t2) a
(.||.) = Choice
infixl 5 .||.

-- | Optional match: @opt e = (Just \<$\>. e) .||. pureP Nothing@.
opt :: PExp env t a
    -> PExp env (ChoiceTy t ('MkTy 'True '[])) (Maybe a)
opt e = (Just <$>. e) .||. pureP Nothing

-- | One-or-more: @plus e = (:) \<$\>. e \<*\>. Star e@.
plus :: PExp env ('MkTy 'False f) a
     -> PExp env (SeqTy ('MkTy 'False f) ('MkTy 'True f)) [a]
plus e = (:) <$>. e <*>. Star e

-- | Match any character in the given list. The list must be non-empty.
oneOf :: [Char] -> PExp env ('MkTy 'False '[]) Char
oneOf []     = error "PEG.Syntax.oneOf: empty character class"
oneOf [c]    = Term c
oneOf (c:cs) = Term c .||. oneOf cs

-- | Match an exact string literal. The string must be non-empty.
stringNE :: String -> PExp env ('MkTy 'False '[]) String
stringNE []     = error "PEG.Syntax.stringNE: empty string"
stringNE [c]    = (\x -> [x]) <$>. Term c
stringNE (c:cs) = (:) <$>. Term c <*>. stringNE cs
