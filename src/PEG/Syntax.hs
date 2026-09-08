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
-- 'PExp' is the core type: a GADT indexed by the input stream, the grammar
-- environment, the 'PEG.Type.Ty' of the expression (nullability + FIRST set),
-- and the Haskell result type.  Combinators like '<*>.' and '.||.' propagate
-- type information at the kind level so that 'PEG.Grammar.Acyclic' can be
-- checked without running the parser.
--
-- The first parameter, @s@, is the stream the expression consumes; see
-- "PEG.Stream".  It appears in the type because a character class produces a
-- /chunk of that stream/ — matching @[a-z]+@ against a 'Data.Text.Text'
-- yields a 'Data.Text.Text' slice, not a @['Char']@.
--
-- Most users will not build 'PExp' values directly; instead they use the
-- quasi-quoter in "PEG.QQ".
module PEG.Syntax
  ( Name (..)
  , PExp (..)
  , nt
  , sat
  , charClass
  , notCharClass
  , spanOf
  , spanOf1
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
  , NTGo
  ) where

import Data.Kind    (Type)
import GHC.TypeLits (Symbol, KnownSymbol)

import PEG.CharSet (CharSet)
import qualified PEG.CharSet as CS
import PEG.Indent (Rel)
import PEG.Type
import PEG.TyLevel
import PEG.Member

-- | A singleton witness for a non-terminal name @n@.
data Name (n :: Symbol) = Name

-- | The 'Ty' of a sequence @e1 e2@.
--
-- Written as a projective type synonym rather than a type family so that it
-- reduces to a @'MkTy'@ head even when its operands are still abstract.  That
-- is what lets a polymorphic combinator such as
--
-- @
-- lexeme :: PExp s env ty a -> PExp s env (SeqTy ty ('MkTy 'True '[])) a
-- @
--
-- compose without the caller having to get the nesting of 'SeqTy' exactly
-- right.  The cost it used to carry — an exponential blow-up as the operands
-- get duplicated across the right-hand side — came from 'Union' and
-- 'ConsIfAbsent', not from here; see "PEG.TyLevel".
type SeqTy t1 t2 =
  'MkTy (And (Nullable t1) (Nullable t2))
        (Union (First t1) (If (Nullable t1) (First t2) '[]))

-- | The 'Ty' of an ordered choice @e1 \/ e2@.
type ChoiceTy t1 t2 =
  'MkTy (Or  (Nullable t1) (Nullable t2))
        (Union (First t1) (First t2))

-- | The 'Ty' of a non-terminal reference @n@ looked up in @env@.
type NTTy n env = NTGo n (TyOf (Lookup n env))

-- | The 'Ty' of a reference to a non-terminal named @n@ whose own 'Ty' is
-- @t@.
--
-- 'NT' and 'nt' are stated in terms of this rather than 'NTTy' so that the
-- environment is searched /once/ per occurrence, by the constructor's
-- @Lookup n env ~ 'EnvEntry ty a@ equality.  Naming @Lookup n env@ twice, as
-- an expansion of 'NTTy' does, doubles the cost of what profiling shows to be
-- the dominant term in checking a large grammar.
type family NTGo (n :: Symbol) (t :: Ty) :: Ty where
  NTGo n ('MkTy nu f) = 'MkTy nu (ConsIfAbsent n f)

-- | A typed PEG expression over the stream @s@.
--
-- Constructors correspond to the standard PEG operators:
--
-- * 'Pure'   — succeed without consuming input, return a value
-- * 'Term'   — match a specific character
-- * 'Sat'    — match any character of a 'CharSet' (a character class)
-- * 'Str'    — match a non-empty string literal
-- * 'Span'   — match a run of characters of a 'CharSet', possibly empty
-- * 'Span1'  — match a non-empty run of characters of a 'CharSet'
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
data PExp (s :: Type) (env :: Env) (ty :: Ty) (a :: Type) where
  Pure     :: a -> PExp s env ('MkTy 'True '[]) a
  Term     :: Char -> PExp s env ('MkTy 'False '[]) Char
  -- | Match one character of a class.  This is what a character class such as
  -- @[a-zA-Z0-9_]@ compiles to: a single bit test instead of a chain of
  -- ordered choices.
  Sat      :: !CharSet -> PExp s env ('MkTy 'False '[]) Char
  -- | Match a string literal.  The string must be non-empty (the 'Ty' index
  -- claims the expression is not nullable); use 'pureP' @""@ otherwise.
  --
  -- The result is the literal itself, so it is shared rather than sliced out
  -- of the input.
  Str      :: String -> PExp s env ('MkTy 'False '[]) String
  -- | Match the longest run of characters belonging to a class, possibly
  -- empty — what @[a-z]*@ compiles to.  The result is a chunk of the input
  -- stream, so on 'Data.Text.Text' this is a slice and costs no copy.
  Span     :: !CharSet -> PExp s env ('MkTy 'True  '[]) s
  -- | As 'Span', but the run must be non-empty: @[a-z]+@.
  Span1    :: !CharSet -> PExp s env ('MkTy 'False '[]) s
  AnyChar  :: PExp s env ('MkTy 'False '[]) Char
  -- The environment is looked up /once/, by the equality below, and the
  -- result is bound to the rigid variables @ty@ and @a@.  Passing
  -- @TyOf (Lookup n env)@ straight to 'KnownMember' instead makes GHC
  -- re-reduce the lookup at every step of the instance chain that walks
  -- @env@, which costs @O(|env|^2)@ per non-terminal occurrence.
  NT       :: forall n ty s env a.
              ( KnownSymbol n
              , Lookup n env ~ 'EnvEntry ty a
              , KnownMember n env a
              )
           => Name n
           -> PExp s env (NTGo n ty) a
  Seq      :: PExp s env t1 (a -> b)
           -> PExp s env t2 a
           -> PExp s env (SeqTy t1 t2) b
  Choice   :: PExp s env t1 a
           -> PExp s env t2 a
           -> PExp s env (ChoiceTy t1 t2) a
  Star     :: PExp s env ('MkTy 'False f) a
           -> PExp s env ('MkTy 'True  f) [a]
  Not      :: PExp s env ('MkTy n f) a
           -> PExp s env ('MkTy 'True f) ()
  Map      :: (a -> b)
           -> PExp s env ty a
           -> PExp s env ty b
  Indent   :: Rel n
           -> PExp s env ty a
           -> PExp s env ty a
  Position :: Rel n
           -> PExp s env ty a
           -> PExp s env ty a
  Align    :: PExp s env ty a
           -> PExp s env ty a

instance Functor (PExp s env ty) where
  fmap = Map

-- | Reference a non-terminal by name using a type application:
-- @nt \@\"ruleName\"@.
--
-- The name is deliberately the /first/ quantified variable, so that
-- @nt \@\"expr\"@ keeps working: the stream and environment are recovered by
-- unification.
nt :: forall n env s ty a.
      ( KnownSymbol n
      , Lookup n env ~ 'EnvEntry ty a
      , KnownMember n env a
      )
   => PExp s env (NTGo n ty) a
nt = NT (Name :: Name n)

-- | Succeed without consuming any input.
pureP :: a -> PExp s env ('MkTy 'True '[]) a
pureP = Pure

-- | Apply a function to the result of an expression.
fmapP :: (a -> b) -> PExp s env ty a -> PExp s env ty b
fmapP = Map

-- | Require the sub-expression to satisfy the given column relation.
indent :: Rel n -> PExp s env ty a -> PExp s env ty a
indent = Indent

-- | Override the token mode for the sub-expression.
position :: Rel n -> PExp s env ty a -> PExp s env ty a
position = Position

-- | Require the sub-expression to start at the current alignment column.
align :: PExp s env ty a -> PExp s env ty a
align = Align

-- | Infix synonym for 'fmapP'.
(<$>.) :: (a -> b) -> PExp s env ty a -> PExp s env ty b
(<$>.) = Map
infixl 4 <$>.

-- | Infix sequential composition.
(<*>.) :: PExp s env t1 (a -> b)
       -> PExp s env t2 a
       -> PExp s env (SeqTy t1 t2) b
(<*>.) = Seq
infixl 4 <*>.

-- | Sequence two expressions, discarding the result of the first.
(.>>.) :: PExp s env t1 a
       -> PExp s env t2 b
       -> PExp s env (SeqTy t1 t2) b
e1 .>>. e2 = Map (\_ b -> b) e1 <*>. e2
infixl 6 .>>.

-- | Infix ordered choice (@e1 \/ e2@): try @e1@; if it fails, try @e2@.
(.||.) :: PExp s env t1 a -> PExp s env t2 a -> PExp s env (ChoiceTy t1 t2) a
(.||.) = Choice
infixl 5 .||.

-- | Optional match: @opt e = (Just \<$\>. e) .||. pureP Nothing@.
opt :: PExp s env t a
    -> PExp s env (ChoiceTy t ('MkTy 'True '[])) (Maybe a)
opt e = (Just <$>. e) .||. pureP Nothing

-- | One-or-more: @plus e = (:) \<$\>. e \<*\>. Star e@.
--
-- For a single character class, prefer 'spanOf1': it matches the whole run in
-- one scan and returns a chunk of the stream instead of a list.
plus :: PExp s env ('MkTy 'False f) a
     -> PExp s env (SeqTy ('MkTy 'False f) ('MkTy 'True f)) [a]
plus e = (:) <$>. e <*>. Star e

-- | Match any character of the given set.
sat :: CharSet -> PExp s env ('MkTy 'False '[]) Char
sat = Sat

-- | Match any character inside one of the given inclusive ranges.
-- This is the representation the quasi-quoter emits for @[a-z0-9]@ and
-- friends.
charClass :: [(Char, Char)] -> PExp s env ('MkTy 'False '[]) Char
charClass = Sat . CS.fromRanges

-- | Match any character /outside/ the given inclusive ranges.
-- The quasi-quoter emits this for @[^\"]@.
notCharClass :: [(Char, Char)] -> PExp s env ('MkTy 'False '[]) Char
notCharClass = Sat . CS.notInRanges

-- | Match the longest run of characters of the set, possibly empty.  The
-- result is a chunk of the input stream.
spanOf :: CharSet -> PExp s env ('MkTy 'True '[]) s
spanOf = Span

-- | Match a non-empty run of characters of the set.
spanOf1 :: CharSet -> PExp s env ('MkTy 'False '[]) s
spanOf1 = Span1

-- | Match any character in the given list. The list must be non-empty.
oneOf :: [Char] -> PExp s env ('MkTy 'False '[]) Char
oneOf []  = error "PEG.Syntax.oneOf: empty character class"
oneOf [c] = Term c
oneOf cs  = Sat (CS.fromList cs)

-- | Match an exact string literal. The string must be non-empty.
stringNE :: String -> PExp s env ('MkTy 'False '[]) String
stringNE [] = error "PEG.Syntax.stringNE: empty string"
stringNE s  = Str s
