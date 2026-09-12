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
-- environment, and the Haskell result type.  Every non-terminal reference is
-- checked against the environment, so @nt \@\"expr\"@ is a type error unless
-- the grammar has a rule called @expr@, and it has whatever type that rule
-- has.
--
-- The first parameter, @s@, is the stream the expression consumes; see
-- "PEG.Stream".  It appears in the type because a character class produces a
-- /chunk of that stream/ — matching @[a-z]+@ against a 'Data.Text.Text'
-- yields a 'Data.Text.Text' slice, not a @['Char']@.
--
-- Most users will not build 'PExp' values directly; instead they use the
-- quasi-quoter in "PEG.QQ".
--
-- == What is no longer in the index
--
-- A 'PExp' used to carry a fourth index, its nullability and FIRST set, from
-- which @PEG.Grammar.Acyclic@ derived a type error for a left-recursive
-- grammar.  Both are still computed and left recursion is still rejected, by
-- "PEG.Analysis" when the grammar is spliced rather than by GHC on every
-- compilation that mentions it; "PEG.Type" says what that cost and what it
-- buys, and "PEG.Grammar" says what it gives up.
--
-- One consequence shows up here rather than there.  'Star' used to demand a
-- non-nullable argument, so that @e*@ on an @e@ matching the empty string was
-- a type error; now nothing in the type stops it, and it is "PEG.Analysis"
-- that reports it.  A 'Star' built by hand over a nullable expression will
-- loop at run time.
--
-- The other consequence is that a combinator over expressions is now an
-- ordinary polymorphic function.  What had to be written
--
-- @
-- lexeme :: PExp s env ty a -> PExp s env (SeqTy ty ('MkTy 'True '[])) a
-- @
--
-- is now @PExp s env a -> PExp s env a@, and composes without the caller
-- having to get a nesting of type families right.
module PEG.Syntax
  ( Name (..)
  , PExp (..)
  , nt
  , ntw
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
data PExp (s :: Type) (env :: Env) (a :: Type) where
  Pure     :: a -> PExp s env a
  Term     :: Char -> PExp s env Char
  -- | Match one character of a class.  This is what a character class such as
  -- @[a-zA-Z0-9_]@ compiles to: a single bit test instead of a chain of
  -- ordered choices.
  Sat      :: !CharSet -> PExp s env Char
  -- | Match a string literal.  The string must be non-empty; use 'pureP' @""@
  -- otherwise.
  --
  -- The result is the literal itself, so it is shared rather than sliced out
  -- of the input.
  Str      :: String -> PExp s env String
  -- | Match the longest run of characters belonging to a class, possibly
  -- empty — what @[a-z]*@ compiles to.  The result is a chunk of the input
  -- stream, so on 'Data.Text.Text' this is a slice and costs no copy.
  Span     :: !CharSet -> PExp s env s
  -- | As 'Span', but the run must be non-empty: @[a-z]+@.
  Span1    :: !CharSet -> PExp s env s
  AnyChar  :: PExp s env Char
  -- The environment is looked up /once/, by the equality below, and the
  -- result is bound to the rigid variable @a@.  Passing @ResOf (Lookup n
  -- env)@ straight to 'KnownMember' instead makes GHC re-reduce the lookup at
  -- every step of the instance chain that walks @env@, which costs
  -- @O(|env|^2)@ per non-terminal occurrence.
  NT       :: forall n s env a.
              ( KnownSymbol n
              , Lookup n env ~ 'EnvEntry a
              , KnownMember n env a
              )
           => Name n
           -> PExp s env a
  -- | As 'NT', but the proof that the rule is in the environment is supplied
  -- rather than searched for.
  --
  -- The @Lookup@ equality is kept, so this is not a weaker claim than 'NT':
  -- @a@ still comes from the environment, and a witness that points at a
  -- different rule does not type-check.  What is gone is the 'KnownMember'
  -- instance chain, which walks the environment one entry at a time for every
  -- occurrence of every non-terminal.  On a 64-rule grammar that chain is
  -- about three quarters of what resolving a reference costs; see
  -- @bench-compile/@.
  --
  -- A splice knows each rule's position and so can write the witness down.
  -- Hand-written grammars have nothing to gain here and should keep using
  -- 'nt'.
  NTW      :: forall n s env a.
              ( KnownSymbol n
              , Lookup n env ~ 'EnvEntry a
              )
           => Name n
           -> Member n env a
           -> PExp s env a
  Seq      :: PExp s env (a -> b)
           -> PExp s env a
           -> PExp s env b
  Choice   :: PExp s env a
           -> PExp s env a
           -> PExp s env a
  -- | Kleene star.  The argument must not match the empty string, or the
  -- parser will not terminate; that is checked by "PEG.Analysis" when the
  -- grammar is spliced, and not at all when a 'Star' is built by hand.
  Star     :: PExp s env a
           -> PExp s env [a]
  Not      :: PExp s env a
           -> PExp s env ()
  Map      :: (a -> b)
           -> PExp s env a
           -> PExp s env b
  Indent   :: Rel n
           -> PExp s env a
           -> PExp s env a
  Position :: Rel n
           -> PExp s env a
           -> PExp s env a
  Align    :: PExp s env a
           -> PExp s env a

instance Functor (PExp s env) where
  fmap = Map

-- | Reference a non-terminal by name using a type application:
-- @nt \@\"ruleName\"@.
--
-- The name is deliberately the /first/ quantified variable, so that
-- @nt \@\"expr\"@ keeps working: the stream and environment are recovered by
-- unification.
nt :: forall n env s a.
      ( KnownSymbol n
      , Lookup n env ~ 'EnvEntry a
      , KnownMember n env a
      )
   => PExp s env a
nt = NT (Name :: Name n)

-- | Reference a non-terminal by name, supplying the membership proof:
-- @ntw \@"ruleName" (There Here)@.
--
-- This is what a generated grammar emits; see 'NTW'.
ntw :: forall n env s a.
       ( KnownSymbol n
       , Lookup n env ~ 'EnvEntry a
       )
    => Member n env a
    -> PExp s env a
ntw = NTW (Name :: Name n)

-- | Succeed without consuming any input.
pureP :: a -> PExp s env a
pureP = Pure

-- | Apply a function to the result of an expression.
fmapP :: (a -> b) -> PExp s env a -> PExp s env b
fmapP = Map

-- | Require the sub-expression to satisfy the given column relation.
indent :: Rel n -> PExp s env a -> PExp s env a
indent = Indent

-- | Override the token mode for the sub-expression.
position :: Rel n -> PExp s env a -> PExp s env a
position = Position

-- | Require the sub-expression to start at the current alignment column.
align :: PExp s env a -> PExp s env a
align = Align

-- | Infix synonym for 'fmapP'.
(<$>.) :: (a -> b) -> PExp s env a -> PExp s env b
(<$>.) = Map
infixl 4 <$>.

-- | Infix sequential composition.
(<*>.) :: PExp s env (a -> b)
       -> PExp s env a
       -> PExp s env b
(<*>.) = Seq
infixl 4 <*>.

-- | Sequence two expressions, discarding the result of the first.
(.>>.) :: PExp s env a
       -> PExp s env b
       -> PExp s env b
e1 .>>. e2 = Map (\_ b -> b) e1 <*>. e2
infixl 6 .>>.

-- | Infix ordered choice (@e1 \/ e2@): try @e1@; if it fails, try @e2@.
(.||.) :: PExp s env a -> PExp s env a -> PExp s env a
(.||.) = Choice
infixl 5 .||.

-- | Optional match: @opt e = (Just \<$\>. e) .||. pureP Nothing@.
opt :: PExp s env a -> PExp s env (Maybe a)
opt e = (Just <$>. e) .||. pureP Nothing

-- | One-or-more: @plus e = (:) \<$\>. e \<*\>. Star e@.
--
-- As for 'Star', @e@ must not match the empty string.
--
-- For a single character class, prefer 'spanOf1': it matches the whole run in
-- one scan and returns a chunk of the stream instead of a list.
plus :: PExp s env a -> PExp s env [a]
plus e = (:) <$>. e <*>. Star e

-- | Match any character of the given set.
sat :: CharSet -> PExp s env Char
sat = Sat

-- | Match any character inside one of the given inclusive ranges.
-- This is the representation the quasi-quoter emits for @[a-z]@ and
-- friends.
charClass :: [(Char, Char)] -> PExp s env Char
charClass = Sat . CS.fromRanges

-- | Match any character /outside/ the given inclusive ranges.
-- The quasi-quoter emits this for @[^\"]@.
notCharClass :: [(Char, Char)] -> PExp s env Char
notCharClass = Sat . CS.notInRanges

-- | Match the longest run of characters of the set, possibly empty.  The
-- result is a chunk of the input stream.
spanOf :: CharSet -> PExp s env s
spanOf = Span

-- | Match a non-empty run of characters of the set.
spanOf1 :: CharSet -> PExp s env s
spanOf1 = Span1

-- | Match any character in the given list. The list must be non-empty.
oneOf :: [Char] -> PExp s env Char
oneOf []  = error "PEG.Syntax.oneOf: empty character class"
oneOf [c] = Term c
oneOf cs  = Sat (CS.fromList cs)

-- | Match an exact string literal. The string must be non-empty.
stringNE :: String -> PExp s env String
stringNE [] = error "PEG.Syntax.stringNE: empty string"
stringNE s  = Str s
