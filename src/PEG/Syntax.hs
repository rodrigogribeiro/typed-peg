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
-- 'PExp' is the core type: a GADT indexed by the input stream, the type of
-- the grammar's non-terminal keys (see "PEG.Key"), and the Haskell result
-- type.  A non-terminal reference is a key, so it can only name a rule that
-- exists and only at the type that rule has: @NT ArithEnv_expr@ for a
-- generated grammar, @nt \@\"expr\"@ for one whose environment is a
-- type-level list.
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
-- is now @PExp s nt a -> PExp s nt a@, and composes without the caller
-- having to get a nesting of type families right.  It works unchanged over
-- both kinds of key.
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
  , getOffset
  , label
  , hidden
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
import GHC.TypeLits (Symbol)

import PEG.CharSet (CharSet)
import qualified PEG.CharSet as CS
import PEG.Indent (Rel)
import PEG.Key
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
-- * 'NT'     — invoke a non-terminal, named by its key
-- * 'Seq'    — sequential composition (@e1 e2@)
-- * 'Choice' — ordered choice (@e1 \/ e2@)
-- * 'Star'   — Kleene star (@e*@)
-- * 'Not'    — negative lookahead (@!e@)
-- * 'Map'    — apply a function to the result
-- * 'Indent' — require the next token to satisfy an indentation relation
-- * 'Position'— set the column relation for tokens inside the sub-expression
-- * 'Align'  — require the next token to be aligned with the current position
-- * 'GetOffset' — consume nothing, return the offset of the current position
-- * 'Label'  — name the sub-expression in the \"expected\" list of an error
data PExp (s :: Type) (nt :: Type -> Type) (a :: Type) where
  Pure     :: a -> PExp s nt a
  Term     :: Char -> PExp s nt Char
  -- | Match one character of a class.  This is what a character class such as
  -- @[a-zA-Z0-9_]@ compiles to: a single bit test instead of a chain of
  -- ordered choices.
  Sat      :: !CharSet -> PExp s nt Char
  -- | Match a string literal.  The string must be non-empty; use 'pureP' @""@
  -- otherwise.
  --
  -- The result is the literal itself, so it is shared rather than sliced out
  -- of the input.
  Str      :: String -> PExp s nt String
  -- | Match the longest run of characters belonging to a class, possibly
  -- empty — what @[a-z]*@ compiles to.  The result is a chunk of the input
  -- stream, so on 'Data.Text.Text' this is a slice and costs no copy.
  Span     :: !CharSet -> PExp s nt s
  -- | As 'Span', but the run must be non-empty: @[a-z]+@.
  Span1    :: !CharSet -> PExp s nt s
  AnyChar  :: PExp s nt Char
  -- | A reference to the rule the key names.  Its result type is the key's
  -- index, so nothing about the rest of the grammar is consulted.
  NT       :: nt a -> PExp s nt a
  Seq      :: PExp s nt (a -> b)
           -> PExp s nt a
           -> PExp s nt b
  Choice   :: PExp s nt a
           -> PExp s nt a
           -> PExp s nt a
  -- | Kleene star.  The argument must not match the empty string, or the
  -- parser will not terminate; that is checked by "PEG.Analysis" when the
  -- grammar is spliced, and not at all when a 'Star' is built by hand.
  Star     :: PExp s nt a
           -> PExp s nt [a]
  Not      :: PExp s nt a
           -> PExp s nt ()
  Map      :: (a -> b)
           -> PExp s nt a
           -> PExp s nt b
  Indent   :: Rel n
           -> PExp s nt a
           -> PExp s nt a
  Position :: Rel n
           -> PExp s nt a
           -> PExp s nt a
  Align    :: PExp s nt a
           -> PExp s nt a
  -- | Consume nothing and return how many characters of the input have been
  -- consumed so far: the offset of the next character.  This is how a
  -- semantic action learns where a node starts or ends; "PEG.Location" turns
  -- an offset into a line and a column.  Written @\@@ in the quasi-quoter.
  GetOffset :: PExp s nt Int
  -- | Report the sub-expression, in the list of what was expected at a parse
  -- error, by a name instead of by what is inside it.  It changes nothing
  -- about what the sub-expression matches, and costs nothing unless a parse
  -- fails.  The empty name hides the sub-expression from that list.  Written
  -- @%label rule "name"@ in the quasi-quoter; see 'PEG.Parse.ParseError'.
  Label    :: String
           -> PExp s nt a
           -> PExp s nt a

instance Functor (PExp s nt) where
  fmap = Map

-- | Reference a rule of a type-level environment by name, using a type
-- application: @nt \@\"ruleName\"@.
--
-- The name is deliberately the /first/ quantified variable, so that
-- @nt \@\"expr\"@ keeps working: the stream and environment are recovered by
-- unification.
--
-- The environment is searched by the 'KnownMember' instance chain, once for
-- every occurrence, which is what makes a large environment slow to compile.
-- A grammar written with 'PEG.QQ.pegGrammar' in declaration position has
-- declared keys instead, and does not search anything.
nt :: forall n env s a.
      ( Lookup n env ~ 'EnvEntry a
      , KnownMember n env a
      )
   => PExp s (InEnv env) a
nt = NT (InEnv (member :: Member n env a))

-- | Reference a rule of a type-level environment by name, supplying the
-- membership proof: @ntw \@"ruleName" (There Here)@.
--
-- The @Lookup@ equality is kept, so this is not a weaker claim than 'nt': @a@
-- still comes from the environment, and a witness that points at a different
-- rule does not type-check.  What is gone is the 'KnownMember' search.  The
-- proof itself still costs the type checker in proportion to its depth; see
-- "PEG.Key".
ntw :: forall n env s a.
       ( Lookup n env ~ 'EnvEntry a
       )
    => Member n env a
    -> PExp s (InEnv env) a
ntw w = NT (InEnv w)

-- | Succeed without consuming any input.
pureP :: a -> PExp s nt a
pureP = Pure

-- | Apply a function to the result of an expression.
fmapP :: (a -> b) -> PExp s nt a -> PExp s nt b
fmapP = Map

-- | Require the sub-expression to satisfy the given column relation.
indent :: Rel n -> PExp s nt a -> PExp s nt a
indent = Indent

-- | Override the token mode for the sub-expression.
position :: Rel n -> PExp s nt a -> PExp s nt a
position = Position

-- | Require the sub-expression to start at the current alignment column.
align :: PExp s nt a -> PExp s nt a
align = Align

-- | The offset of the current position: the number of characters consumed
-- so far.  Consumes nothing and never fails.
getOffset :: PExp s nt Int
getOffset = GetOffset

-- | Name an expression in the \"expected\" list of a parse error: when it
-- fails at the error's position without having consumed anything, the list
-- says the name instead of what the expression was looking for.
label :: String -> PExp s nt a -> PExp s nt a
label = Label

-- | Keep an expression out of the \"expected\" list of a parse error
-- altogether: @'label' \"\"@.  Meant for whitespace and comments, which
-- could otherwise continue at almost any error.
hidden :: PExp s nt a -> PExp s nt a
hidden = Label ""

-- | Infix synonym for 'fmapP'.
(<$>.) :: (a -> b) -> PExp s nt a -> PExp s nt b
(<$>.) = Map
infixl 4 <$>.

-- | Infix sequential composition.
(<*>.) :: PExp s nt (a -> b)
       -> PExp s nt a
       -> PExp s nt b
(<*>.) = Seq
infixl 4 <*>.

-- | Sequence two expressions, discarding the result of the first.
(.>>.) :: PExp s nt a
       -> PExp s nt b
       -> PExp s nt b
e1 .>>. e2 = Map (\_ b -> b) e1 <*>. e2
infixl 6 .>>.

-- | Infix ordered choice (@e1 \/ e2@): try @e1@; if it fails, try @e2@.
(.||.) :: PExp s nt a -> PExp s nt a -> PExp s nt a
(.||.) = Choice
infixl 5 .||.

-- | Optional match: @opt e = (Just \<$\>. e) .||. pureP Nothing@.
opt :: PExp s nt a -> PExp s nt (Maybe a)
opt e = (Just <$>. e) .||. pureP Nothing

-- | One-or-more: @plus e = (:) \<$\>. e \<*\>. Star e@.
--
-- As for 'Star', @e@ must not match the empty string.
--
-- For a single character class, prefer 'spanOf1': it matches the whole run in
-- one scan and returns a chunk of the stream instead of a list.
plus :: PExp s nt a -> PExp s nt [a]
plus e = (:) <$>. e <*>. Star e

-- | Match any character of the given set.
sat :: CharSet -> PExp s nt Char
sat = Sat

-- | Match any character inside one of the given inclusive ranges.
-- This is the representation the quasi-quoter emits for @[a-z]@ and
-- friends.
charClass :: [(Char, Char)] -> PExp s nt Char
charClass = Sat . CS.fromRanges

-- | Match any character /outside/ the given inclusive ranges.
-- The quasi-quoter emits this for @[^\"]@.
notCharClass :: [(Char, Char)] -> PExp s nt Char
notCharClass = Sat . CS.notInRanges

-- | Match the longest run of characters of the set, possibly empty.  The
-- result is a chunk of the input stream.
spanOf :: CharSet -> PExp s nt s
spanOf = Span

-- | Match a non-empty run of characters of the set.
spanOf1 :: CharSet -> PExp s nt s
spanOf1 = Span1

-- | Match any character in the given list. The list must be non-empty.
oneOf :: [Char] -> PExp s nt Char
oneOf []  = error "PEG.Syntax.oneOf: empty character class"
oneOf [c] = Term c
oneOf cs  = Sat (CS.fromList cs)

-- | Match an exact string literal. The string must be non-empty.
stringNE :: String -> PExp s nt String
stringNE [] = error "PEG.Syntax.stringNE: empty string"
stringNE s  = Str s
