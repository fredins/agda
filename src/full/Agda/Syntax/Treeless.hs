{-# LANGUAGE PatternSynonyms #-}

-- | The treeless syntax is intended to be used as input for the compiler backends.
-- It is more low-level than Internal syntax and is not used for type checking.
--
-- Some of the features of treeless syntax are:
-- - case expressions instead of case trees
-- - no instantiated datatypes / constructors
module Agda.Syntax.Treeless
    ( module Agda.Syntax.Abstract.Name
    , module Agda.Syntax.Treeless
    ) where

import Control.Arrow (first, second)
import Control.DeepSeq
import Control.Monad.Reader

import Data.Map (Map)
import Data.Maybe (fromMaybe, isJust)
import qualified Data.Map as Map
import Data.Semigroup (All(..), Any(..) )
import Data.Word

import GHC.Generics (Generic)

import Agda.Syntax.Position
import Agda.Syntax.Literal
import Agda.Syntax.Common
import Agda.Syntax.Abstract.Name
import Agda.TypeChecking.Substitute
import Agda.Utils.Impossible
import Agda.Utils.List
import Agda.Utils.Pretty

data Compiled = Compiled
  { cTreeless :: TTerm
  , cArgUsage :: Maybe [ArgUsage]
      -- ^ 'Nothing' if treeless usage analysis has not run yet.
  }
  deriving (Show, Eq, Ord, Generic)

-- | Usage status of function arguments in treeless code.
data ArgUsage
  = ArgUsed
  | ArgUnused
  deriving (Show, Eq, Ord, Generic)

-- | The treeless compiler can behave differently depending on the target
--   language evaluation strategy. For instance, more aggressive erasure for
--   lazy targets.
data EvaluationStrategy = LazyEvaluation | EagerEvaluation
  deriving (Eq, Show)

type Args = [TTerm]

-- this currently assumes that TApp is translated in a lazy/cbn fashion.
-- The AST should also support strict translation.
--
-- | Treeless Term. All local variables are using de Bruijn indices.
data TTerm = TVar Int
           | TPrim TPrim
           | TDef QName
           | TApp TTerm Args
           | TLam TTerm
           | TLit Literal
           | TCon QName
           | TLet TTerm TTerm
           -- ^ introduces a new (non-recursive) local binding. The bound term
           -- MUST only be evaluated if it is used inside the body.
           -- Sharing may happen, but is optional.
           -- It is also perfectly valid to just inline the bound term in the body.
           | TCase Int CaseInfo TTerm [TAlt]
           -- ^ Case scrutinee (always variable), case type, default value, alternatives
           -- First, all TACon alternatives are tried; then all TAGuard alternatives
           -- in top to bottom order.
           -- TACon alternatives must not overlap.
           | TUnit -- used for levels right now
           | TSort
           | TErased
           | TCoerce TTerm  -- ^ Used by the GHC backend
           | TError TError
           -- ^ A runtime error, something bad has happened.
  deriving (Show, Eq, Ord, Generic)

-- | Compiler-related primitives. This are NOT the same thing as primitives
-- in Agda's surface or internal syntax!
-- Some of the primitives have a suffix indicating which type of arguments they take,
-- using the following naming convention:
-- Char | Type
-- C    | Character
-- F    | Float
-- I    | Integer
-- Q    | QName
-- S    | String
data TPrim
  = PAdd | PAdd64
  | PSub | PSub64
  | PMul | PMul64
  | PQuot | PQuot64
  | PRem  | PRem64
  | PGeq
  | PLt   | PLt64
  | PEqI  | PEq64
  | PEqF
  | PEqS
  | PEqC
  | PEqQ
  | PIf
  | PSeq
  | PITo64 | P64ToI
  deriving (Show, Eq, Ord, Generic)

instance Pretty Compiled where
  pretty Compiled {cTreeless, cArgUsage} =
    "Compiled {" <?> vcat
      [ "cTreeless   =" <?> pretty cTreeless
      , "funCompiled =" <?> pshow cArgUsage
      ] <?> "}"

isPrimEq :: TPrim -> Bool
isPrimEq p = p `elem` [PEqI, PEqF, PEqS, PEqC, PEqQ, PEq64]

-- | Strip leading coercions and indicate whether there were some.
coerceView :: TTerm -> (Bool, TTerm)
coerceView = \case
  TCoerce t -> (True,) $ snd $ coerceView t
  t         -> (False, t)

mkTApp :: TTerm -> Args -> TTerm
mkTApp x           [] = x
mkTApp (TApp x as) bs = TApp x (as ++ bs)
mkTApp x           as = TApp x as

tAppView :: TTerm -> (TTerm, [TTerm])
tAppView = \case
  TApp a bs -> second (++ bs) $ tAppView a
  t         -> (t, [])

-- | Expose the format @coerce f args@.
--
--   We fuse coercions, even if interleaving with applications.
--   We assume that coercion is powerful enough to satisfy
--   @
--      coerce (coerce f a) b = coerce f a b
--   @
coerceAppView :: TTerm -> ((Bool, TTerm), [TTerm])
coerceAppView = \case
  TCoerce t -> first ((True,) . snd) $ coerceAppView t
  TApp a bs -> second (++ bs) $ coerceAppView a
  t         -> ((False, t), [])

tLetView :: TTerm -> ([TTerm], TTerm)
tLetView (TLet e b) = first (e :) $ tLetView b
tLetView e          = ([], e)

tLamView :: TTerm -> (Int, TTerm)
tLamView = go 0
  where go n (TLam b) = go (n + 1) b
        go n t        = (n, t)

mkTLam :: Int -> TTerm -> TTerm
mkTLam n b = foldr ($) b $ replicate n TLam

-- | Introduces a new binding
mkLet :: TTerm -> TTerm -> TTerm
mkLet x body = TLet x body

tInt :: Integer -> TTerm
tInt = TLit . LitNat

intView :: TTerm -> Maybe Integer
intView (TLit (LitNat x)) = Just x
intView _ = Nothing

word64View :: TTerm -> Maybe Word64
word64View (TLit (LitWord64 x)) = Just x
word64View _ = Nothing

tPlusK :: Integer -> TTerm -> TTerm
tPlusK 0 n = n
tPlusK k n | k < 0 = tOp PSub n (tInt (-k))
tPlusK k n = tOp PAdd (tInt k) n

-- -(k + n)
tNegPlusK :: Integer -> TTerm -> TTerm
tNegPlusK k n = tOp PSub (tInt (-k)) n

plusKView :: TTerm -> Maybe (Integer, TTerm)
plusKView (TApp (TPrim PAdd) [k, n]) | Just k <- intView k = Just (k, n)
plusKView (TApp (TPrim PSub) [n, k]) | Just k <- intView k = Just (-k, n)
plusKView _ = Nothing

negPlusKView :: TTerm -> Maybe (Integer, TTerm)
negPlusKView (TApp (TPrim PSub) [k, n]) | Just k <- intView k = Just (-k, n)
negPlusKView _ = Nothing

tOp :: TPrim -> TTerm -> TTerm -> TTerm
tOp op a b = TPOp op a b

pattern TPOp :: TPrim -> TTerm -> TTerm -> TTerm
pattern TPOp op a b = TApp (TPrim op) [a, b]

pattern TPFn :: TPrim -> TTerm -> TTerm
pattern TPFn op a = TApp (TPrim op) [a]

tUnreachable :: TTerm
tUnreachable = TError TUnreachable

tIfThenElse :: TTerm -> TTerm -> TTerm -> TTerm
tIfThenElse c i e = TApp (TPrim PIf) [c, i, e]

data CaseType
  = CTData QName
    -- Case on datatype.
  | CTNat
  | CTInt
  | CTChar
  | CTString
  | CTFloat
  | CTQName
  deriving (Show, Eq, Ord, Generic)

data CaseInfo = CaseInfo
  { caseLazy :: Bool
  , caseErased :: Erased
    -- ^ Is this a match on an erased argument?
  , caseType :: CaseType }
  deriving (Show, Eq, Ord, Generic)

data TAlt
  = TACon    { aCon  :: QName, aArity :: Int, aBody :: TTerm }
  -- ^ Matches on the given constructor. If the match succeeds,
  -- the pattern variables are prepended to the current environment
  -- (pushes all existing variables aArity steps further away)
  | TAGuard  { aGuard :: TTerm, aBody :: TTerm }
  -- ^ Binds no variables
  --
  -- The guard must only use the variable that the case expression
  -- matches on.
  | TALit    { aLit :: Literal,   aBody:: TTerm }
  deriving (Show, Eq, Ord, Generic)

data TError
  = TUnreachable
  -- ^ Code which is unreachable. E.g. absurd branches or missing case defaults.
  -- Runtime behaviour of unreachable code is undefined, but preferably
  -- the program will exit with an error message. The compiler is free
  -- to assume that this code is unreachable and to remove it.
  | TMeta String
  -- ^ Code which could not be obtained because of a hole in the program.
  -- This should throw a runtime error.
  -- The string gives some information about the meta variable that got compiled.
  deriving (Show, Eq, Ord, Generic)


class Unreachable a where
  -- | Checks if the given expression is unreachable or not.
  isUnreachable :: a -> Bool

instance Unreachable TAlt where
  isUnreachable = isUnreachable . aBody

instance Unreachable TTerm where
  isUnreachable (TError TUnreachable{}) = True
  isUnreachable (TLet _ b) = isUnreachable b
  isUnreachable _ = False

instance KillRange Compiled where
  killRange c = c -- bogus, but not used anyway


-- * Utilities for ArgUsage
---------------------------------------------------------------------------

-- | @filterUsed used args@ drops those @args@ which are labelled
-- @ArgUnused@ in list @used@.
--
-- Specification:
--
-- @
--   filterUsed used args = [ a | (a, ArgUsed) <- zip args $ used ++ repeat ArgUsed ]
-- @
--
-- Examples:
--
-- @
--   filterUsed []                 == id
--   filterUsed (repeat ArgUsed)   == id
--   filterUsed (repeat ArgUnused) == const []
-- @
filterUsed :: [ArgUsage] -> [a] -> [a]
filterUsed = curry $ \case
  ([], args) -> args
  (_ , [])   -> []
  (ArgUsed   : used, a : args) -> a : filterUsed used args
  (ArgUnused : used, a : args) ->     filterUsed used args


-- * Pretty instances
---------------------------------------------------------------------------

data PEnv = PEnv { pPrec :: Int
                 , pFresh :: [String]
                 , pBound :: [String] }

type P = Reader PEnv

--UNUSED Liang-Ting Chen 2019-07-16
--withName :: (String -> P a) -> P a
--withName k = withNames 1 $ \[x] -> k x

withNames :: Int -> ([String] -> P a) -> P a
withNames n k = do
  (xs, ys) <- asks $ splitAt n . pFresh
  local (\ e -> e { pFresh = ys }) (k xs)

-- | Don't generate fresh names for unused variables.
withNames' :: HasFree a => Int -> a -> ([String] -> P b) -> P b
withNames' n tm k = withNames n' $ k . insBlanks
  where
    fv = freeVars tm
    n'  = length $ filter (< n) $ Map.keys fv
    insBlanks = go n
      where
        go 0 _ = []
        go i xs0@(~(x : xs))
          | Map.member (i - 1) fv = x   : go (i - 1) xs
          | otherwise             = "_" : go (i - 1) xs0

bindName :: String -> P a -> P a
bindName x = local $ \ e -> e { pBound = x : pBound e }

bindNames :: [String] -> P a -> P a
bindNames xs p = foldr bindName p xs

paren :: Int -> P Doc -> P Doc
paren p doc = do
  n <- asks pPrec
  (if p < n then parens else id) <$> doc

prec :: Int -> P a -> P a
prec p = local $ \ e -> e { pPrec = p }

name :: Int -> P String
name x = asks
  $ (\ xs -> indexWithDefault __IMPOSSIBLE__ xs x)
  . (++ map (("^" ++) . show) [1..])
  . pBound

runP :: P a -> a
runP p = runReader p PEnv{ pPrec = 0, pFresh = names, pBound = [] }
  where
    names = [ x ++ i | i <- "" : map show [1..], x <- map (:[]) ['a'..'z'] ]

instance Pretty TTerm where
  prettyPrec p t = runP $ prec p (pTerm t)

opName :: TPrim -> String
opName PAdd = "+"
opName PSub = "-"
opName PMul = "*"
opName PQuot = "quot"
opName PRem = "rem"
opName PGeq = ">="
opName PLt  = "<"
opName PEqI = "==I"
opName PAdd64 = "+64"
opName PSub64 = "-64"
opName PMul64 = "*64"
opName PQuot64 = "quot64"
opName PRem64 = "rem64"
opName PLt64  = "<64"
opName PEq64 = "==64"
opName PEqF = "==F"
opName PEqS = "==S"
opName PEqC = "==C"
opName PEqQ = "==Q"
opName PIf  = "if_then_else_"
opName PSeq = "seq"
opName PITo64 = "toWord64"
opName P64ToI = "fromWord64"


isInfix :: TPrim -> Maybe (Int, Int, Int)
isInfix op =
  case op of
    PMul -> l 7
    PAdd -> l 6
    PSub -> l 6
    PGeq -> non 4
    PLt  -> non 4
    PMul64 -> l 7
    PAdd64 -> l 6
    PSub64 -> l 6
    PLt64  -> non 4
    p | isPrimEq p -> non 4
    _    -> Nothing
  where
    l n   = Just (n, n, n + 1)
    r n   = Just (n, n + 1, n) -- NB:: Defined but not used
    non n = Just (n, n + 1, n + 1)

pTerm' :: Int -> TTerm -> P Doc
pTerm' p = prec p . pTerm

pTerm :: TTerm -> P Doc
pTerm = \case
  TVar x -> text <$> name x
  TApp (TPrim op) [a, b] | Just (c, l, r) <- isInfix op ->
    paren c $ sep <$> sequence [ pTerm' l a
                               , pure $ text $ opName op
                               , pTerm' r b ]
  TApp (TPrim PIf) [a, b, c] ->
    paren 0 $ (\ a b c -> sep [ "if" <+> a
                              , nest 2 $ "then" <+> b
                              , nest 2 $ "else" <+> c ])
              <$> pTerm' 0 a
              <*> pTerm' 0 b
              <*> pTerm c
  TDef f -> pure $ pretty f
  TCon c -> pure $ pretty c
  TLit l -> pure $ pretty l
  TPrim op | isJust (isInfix op) -> pure $ text ("_" ++ opName op ++ "_")
           | otherwise -> pure $ text (opName op)
  TApp f es ->
    paren 9 $ (\a bs -> sep [a, nest 2 $ fsep bs])
              <$> pTerm' 9 f
              <*> mapM (pTerm' 10) es
  t@TLam{} -> paren 0 $ withNames' n b $ \ xs -> bindNames xs $
    (\b -> sep [ text ("λ " ++ unwords xs ++ " →")
               , nest 2 b ]) <$> pTerm' 0 b
    where
      (n, b) = tLamView t
  t@TLet{} -> paren 0 $ withNames (length es) $ \ xs ->
    (\ (binds, b) -> sep [ "let" <+> vcat [ sep [ text x <+> "="
                                                , nest 2 e ] | (x, e) <- binds ]
                              <+> "in", b ])
      <$> pLets (zip xs es) b
    where
      (es, b) = tLetView t

      pLets [] b = ([],) <$> pTerm' 0 b
      pLets ((x, e) : bs) b = do
        e <- pTerm' 0 e
        first ((x, e) :) <$> bindName x (pLets bs b)

  TCase x _ def alts -> paren 0 $
    (\ sc alts defd ->
      sep [ "case" <+> sc <+> "of"
          , nest 2 $ vcat (alts ++ [ "_ →" <+> defd | null alts || def /= TError TUnreachable ]) ]
    ) <$> pTerm' 0 (TVar x)
      <*> mapM pAlt alts
      <*> pTerm' 0 def
    where
      pAlt (TALit l b) = pAlt' <$> pTerm' 0 (TLit l) <*> pTerm' 0 b
      pAlt (TAGuard g b) =
        pAlt' <$> (("_" <+> "|" <+>) <$> pTerm' 0 g)
              <*> (pTerm' 0 b)
      pAlt (TACon c a b) =
        withNames' a b $ \ xs -> bindNames xs $
        pAlt' <$> pTerm' 0 (TApp (TCon c) [TVar i | i <- reverse [0..a - 1]])
              <*> pTerm' 0 b
      pAlt' p b = sep [p <+> "→", nest 2 b]

  TUnit -> pure "()"
  TSort -> pure "Set"
  TErased -> pure "_"
  TError err -> paren 9 $ pure $ "error" <+> text (show (show err))
  TCoerce t -> paren 9 $ ("coe" <+>) <$> pTerm' 10 t

-- DeBruijn, Subst, and HasFree instances
---------------------------------------------------------------------------

instance DeBruijn TTerm where
  deBruijnVar = TVar
  deBruijnView (TVar i) = Just i
  deBruijnView _ = Nothing

instance Subst TTerm where
  type SubstArg TTerm = TTerm

  applySubst IdS = id
  applySubst rho = \case
      t@TDef{}    -> t
      t@TLit{}    -> t
      t@TCon{}    -> t
      t@TPrim{}   -> t
      t@TUnit{}   -> t
      t@TSort{}   -> t
      t@TErased{} -> t
      t@TError{}  -> t
      TVar i         -> lookupS rho i
      TApp f ts      -> tApp (applySubst rho f) (applySubst rho ts)
      TLam b         -> TLam (applySubst (liftS 1 rho) b)
      TLet e b       -> TLet (applySubst rho e) (applySubst (liftS 1 rho) b)
      TCase i t d bs ->
        case applySubst rho (TVar i) of
          TVar j  -> TCase j t (applySubst rho d) (applySubst rho bs)
          e       -> TLet e $ TCase 0 t (applySubst rho' d) (applySubst rho' bs)
            where rho' = wkS 1 rho
      TCoerce e -> TCoerce (applySubst rho e)
    where
      tApp (TPrim PSeq) [TErased, b] = b
      tApp f ts = TApp f ts

instance Subst TAlt where
  type SubstArg TAlt = TTerm
  applySubst rho (TACon c i b) = TACon c i (applySubst (liftS i rho) b)
  applySubst rho (TALit l b)   = TALit l (applySubst rho b)
  applySubst rho (TAGuard g b) = TAGuard (applySubst rho g) (applySubst rho b)

newtype UnderLambda = UnderLambda Any
  deriving (Eq, Ord, Show, Semigroup, Monoid)

newtype SeqArg = SeqArg All
  deriving (Eq, Ord, Show, Semigroup, Monoid)

data Occurs = Occurs Int UnderLambda SeqArg
  deriving (Eq, Ord, Show)

once :: Occurs
once = Occurs 1 mempty (SeqArg $ All False)

inSeq :: Occurs -> Occurs
inSeq (Occurs n l _) = Occurs n l mempty

underLambda :: Occurs -> Occurs
underLambda o = o <> Occurs 0 (UnderLambda $ Any True) mempty

instance Semigroup Occurs where
  Occurs a k s <> Occurs b l t = Occurs (a + b) (k <> l) (s <> t)

instance Monoid Occurs where
  mempty  = Occurs 0 mempty mempty
  mappend = (<>)


-- Andreas, 2019-07-10: this free variable computation should be rewritten
-- in the style of TypeChecking.Free.Lazy.
-- https://github.com/agda/agda/commit/03eb3945114a4ccdb449f22d69db8d6eaa4699b8#commitcomment-34249120

class HasFree a where
  freeVars :: a -> Map Int Occurs

freeIn :: HasFree a => Int -> a -> Bool
freeIn i x = Map.member i (freeVars x)

occursIn :: HasFree a => Int -> a -> Occurs
occursIn i x = fromMaybe mempty $ Map.lookup i (freeVars x)

instance HasFree Int where
  freeVars x = Map.singleton x once

instance HasFree a => HasFree [a] where
  freeVars xs = Map.unionsWith mappend $ map freeVars xs

instance (HasFree a, HasFree b) => HasFree (a, b) where
  freeVars (x, y) = Map.unionWith mappend (freeVars x) (freeVars y)

data Binder a = Binder Int a

instance HasFree a => HasFree (Binder a) where
  freeVars (Binder 0 x) = freeVars x
  freeVars (Binder k x) = Map.filterWithKey (\ k _ -> k >= 0) $ Map.mapKeysMonotonic (subtract k) $ freeVars x

newtype InSeq a = InSeq a

instance HasFree a => HasFree (InSeq a) where
  freeVars (InSeq x) = inSeq <$> freeVars x

instance HasFree TTerm where
  freeVars = \case
    TDef{}    -> Map.empty
    TLit{}    -> Map.empty
    TCon{}    -> Map.empty
    TPrim{}   -> Map.empty
    TUnit{}   -> Map.empty
    TSort{}   -> Map.empty
    TErased{} -> Map.empty
    TError{}  -> Map.empty
    TVar i         -> freeVars i
    TApp (TPrim PSeq) [TVar x, b] -> freeVars (InSeq x, b)
    TApp f ts      -> freeVars (f, ts)
    TLam b         -> underLambda <$> freeVars (Binder 1 b)
    TLet e b       -> freeVars (e, Binder 1 b)
    TCase i _ d bs -> freeVars (i, (d, bs))
    TCoerce t      -> freeVars t

instance HasFree TAlt where
  freeVars = \case
    TACon _ i b -> freeVars (Binder i b)
    TALit _ b   -> freeVars b
    TAGuard g b -> freeVars (g, b)

-- | Strenghtening.
tryStrengthen :: (HasFree a, Subst a) => Int -> a -> Maybe a
tryStrengthen n t =
  case Map.minViewWithKey (freeVars t) of
    Just ((i, _), _) | i < n -> Nothing
    _ -> Just $ applySubst (strengthenS impossible n) t


-- NFData instances
---------------------------------------------------------------------------

instance NFData Compiled
instance NFData ArgUsage
instance NFData TTerm
instance NFData TPrim
instance NFData CaseType
instance NFData CaseInfo
instance NFData TAlt
instance NFData TError
