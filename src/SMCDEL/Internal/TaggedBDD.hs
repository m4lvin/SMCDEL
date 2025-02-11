module SMCDEL.Internal.TaggedBDD where

import Data.Tagged
import Data.HasCacBDD hiding (Top,Bot)

import SMCDEL.Language

-- * Tagged BDDs

-- | Operations on tagged BDDs.
-- The tag `a` is meant to be an empty type.
class TagForBDDs a where
  -- | How many copies of the vocabulary do we have?
  -- This is the number of markers + 1.
  multiplier :: Tagged a Bdd -> Int
  multiplier _ = 2
  -- | Move back, must be without markers!
  unmvBdd :: Tagged a Bdd -> Bdd
  unmvBdd = relabelFun (\n -> if even n then n `div` 2 else error ("Odd: " ++ show n)) . untag
  -- | Move into double vocabulary, but do not add marker
  mv :: Bdd -> Tagged a Bdd
  mv = cpMany 0
  -- | Move into extended vocabulary, add one marker
  cp :: Bdd -> Tagged a Bdd
  cp = cpMany 1
  -- | Move into extended vocabulary, add k many markers, MUST be available!
  cpMany :: Int -> Bdd -> Tagged a Bdd
  cpMany k b = let x = pure $ relabelFun (\n -> (multiplier x * n) + k) b
                in if k >= multiplier x then error "Not enough markers!" else x

  -- | Evaluate a tagged BDD.
  tagBddEval :: [Prp] -> Tagged a Bdd -> Bool
  tagBddEval truths querybdd = evaluateFun (untag querybdd) (\n -> P n `elem` truths)

-- * Pre-defined tags

-- | Tag for BDDs using the duplicated vocabulary \(V \cup V'\).
data Dubbel
instance TagForBDDs Dubbel where
  multiplier = const 2

-- | Tag for BDDs using the triple vocabulary \(V \cup V' \cup V''\).
data Tripel
instance TagForBDDs Tripel where
  multiplier = const 3

-- | Tag for BDDs using the quadruple vocabulary \(V \cup V' \cup V'' \cup V'''\).
data Quadrupel
instance TagForBDDs Quadrupel where
  multiplier = const 4

-- * Generic definition for tagged BDDs

-- | The total relation as a tagged BDD.
totalRelBdd :: Tagged a Bdd
totalRelBdd = pure top

-- | The empty relation as a tagged BDD.
emptyRelBdd :: Tagged a Bdd
emptyRelBdd = pure bot

-- | Given a vocabulary, make a tagged BDD to say
-- that each plain variable \(p\) and the corresponding
-- marked variable \(p'\) variable have the same value:
-- \( \wedge_p (p \leftrightarrow p') \).
-- This encodes the identity relation.
allsamebdd :: TagForBDDs a => [Prp] -> Tagged a Bdd
allsamebdd ps = conSet <$> sequence [ equ <$> mv (var x) <*> cp (var x) | (P x) <- ps ]
