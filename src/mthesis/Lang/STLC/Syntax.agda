{-# OPTIONS --without-K #-}


{- Module defining the syntax for the Simply Typed Lambda Calculus.
Syntax here contains terms and types. 
-}
module mthesis.Lang.STLC.Syntax where


-- Everything's based on HoTT.
open import HoTT

-- general syntax:
open import mthesis.Lang.General.Variable

data Term : Type0 where
 L : Term → Term
 -- ^ Abstraction using deBruijn.
 App : Term → Term → Term
 -- ^ Application of terms.
 V : Variable → Term
 -- ^ Simple Variable, which is either bound or free.

-- | Proposition which describes if a term is valid on a given
-- level of abstractions.
data isValidTermAtLevel : ℕ → Term → Type0 where
  fvarBase : { t : Term } → Σ ℕ (\n → (t == V (FreeVar n))) → ∀ {n} → isValidTermAtLevel n t
  bvarBase : { t : Term } → ∀ { n } → Σ ℕ (\m → (t == V (BoundVar m)) × (m < n)) → isValidTermAtLevel n t
  appStep : (t : Term) → (s : Term) → ∀ { n } → isValidTermAtLevel n t → isValidTermAtLevel n s → isValidTermAtLevel n (App t s)
  absStep : { t : Term } → ∀ { n } → isValidTermAtLevel (n + 1) t → isValidTermAtLevel n (L t)

-- | A valid term is valid beginning on a level of abstraction of 0.
isValidTerm : Term → Type0
isValidTerm t = isValidTermAtLevel 0 t


-- | A type for the simple type syntax: universal quantified type variables
-- or function types.
data LType : Type0 where
  TyV : Variable → LType
  -- ^ Type variable. Be aware: every variable is universal bound.
  -- This especially means: It makes no difference if this is either free or bound.
  TyFunc : LType → LType → LType
  -- ^ Type of functions, `a → b`.
