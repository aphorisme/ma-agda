{-# OPTIONS --without-K #-}
module playground.STLC where

open import HoTT
-- from mthesis:
open import mthesis.Lang.General.Variable
open import mthesis.Lang.STLC.Syntax

-- # A playground for the STLC definitions and propositions, etc.

-- ## Defining some terms.

-- the identity. Note: Index for bound var starts of 0.
-- this is the `λx.x` term.
identity : Term
identity = L (V (BoundVar 0))

-- proving, that this term is valid (i.e. no bound var without scope).
identity_valid : isValidTerm identity
identity_valid =
   absStep (bvarBase (0 , (idp , ltS)))


-- K combinator term: `λ x . λ y . x` 
k-comb : Term
k-comb = L $ L (V $ BoundVar 1)

k-comb_valid : isValidTerm k-comb
k-comb_valid =
  absStep (absStep
          (bvarBase (1 , (idp , ltS))))
          

-- ## Some invalid terms.

invalid01 : Term
invalid01 = L $ L (V $ BoundVar 2)

invalid01_invalid : (isValidTerm invalid01) → ⊥
invalid01_invalid (fvarBase {_} _ {_}) = ⊥-elim
invalid01_invalid (bvarBase x) = _
invalid01_invalid (absStep x) = _
