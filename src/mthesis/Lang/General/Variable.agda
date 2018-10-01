{-# OPTIONS --without-K #-}

module mthesis.Lang.General.Variable where

open import HoTT

-- | A simple variable type, consisting of free and bound variable.
data Variable : Type0 where
  FreeVar : ℕ → Variable
  BoundVar : ℕ → Variable


-- | Prop which is inhabited if given variable is free.
isFree : Variable → Type0
isFree v = Σ ℕ (\n → v == FreeVar n)

-- | Prop which is inhabited if given variable is bound.
isBound : Variable → Type0
isBound v = Σ ℕ (\n → v == BoundVar n)

-- | Returns the name of the variable.
nameOf : Variable → ℕ
nameOf (FreeVar n) = n
nameOf (BoundVar n) = n
