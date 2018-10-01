{-# OPTIONS --without-K --rewriting #-}
module common.identity where

open import HoTT

{-------------------------------
 Some translations from book into
 agda, for the beginner.
-------------------------------}

-- As far as I can see, there is only based path induction 
-- named 'J'.
--
-- So, I need some elim= as (non-based) path induction.

elim= : ∀ {i j} {A : Type i} → (C : (x y : A)(p : x == y) → Type j) (c : (x : A) → (C x x idp)) → (x y : A) (p : (x == y)) → (C x y p)
elim= {i} {j} {A} C c x y p = J {i} {j} {A} {x} (C x) (c x) {y} p
