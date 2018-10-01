{-# OPTIONS --without-K --rewriting #-}
module playground.identity where

open import HoTT
open import common.identity

{-
-------------------------------
Einfache Übungen zum Aufwärmen
-------------------------------
-}
{-
Transitivität (a == b) → (b == c) → (a == c)

Via elimination (induction) on identity.
-}

CTy : ∀ { i } { A : Type i } → (c a b : A) → (a == b) → Type i
CTy c a b p = (b == c) → (a == c)

crefl : ∀ { i } { A : Type i } → (c x : A) → CTy c x x idp
crefl c x = λ p → p

trans : ∀ { i } { A : Type i } → {a b c : A } → (a == b) → (b == c) → (a == c)
trans {_} {_} {a} {b} {c} = elim= (CTy c) (λ x → crefl c x) a b

{- Beweis von Lemma 2.3.2:

 lift(u,p) : (x, u) == (y, transport P p)

mit

 ap pr₁ (lift u p) == p

-}

-- zunächst mal Existenz von lift:
CLift : ∀ {i j} {A : Type i} (P : A → Type j) (x y : A) (p : x == y) → Type (lmax i j)
CLift P x y p = (u : P x) → (x , u) == (y , transport P p u)

{-------------------------------
postulates to try stuff.
-------------------------------}
postulate
   i j : ULevel
   A0 : Type i
   x0 : A0
   P0 : A0 → Type j


clift0 : ∀ {i j} {A : Type i} (P : A → Type j) (x : A) → CLift P x x idp
clift0 P x = λ u → idp

liftFunc : ∀ {i j} {A : Type i} {x y : A} → (P : A → Type j) → (p : x == y) (u : P x) → (x , u) == (y , transport P p u)
liftFunc {_} {_} {_} {x} {y} P p =
   elim= (CLift P) (clift0 P) x y p

-- so far, so good. a 'liftFunc' does exist.
-- now, to the lifting property of 'transport':
--
-- ap pr₁ (liftFunc p u) == p
--
-- by induction on p, we can assume p = refl (idp), hence:
liftingProperty : ∀ {i j} {A : Type i} {x y : A} (P : A → Type j) (p : x == y) (u : P x) → ap fst (liftFunc P p u) == p
liftingProperty P idp u = idp
