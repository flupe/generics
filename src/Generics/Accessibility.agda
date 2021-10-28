{-# OPTIONS --safe --without-K #-}
open import Generics.Prelude
open import Generics.Telescope
open import Generics.Desc
open import Generics.All

module Generics.Accessibility
  {P I ℓ} (A : Indexed P I ℓ)
  {n} (D : DataDesc P I n)
  (let A′ = uncurry P I A)
  (split : ∀ {pi} → A′ pi → ⟦ D ⟧Data A′ pi)
  {p} where

  -- | Accessibility predicate for datatype A at value x
  data Acc {i} (x : A′ (p , i)) : Setω where
    acc : AllDataω Acc D (split x) → Acc x
