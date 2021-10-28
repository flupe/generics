{-# OPTIONS --safe #-}

open import Generics.Prelude
open import Generics.Telescope
open import Generics.Desc
open import Generics.Mu

module Generics.Desc.Fold
  {P I n} {D : DataDesc P I n}
  {c} (X : ⟦ P , I ⟧xtel → Set c)
  (alg : ∀ {pi} → ⟦ D ⟧Data X pi → X pi) where

private
  variable
    p : ⟦ P ⟧tel tt
    V : ExTele P
    i : ⟦ I ⟧tel p
    v : ⟦ V ⟧tel p

fold : μ D (p , i) → X (p , i)

foldIndArg : (C : ConDesc P V I)
             (x : ⟦ C ⟧IndArgω (μ D) (p , v))
           → ⟦ C ⟧IndArg X (p , v)
foldIndArg (var _) x = fold x
foldIndArg (π ia _ C) x = fun< ia > λ s → foldIndArg C (x s)
foldIndArg (A ⊗ B) (xa , xb) = foldIndArg A xa , foldIndArg B xb

foldCon : (C : ConDesc P V I)
          (x : ⟦ C ⟧Conω (μ D) (p , v , i))
        → ⟦ C ⟧Con X (p , v , i)
foldCon (var _) (liftω refl) = refl
foldCon (π _ _ C) (s , x) = (s , foldCon C x)
foldCon (A ⊗ B) (xa , xb) = foldIndArg A xa , foldCon B xb

fold ⟨ k , x ⟩ = alg (k , foldCon (lookupCon D k) x)
