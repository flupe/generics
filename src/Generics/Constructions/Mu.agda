{-# OPTIONS --safe #-}

open import Generics.Prelude
open import Generics.Telescope
open import Generics.Desc
open import Generics.HasDesc
open import Generics.All

module Generics.Constructions.Mu
  {P I ℓ} (A : Indexed P I ℓ) (H : HasDesc A)
  (open HasDesc H)
  {p} where

private
  variable
    V : ExTele P
    i : ⟦ I ⟧tel p
    v : ⟦ V ⟧tel p

open import Generics.Mu public

toData : (x : ⟦ D ⟧Data A′ (p , i)) → AllDataω Acc D x → μ D (p , i)

to-wf : (x : A′ (p , i)) → Acc x → μ D (p , i)
to-wf x (acc a) = toData (split x) a

toData (k , x) a = ⟨ k , toCon (lookupCon D k) x a ⟩
  where
    toIndArg : (C : ConDesc P V I)
               (x : ⟦ C ⟧IndArg A′ (p , v))
             → AllIndArgω Acc C x
             → ⟦ C ⟧IndArgω (μ D) (p , v)
    toIndArg (var _) x a = to-wf x a
    toIndArg (π ai _ C) x a s = toIndArg C (app< ai > x s) (a s)
    toIndArg (A ⊗ B) (xa , xb) (aa , ab)
      = toIndArg A xa aa , toIndArg B xb ab

    toCon : (C : ConDesc P V I)
            (x : ⟦ C ⟧Con A′ (p , v , i))
          → AllConω Acc C x
          → ⟦ C ⟧Conω (μ D) (p , v , i)
    toCon (var _) refl _ = liftω refl
    toCon (π _ _ C) (s , x) a = s , toCon C x a
    toCon (A ⊗ B) (xa , xb) (aa , ab)
      = toIndArg A xa aa , toCon B xb ab

to : A′ (p , i) → μ D (p , i)
to x = to-wf x (wf x)


from : μ D (p , i) → A′ (p , i)

fromIndArg : (C : ConDesc P V I)
           → ⟦ C ⟧IndArgω (μ D) (p , v)
           → ⟦ C ⟧IndArg A′ (p , v)
fromIndArg (var _) x = from x
fromIndArg (π ai S C) x = fun< ai > λ s → fromIndArg C (x s)
fromIndArg (A ⊗ B) (xa , xb) = fromIndArg A xa , fromIndArg B xb

fromCon : (C : ConDesc P V I)
        → ⟦ C ⟧Conω (μ D) (p , v , i)
        → ⟦ C ⟧Con A′ (p , v , i)
fromCon (var _) (liftω refl) = refl
fromCon (π _ S C) (s , x) = s , fromCon C x
fromCon (A ⊗ B) (xa , xb) = fromIndArg A xa , fromCon B xb

from ⟨ k , x ⟩ = constr (k , fromCon (lookupCon D k) x)
