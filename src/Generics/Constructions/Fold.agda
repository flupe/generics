{-# OPTIONS --safe #-}

open import Generics.Prelude hiding (lookup; pi; curry)
open import Generics.Telescope
open import Generics.Desc
open import Generics.All
open import Generics.HasDesc
import Generics.Helpers as Helpers


module Generics.Constructions.Fold
  {P I ℓ} {A : Indexed P I ℓ} (H : HasDesc {P} {I} {ℓ} A)
  {p c} {X : Pred′ I λ i → Set c}
  where

open HasDesc H

private
  variable
    V : ExTele P
    i : ⟦ I ⟧tel p
    v : ⟦ V ⟧tel p

X′ : ⟦ I ⟧tel p → Set c
X′ i = unpred′ I _ X i


------------------------
-- Types of the algebra

levelAlg : ConDesc P V I → Level
levelAlg (var _) = c
levelAlg (π {ℓ} _ _ C) = ℓ ⊔ levelAlg C
levelAlg (A ⊗ B) = levelAlg A ⊔ levelAlg B

AlgIndArg : (C : ConDesc P V I) → ⟦ V ⟧tel p → Set (levelAlg C)
AlgIndArg (var f) v = X′ (f (p , v))
AlgIndArg (π ia S C) v = Π< ia > (S (p , v)) λ s → AlgIndArg C (v , s)
AlgIndArg (A ⊗ B) v = AlgIndArg A v × AlgIndArg B v

AlgCon : (C : ConDesc P V I) → ⟦ V ⟧tel p → Set (levelAlg C)
AlgCon (var f) v = X′ (f (p , v))
AlgCon (π ia S C) v = Π< ia > (S (p , v)) λ s → AlgCon C (v , s)
AlgCon (A ⊗ B) v = AlgIndArg A v → AlgCon B v

Algebra : ∀ k → Set (levelAlg (lookupCon D k))
Algebra k = AlgCon (lookupCon D k) tt

----------------
-- Generic fold

module _ (algs : Els Algebra) where

  fold-wf : (x : A′ (p , i)) → Acc x → X′ i

  foldData-wf : (x : ⟦ D ⟧Data A′ (p , i)) → AllDataω Acc D x → X′ i
  foldData-wf {i} (k , x) = foldCon (lookupCon D k) (algs k) x
    where
      foldIndArg : (C : ConDesc P V I)
                   (x : ⟦ C ⟧IndArg A′ (p , v))
                 → AllIndArgω Acc C x
                 → AlgIndArg C v
      foldIndArg (var f) x a = fold-wf x a
      foldIndArg (π ia S C) x a = fun< ia > λ s → foldIndArg C (app< ia > x s) (a s)
      foldIndArg (A ⊗ B) (xa , xb) (aa , ab)
        = foldIndArg A xa aa
        , foldIndArg B xb ab

      foldCon : (C   : ConDesc P V I)
                (alg : AlgCon C v)
                (x   : ⟦ C ⟧Con A′ (p , v , i))
              → AllConω Acc C x
              → X′ i
      foldCon (var _) alg refl _ = alg
      foldCon (π ia S C) alg (s , x) a = foldCon C (app< ia > alg s) x a
      foldCon (A ⊗ B) alg (xa , xb) (aa , ab)
        = foldCon B (alg (foldIndArg A xa aa)) xb ab

  fold-wf x (acc a) = foldData-wf (split x) a

  fold : A′ (p , i) → X′ i
  fold x = fold-wf x (wf x)

deriveFold : Arrows Algebra (Pred′ I λ i → A′ (p , i) → X′ i)
deriveFold = curryₙ λ m → pred′ I _ λ i → fold m
