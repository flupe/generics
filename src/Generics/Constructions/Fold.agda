{-# OPTIONS --safe #-}

open import Generics.Prelude hiding (lookup; pi; curry)
open import Generics.Telescope
open import Generics.Desc
open import Generics.All
open import Generics.HasDesc
import Generics.Helpers as Helpers


module Generics.Constructions.Fold
  {P I ℓ} {A : Indexed P I ℓ} (H : HasDesc {P} {I} {ℓ} A)
  {p c} {X : Pred′ I λ i → Set (ℓ ⊔ c)}
  where

open HasDesc H

private
  variable
    V : ExTele P
    i : ⟦ I ⟧tel p
    v : ⟦ V ⟧tel p

X′ : ⟦ I ⟧tel p → Set (ℓ ⊔ c)
X′ i = unpred′ I _ X i

------------------------
-- Types of the algebra

levelIndArg levelCon : ConDesc P V I ℓ → Level
levelIndArg (var _) = ℓ ⊔ c
levelIndArg (π {ℓ} _ _ _ C) = ℓ ⊔ levelIndArg C
levelIndArg (A ⊗ B) = levelIndArg A ⊔ levelIndArg B

levelCon (var _) = ℓ ⊔ c
levelCon (π {ℓ} _ _ _ C) = ℓ ⊔ levelCon C
levelCon (A ⊗ B) = levelIndArg A ⊔ levelCon B

AlgIndArg : (C : ConDesc P V I ℓ) → ⟦ V ⟧tel p → Set (levelIndArg C)
AlgIndArg (var f) v = X′ (f (p , v))
AlgIndArg (π _ ia S C) v = Π< ia > (S (p , v)) λ s → AlgIndArg C (v , s)
AlgIndArg (A ⊗ B) v = AlgIndArg A v × AlgIndArg B v

AlgCon : (C : ConDesc P V I ℓ) → ⟦ V ⟧tel p → Set (levelCon C)
AlgCon (var f) v = X′ (f (p , v))
AlgCon (π _ ia S C) v = Π< ia > (S (p , v)) λ s → AlgCon C (v , s)
AlgCon (A ⊗ B) v = AlgIndArg A v → AlgCon B v

Algebra : ∀ k → Set (levelCon (lookupCon D k))
Algebra k = AlgCon (lookupCon D k) tt

----------------
-- Generic fold

module _ (algs : Els Algebra) where

  fold-wf : (x : A′ (p , i)) → Acc x → X′ i

  foldData-wf
    : (x : ⟦ D ⟧Data ℓ A′ (p , i))
    → AllData D A′ Acc x
    → X′ i
  foldData-wf {i} (k , x) = foldCon (lookupCon D k) (algs k) x
    where
      foldIndArg : (C : ConDesc P V I ℓ)
                   (x : ⟦ C ⟧IndArg ℓ A′ (p , v))
                 → AllIndArg C A′ Acc x
                 → AlgIndArg C v
      foldIndArgᵇ
        : ∀ {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) {ia}
          {S : ⟦ P , V ⟧xtel → Set ℓ₂}
          (C : ConDesc P (V ⊢< ia > S) I ℓ)
          (x : IndArgᵇ ℓ e ia A′ S C (p , v))
        → AllIndArgᵇ e ia A′ S C Acc x
        → (s : < relevance ia > S (p , v))
        → AlgIndArg C (v , s)
      foldIndArg (var f) x (lift a) = fold-wf x a
      foldIndArg (π e ia S C) x a = fun< ia > (foldIndArgᵇ e C x a)
      foldIndArg (A ⊗ B) (xa , xb) (aa , ab)
        = foldIndArg A xa aa
        , foldIndArg B xb ab
      foldIndArgᵇ refl C x a s = foldIndArg C (x s) (a s)

      foldCon : (C   : ConDesc P V I ℓ)
                (alg : AlgCon C v)
                (x   : ⟦ C ⟧Con ℓ A′ (p , v , i))
              → AllCon C A′ Acc x
              → X′ i
      foldConᵇ
        : ∀ {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) {ia}
          {S   : ⟦ P , V ⟧xtel → Set ℓ₂}
          (C   : ConDesc P (V ⊢< ia > S) I ℓ)
          (alg : Π< ia > (S (p , v)) λ s → AlgCon C (v , s))
          (x   : Conᵇ ℓ e ia A′ S C (p , v , i))
        → AllConᵇ e ia A′ S C Acc x
        → X′ i
      foldCon (var _) alg (lift refl) _ = alg
      foldCon (π e ai₁ S C) alg x a = foldConᵇ e C alg x a
      foldCon (A ⊗ B) alg (xa , xb) (aa , ab)
        = foldCon B (alg (foldIndArg A xa aa)) xb ab
      foldConᵇ refl C alg (s , x) a = foldCon C (app< _ > alg s) x a

  fold-wf x (acc a) = foldData-wf (split x) a

  fold : A′ (p , i) → X′ i
  fold x = fold-wf x (wf x)

deriveFold : Arrows Algebra (Pred′ I λ i → A′ (p , i) → X′ i)
deriveFold = curryₙ λ m → pred′ I _ λ i → fold m
