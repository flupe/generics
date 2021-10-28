{-# OPTIONS --safe #-}

open import Generics.Prelude
open import Generics.Telescope
open import Generics.Desc

module Generics.Desc.Fold
  {P I ℓ n} {D : DataDesc P I ℓ n}
  {c} (X : ⟦ P , I ⟧xtel → Set (ℓ ⊔ c))
  (alg : ∀ {pi} → ⟦ D ⟧Data c X pi → X pi) where

private
  variable
    p : ⟦ P ⟧tel tt
    V : ExTele P
    i : ⟦ I ⟧tel p
    v : ⟦ V ⟧tel p

fold : μ D (p , i) → X (p , i)

foldIndArg : (C : ConDesc P V I ℓ)
             (x : ⟦ C ⟧IndArg (levelOfTel I) (μ D) (p , v))
           → ⟦ C ⟧IndArg c X (p , v)
foldIndArgᵇ : ∀ {ℓ₁ ℓ₂} (e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia
              (S : ⟦ P , V ⟧xtel → Set ℓ₂)
              (C : ConDesc P (V ⊢< ia > S) I ℓ)
            → IndArgᵇ (levelOfTel I) e ia (μ D) S C (p , v)
            → IndArgᵇ c e ia X S C (p , v)
foldIndArg (var f) x = fold x
foldIndArg (π e ia S C) x = foldIndArgᵇ e ia S C x
foldIndArg (A ⊗ B) (xa , xb) = foldIndArg A xa , foldIndArg B xb
foldIndArgᵇ refl ia S C x s = foldIndArg C (x s)

foldCon : (C : ConDesc P V I ℓ)
          (x : ⟦ C ⟧Con (levelOfTel I) (μ D) (p , v , i))
        → ⟦ C ⟧Con c X (p , v , i)
foldConᵇ : ∀ {ℓ₁ ℓ₂} (e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia
           (S : ⟦ P , V ⟧xtel → Set ℓ₂)
           (C : ConDesc P (V ⊢< ia > S) I ℓ)
         → Conᵇ (levelOfTel I) e ia (μ D) S C (p , v , i)
         → Conᵇ c e ia X S C (p , v , i)
foldCon (var f) (lift refl) = lift refl
foldCon (π e ia S C) x = foldConᵇ e ia S C x
foldCon (A ⊗ B) (xa , xb) = foldIndArg A xa , foldCon B xb
foldConᵇ refl ia S C (s , x) = s , foldCon C x

fold ⟨ k , x ⟩ = alg (k , foldCon (lookupCon D k) x)
