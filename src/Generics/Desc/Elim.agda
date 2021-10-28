{-# OPTIONS --safe #-}

open import Generics.Prelude
open import Generics.Telescope
open import Generics.Desc
open import Generics.All

module Generics.Desc.Elim
  {P I ℓ n} {D : DataDesc P I ℓ n}
  {p c} (Pr : ∀ {i} → μ D (p , i) → Set c)
  (f : ∀ {i} (x : μ D (p , i)) → All D Pr x → Pr x) where

private
  variable
    V : ExTele P
    i : ⟦ I ⟧tel p
    v : ⟦ V ⟧tel p

all : (x : μ D (p , i)) → All D Pr x

allIndArg : (C : ConDesc P V I ℓ)
            (x : ⟦ C ⟧IndArg (levelOfTel I) (μ D) (p , v))
          → AllIndArg C (μ D) Pr x
allIndArgᵇ : ∀ {ℓ₁ ℓ₂} (e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia
             (S : ⟦ P , V ⟧xtel → Set ℓ₂)
             (C : ConDesc P (V ⊢< ia > S) I ℓ)
             (x : IndArgᵇ _ e ia (μ D) S C (p , v))
           → AllIndArgᵇ e ia (μ D) S C Pr x
allIndArg (var i) x = lift (f x (all x))
allIndArg (A ⊗ B) (⟦A⟧ , ⟦B⟧) = allIndArg A ⟦A⟧ , allIndArg B ⟦B⟧
allIndArg (π e i S C) x      = allIndArgᵇ e i S C x
allIndArgᵇ refl i S C x s = allIndArg C (x s)

allCon : (C : ConDesc P V I ℓ)
         (x : ⟦_⟧Con C (levelOfTel I) (μ D) (p , v , i))
       → AllCon C (μ D) Pr x
allConᵇ : ∀ {ℓ₁ ℓ₂} (e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia
          (S : ⟦ P , V ⟧xtel → Set ℓ₂)
          (C : ConDesc P (V ⊢< ia > S) I ℓ)
          (x : Conᵇ _ e ia (μ D) S C (p , v , i))
        → AllConᵇ e ia (μ D) S C Pr x
allCon (var i) x = lift tt
allCon (A ⊗ B) (⟦A⟧ , EB) = allIndArg A ⟦A⟧ , allCon B EB
allCon (π e i S C) x = allConᵇ e i S C x
allConᵇ refl i S C (s , EC) = allCon C EC

all ⟨ k , x ⟩ = allCon (lookupCon D k) x

elim : (x : μ D (p , i)) → Pr x
elim x = f x (all x)
