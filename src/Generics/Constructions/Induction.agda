{-# OPTIONS --safe #-}

open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc
open import Generics.HasDesc


module Generics.Constructions.Induction
       {P} {I : ExTele P} {ℓ n} {D : DataDesc P I ℓ n} {p}
       {c} (Pr : ∀ {i} → μ D (p , i) → Set c) where

  module _ (f : ∀ {i} (x : μ D (p , i)) → All D Pr x → Pr x) where

    mutual
      allIndArg : ∀ {V} (C : ConDesc P V I ℓ) {v}
                  (x : ⟦ C ⟧IndArg (levelOfTel I) (μ D) (p , v))
                → AllIndArg C (μ D) Pr x
      allIndArg (var i) x = lift (f x (all x))
      allIndArg (A ⊗ B) (⟦A⟧ , ⟦B⟧) = allIndArg A ⟦A⟧ , allIndArg B ⟦B⟧
      allIndArg (π e i S C) x      = allIndArgᵇ e i S C x

      allIndArgᵇ : ∀ {V} {ℓ₁ ℓ₂} (e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ) (ia : ArgInfo)
                   (S  : ⟦ P , V ⟧xtel → Set ℓ₂)
                   (C  : ConDesc P (V ⊢< ia > S) I ℓ)
                   {v} (x : IndArgᵇ _ e ia (μ D) S C (p , v))
                 → AllIndArgᵇ e ia (μ D) S C Pr x
      allIndArgᵇ refl i S C x s = allIndArg C (x s)


      allCon : ∀ {V} (C : ConDesc P V I ℓ) {v i}
               (x : ⟦_⟧Con C (levelOfTel I) (μ D) (p , v , i))
             → AllCon C (μ D) Pr x
      allCon (var i) x = lift tt
      allCon (A ⊗ B) (⟦A⟧ , EB) = allIndArg A ⟦A⟧ , allCon B EB
      allCon (π e i S C) x = allConᵇ e i S C x


      allConᵇ : ∀ {V} {ℓ₁ ℓ₂} (e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ) (ia : ArgInfo)
                (S  : ⟦ P , V ⟧xtel → Set ℓ₂)
                (C  : ConDesc P (V ⊢< ia > S) I ℓ)
                {v i} (x : Conᵇ _ e ia (μ D) S C (p , v , i))
              → AllConᵇ e ia (μ D) S C Pr x
      allConᵇ refl i S C (s , EC) = allCon C EC


      all : ∀ {i} (x : μ D (p , i)) → All D Pr x
      all ⟨ k , x ⟩ = allCon (lookupCon D k) x

      ind : ∀ {i} (x : μ D (p , i)) → Pr x
      ind x = f x (all x)
