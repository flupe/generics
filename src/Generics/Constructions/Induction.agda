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
      all⟦⟧ : {V : ExTele P} (C : ConDesc P V I ℓ)
            → ∀ {v} (x : ⟦ C ⟧Con (levelOfTel I) (μ D) (p , v)) → All⟦⟧ C (μ D) Pr x
      all⟦⟧ (var i) x = lift (f x (all x))
      all⟦⟧ (A ⊗ B) (⟦A⟧ , ⟦B⟧) = all⟦⟧ A ⟦A⟧ , all⟦⟧ B ⟦B⟧
      all⟦⟧ (π e i S C) x      = all⟦⟧ᵇ e i S C x

      all⟦⟧ᵇ : ∀ {V : ExTele P} {ℓ₁ ℓ₂}
               (e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ)
               (ia : ArgInfo)
               (S  : ⟦ P , V ⟧xtel → Set ℓ₂)
               (C  : ConDesc P (V ⊢< ia > S) I ℓ)
             → ∀ {v} (x : ⟦⟧ᵇ _ e ia (μ D) S C (p , v)) →  All⟦⟧ᵇ e ia (μ D) S C Pr x
      all⟦⟧ᵇ refl i S C x s = all⟦⟧ C (x s)


      allExtend : {V : ExTele P} (C : ConDesc P V I ℓ)
                → ∀ {v i} (x : Extend C (levelOfTel I) (μ D) (p , v , i)) → AllExtend C (μ D) Pr x
      allExtend (var i) x = lift tt
      allExtend (A ⊗ B) (⟦A⟧ , EB) = all⟦⟧ A ⟦A⟧ , allExtend B EB
      allExtend (π e i S C) x = allExtendᵇ e i S C x


      allExtendᵇ : ∀ {V : ExTele P} {ℓ₁ ℓ₂}
                   (e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ)
                   (ia : ArgInfo)
                   (S  : ⟦ P , V ⟧xtel → Set ℓ₂)
                   (C  : ConDesc P (V ⊢< ia > S) I ℓ)
                 → ∀ {v i} (x : Extendᵇ _ e ia (μ D) S C (p , v , i))
                 → AllExtendᵇ e ia (μ D) S C Pr x
      allExtendᵇ refl i S C (s , EC) = allExtend C EC


      all : ∀ {i} (x : μ D (p , i)) → All D Pr x
      all ⟨ k , x ⟩ = allExtend (lookupCon D k) x

      ind : ∀ {i} (x : μ D (p , i)) → Pr x
      ind x = f x (all x)
