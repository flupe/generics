{-# OPTIONS --safe #-}

open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc
open import Generics.HasDesc


module Generics.Constructions.Induction
       {P} {I : ExTele P} {ℓ n} {D : DataDesc P I ℓ n}
       {c} (Pr : ∀ {pi} → μ D pi → Set c) where

  module _ (f : ∀ {pi} (x : μ D pi) → All D Pr x → Pr x) where

    mutual
      all⟦⟧ : {V : ExTele P} (C : ConDesc P V I ℓ)
            → ∀ {pv} (x : ⟦ C ⟧Con (levelOfTel I) (μ D) pv) → All⟦⟧ C (μ D) Pr x
      all⟦⟧ (var i) x = lift (f x (all x))
      all⟦⟧ (A ⊗ B) (⟦A⟧ , ⟦B⟧) = all⟦⟧ A ⟦A⟧ , all⟦⟧ B ⟦B⟧
      all⟦⟧ (π e i S C) x      = all⟦⟧ᵇ e i S C x

      all⟦⟧ᵇ : ∀ {V : ExTele P} {ℓ₁ ℓ₂}
               (e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ)
               (ia : ArgInfo)
               (S  : ⟦ P , V ⟧xtel → Set ℓ₂)
               (C  : ConDesc P (V ⊢< ia > S) I ℓ)
             → ∀ {pv} (x : ⟦⟧ᵇ _ e ia (μ D) S C pv) →  All⟦⟧ᵇ e ia (μ D) S C Pr x
      all⟦⟧ᵇ refl i S C x s = all⟦⟧ C (x s)


      allExtend : {V : ExTele P} (C : ConDesc P V I ℓ)
                → ∀ {pvi} (x : Extend C (levelOfTel I) (μ D) pvi) → AllExtend C (μ D) Pr x
      allExtend (var i) x = lift tt
      allExtend (A ⊗ B) (⟦A⟧ , EB) = all⟦⟧ A ⟦A⟧ , allExtend B EB
      allExtend (π e i S C) x = allExtendᵇ e i S C x


      allExtendᵇ : ∀ {V : ExTele P} {ℓ₁ ℓ₂}
                   (e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ)
                   (ia : ArgInfo)
                   (S  : ⟦ P , V ⟧xtel → Set ℓ₂)
                   (C  : ConDesc P (V ⊢< ia > S) I ℓ)
                 → ∀ {pvi} (x : Extendᵇ _ e ia (μ D) S C pvi) → AllExtendᵇ e ia (μ D) S C Pr x
      allExtendᵇ refl i S C (s , EC) = allExtend C EC


      all : ∀ {pi} (x : μ D pi) → All D Pr x
      all ⟨ k , x ⟩ = allExtend (lookupCon D k) x

      ind : ∀ {pi} (x : μ D pi) → Pr x
      ind x = f x (all x)
