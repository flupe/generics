open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc
open import Generics.HasDesc

module Generics.Constructions.Induction
       {P} {I : ExTele P} {ℓ n} {D : Desc P I ℓ n}
       {c} (Pr : ∀ {pi} → μ D pi → Set c) where

  module _ (f : ∀ {pi} (x : μ D pi) → All D Pr x → Pr x) where

    mutual 
      all⟦⟧ : {V : ExTele P} (C : CDesc P V I ℓ)
            → ∀ {pv} (x : C⟦ C ⟧ (levelTel I) (μ D) pv) → All⟦⟧ C (μ D) Pr x
      all⟦⟧ (var i) x = lift (f x (all x))
      all⟦⟧ (A ⊗ B) (⟦A⟧ , ⟦B⟧) = all⟦⟧ A ⟦A⟧ , all⟦⟧ B ⟦B⟧
      all⟦⟧ (π e i S C) x      = all⟦⟧b e i S C x

      all⟦⟧b : ∀ {V : ExTele P} {ℓ₁ ℓ₂}
               (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ)
               (i : ArgInfo)
               (S : Σ[ P ⇒ V ] → Set ℓ₂)
               (C : CDesc P (V ⊢< relevance i > S) I ℓ)
             → ∀ {pv} (x : C⟦⟧b _ e i (μ D) S C pv) →  All⟦⟧b e i (μ D) S C Pr x
      all⟦⟧b refl i S C x s = all⟦⟧ C (x s)


      allExtend : {V : ExTele P} (C : CDesc P V I ℓ)
                → ∀ {pvi} (x : Extend C (levelTel I) (μ D) pvi) → AllExtend C (μ D) Pr x
      allExtend (var i) x = lift tt
      allExtend (A ⊗ B) (⟦A⟧ , EB) = all⟦⟧ A ⟦A⟧ , allExtend B EB
      allExtend (π e i S C) x = allExtendb e i S C x


      allExtendb : ∀ {V : ExTele P} {ℓ₁ ℓ₂}
                   (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ)
                   (i : ArgInfo)
                   (S : Σ[ P ⇒ V ] → Set ℓ₂)
                   (C : CDesc P (V ⊢< relevance i > S) I ℓ)
                 → ∀ {pvi} (x : Extendb _ e i (μ D) S C pvi) → AllExtendb e i (μ D) S C Pr x
      allExtendb refl i S C (s , EC) = allExtend C EC


      all : ∀ {pi} (x : μ D pi) → All D Pr x
      all ⟨ k , x ⟩ = allExtend (lookup D k) x

      ind : ∀ {pi} (x : μ D pi) → Pr x
      ind x = f x (all x)
