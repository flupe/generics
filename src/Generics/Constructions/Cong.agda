{-# OPTIONS --safe #-}

open import Generics.Prelude hiding (lookup; pi; curry)
open import Generics.Telescope
open import Generics.Desc
open import Generics.All
open import Generics.HasDesc
import Generics.Helpers as Helpers

open import Relation.Binary.HeterogeneousEquality.Core using (_≅_; refl)

module Generics.Constructions.Cong
  {P I ℓ} {A : Indexed P I ℓ} (H : HasDesc {P} {I} {ℓ} A)
  {p}
  where

open HasDesc H

private
  variable
    V       : ExTele P
    i i₁ i₂ : ⟦ I ⟧tel p
    v v₁ v₂ : ⟦ V ⟧tel p


-----------------------
-- Type of congruences

levelCongCon : (C : ConDesc P V I) → Level
levelCongCon (var _) = ℓ
levelCongCon (π {ℓ} _ _ C) = ℓ ⊔ levelCongCon C
levelCongCon (A ⊗ B) = levelIndArg A ℓ ⊔ levelCongCon B

CongCon : (C   : ConDesc P V I)
          (mk₁ : ∀ {i₁} → ⟦ C ⟧Con A′ (p , v₁ , i₁) → ⟦ D ⟧Data A′ (p , i₁))
          (mk₂ : ∀ {i₂} → ⟦ C ⟧Con A′ (p , v₂ , i₂) → ⟦ D ⟧Data A′ (p , i₂))
        → Set (levelCongCon C)
-- If non-inductive arguments are equal
CongCon (π (n , ai) S C) mk₁ mk₂
  = {s₁ : < relevance ai > S _}
    {s₂ : < relevance ai > S _}
  → s₁ ≅ s₂
  → CongCon C (λ x → mk₁ (s₁ , x))
              (λ x → mk₂ (s₂ , x))
-- And inductive arguments  are equal
CongCon (A ⊗ B) mk₁ mk₂ 
  = {f₁ : ⟦ A ⟧IndArg A′ _}
    {f₂ : ⟦ A ⟧IndArg A′ _}
  → f₁ ≅ f₂
  → CongCon B (λ x → mk₁ (f₁ , x))
              (λ x → mk₂ (f₂ , x))
-- Then applying the constructor to both sets should lead
-- to equal values
CongCon (var f) mk₁ mk₂          
  = constr (mk₁ refl) ≅ constr (mk₂ refl) 

Cong : ∀ k → Set (levelCongCon (lookupCon D k))
Cong k = CongCon (lookupCon D k) (k ,_) (k ,_)


----------------------
-- Generic congruence

deriveCong : ∀ k → Cong k
deriveCong k = congCon (lookupCon D k)
  where
   congCon : (C : ConDesc P V I)
             {mk : ∀ {i} → ⟦ C ⟧Con A′ (p , v , i) → ⟦ D ⟧Data A′ (p , i)}
           → CongCon C mk mk
   congCon (var f) = refl
   congCon (π ai S C) refl = congCon C
   congCon (A ⊗ B) refl = congCon B
