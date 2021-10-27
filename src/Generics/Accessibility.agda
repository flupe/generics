{-# OPTIONS --safe #-}
open import Generics.Prelude
open import Generics.Telescope
open import Generics.Desc
open import Generics.All

module Generics.Accessibility
  {P} {I : ExTele P} {ℓ} (A : Indexed P I ℓ)
  {n} (D : DataDesc P I ℓ n)
  (let A′ = uncurry P I A)
  (split   : ∀ {pi} → A′ pi → ⟦ D ⟧Data ℓ A′ pi)
  {p} where

  -- | Accessibility predicate for datatype A at value x
  data Acc {i} (x : A′ (p , i)) : Set ℓ where
    acc : AllData D A′ Acc (split x) → Acc x

  to-IndArg : ∀ {V} {C : ConDesc P V I ℓ} {v}
           (x : ⟦ C ⟧IndArg ℓ A′ (p , v))
           (a : AllIndArg C A′ Acc x)
         → ⟦ C ⟧IndArg (levelOfTel I) (μ D) (p , v)

  to-IndArgᵇ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ai {v}
          → (S : ⟦ P , V ⟧xtel → Set ℓ₂)
          → (C : ConDesc P (V ⊢< ai > S) I ℓ)
          → (x : IndArgᵇ ℓ e ai A′ S C (p , v))
          → AllIndArgᵇ e ai A′ S C Acc x
          → IndArgᵇ (levelOfTel I) e ai (μ D) S C (p , v)

  to-Con : ∀ {i} {V} {C : ConDesc P V I ℓ} {v}
           (x : ⟦ C ⟧Con ℓ A′ (p , v , i))
           (a : AllCon C A′ Acc x)
         → ⟦ C ⟧Con (levelOfTel I) (μ D) (p , v , i)

  to-Conᵇ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ai {v}
          → (S : ⟦ P , V ⟧xtel → Set ℓ₂)
          → (C : ConDesc P (V ⊢< ai > S) I ℓ)
          → (x : Conᵇ ℓ e ai A′ S C (p , v))
          → AllConᵇ e ai A′ S C Acc x
          → Conᵇ (levelOfTel I) e ai (μ D) S C (p , v)

  to-wf : ∀ {i} (x : A′ (p , i)) → Acc x → μ D (p , i)

  to-IndArg {C = var f} x (lift a) = to-wf x a
  to-IndArg {C = π p ia S C} x a = to-IndArgᵇ p ia S C x a
  to-IndArg {C = A ⊗ B} (xa , xb) (aa , ab) = to-IndArg {C = A} xa aa , to-IndArg {C = B} xb ab

  to-IndArgᵇ refl _ S C X a s = to-IndArg {C = C} (X s) (a s)

  to-Conᵇ refl _ S C (s , x) a = s , to-Con {C = C} x a

  to-Con {C = var f} (lift refl) a = lift refl
  to-Con {C = π e ia S C} x a = to-Conᵇ e ia S C x a
  to-Con {C = A ⊗ B} (xa , xb) (aa , ab) = to-IndArg {C = A} xa aa , (to-Con {C = B} xb ab)

  to-wf x (acc a) with split x
  ... | (k , x′) = ⟨ k , to-Con {C = lookupCon D k} x′ a ⟩
