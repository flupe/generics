module Generics.Constructions.DecEq where

open import Generics.Prelude hiding (lookup; _≟_)
open import Generics.Telescope
open import Generics.Desc
open import Generics.HasDesc
import Generics.Helpers as Helpers
import Data.Fin.Properties as Fin

open import Relation.Nullary.Decidable as Decidable
open import Data.Empty
open import Relation.Nullary
import Data.Product.Properties as Product
open import Relation.Binary using (DecidableEquality)
open import Relation.Nullary.Product


record DecEq {l} (A : Set l) : Set l where field _≟_ : DecidableEquality A

module _ {P} {I : ExTele P} {ℓ}
         {A : Indexed P I ℓ}
         (H : HasDesc {P} {I} {ℓ} A) where

  data HigherOrderArgumentsNotSupported : Set where

  -- Predicate preventing the use of Higher-order inductive arguments
  OnlyFO : ∀ {V} → ConDesc P V I ℓ → Setω
  OnlyFO (var _) = Liftω ⊤
  OnlyFO (π _ _ _ _) = Liftω HigherOrderArgumentsNotSupported
  OnlyFO (A ⊗ B) = OnlyFO A ×ω OnlyFO B

  open HasDesc H
  open Helpers P I ℓ DecEq (const ⊤) OnlyFO

  DecEqHelpers : ∀ p → Setω
  DecEqHelpers p = Helpers p D

  private irr≡ : ∀ {l} (A : Set l) (x y : Irr A) → x ≡ y
          irr≡ A (irrv _) (irrv _) = refl

  private module _ {p} (DH : DecEqHelpers p) where

    variable
      V : ExTele P
      v : ⟦ V ⟧tel p
      i : ⟦ I ⟧tel p

    ≡-dec-IndArd : ∀ (C : ConDesc P V I ℓ) → OnlyFO C
                 → DecidableEquality (⟦ C ⟧IndArg (levelOfTel I) (μ D) (p , v))

    ≡-dec-Con : ∀ (C : ConDesc P V I ℓ) → ConHelper p C
              → DecidableEquality (⟦ C ⟧Con (levelOfTel I) (μ D) (p , v , i))

    ≡-dec-μ : DecidableEquality (μ D (p , i))

    ≡-dec-Conᵇ-irr : ∀ {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) {vs q}
                     (S : ⟦ P , V ⟧xtel → Set ℓ₂)
                     (C : ConDesc P (V ⊢< ai vs irrelevant q > S) I ℓ)
                   → ConHelper p C
                   → DecidableEquality (Conᵇ (levelOfTel I) e _ (μ D) S C (p , v , i))

    ≡-dec-Conᵇ-rel : ∀ {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) {vs q}
                     (S : ⟦ P , V ⟧xtel → Set ℓ₂)
                     (C : ConDesc P (V ⊢< ai vs relevant q > S) I ℓ)
                   → DecEq (S (p , v)) → ConHelper p C
                   → DecidableEquality (Conᵇ (levelOfTel I) e _ (μ D) S C (p , v , i))

    ≡-dec-IndArd (var i) H x y = ≡-dec-μ x y
    ≡-dec-IndArd (A ⊗ B) (HA ,ω HB) x y = Product.≡-dec (≡-dec-IndArd A HA) (≡-dec-IndArd B HB) x y
                                        -- TODO: inline product
    ≡-dec-IndArd (π p i S C) ()

    ≡-dec-Conᵇ-irr refl S C HC (x₁ , x₂) (y₁ , y₂) with irr≡ _ x₁ y₁
    ≡-dec-Conᵇ-irr refl S C HC (x₁ , x₂) (y₁ , y₂) | refl with ≡-dec-Con C HC x₂ y₂
    ≡-dec-Conᵇ-irr refl S C HC (x₁ , x₂) (y₁ , y₂) | refl | yes refl = yes refl
    ≡-dec-Conᵇ-irr refl S C HC (x₁ , x₂) (y₁ , y₂) | refl | no  ¬p   = no (¬p ∘ (λ { refl → refl }))

    ≡-dec-Conᵇ-rel refl _ C HS HC (x₁ , x₂) (y₁ , y₂) with DecEq._≟_ HS x₁ y₁
    ≡-dec-Conᵇ-rel refl _ C HS HC (x₁ , x₂) (y₁ , y₂) | no ¬q = no (¬q ∘ cong proj₁)
    ≡-dec-Conᵇ-rel refl _ C HS HC (x₁ , x₂) (y₁ , y₂) | yes refl with ≡-dec-Con C HC x₂ y₂
    ≡-dec-Conᵇ-rel refl _ C HS HC (x₁ , x₂) (y₁ , y₂) | yes refl | yes refl = yes refl
    ≡-dec-Conᵇ-rel refl _ C HS HC (x₁ , x₂) (y₁ , y₂) | yes refl | no ¬q = no (¬q ∘ (λ { refl → refl }))

    ≡-dec-Con .(var _) var (lift refl) (lift refl) = yes refl
    ≡-dec-Con ._ (pi-irr ⦃ _ ⦄ ⦃ HC ⦄) x y = ≡-dec-Conᵇ-irr _ _ _ HC x y
    ≡-dec-Con ._ (pi-rel ⦃ HS ⦄ ⦃ HC ⦄) x y = ≡-dec-Conᵇ-rel _ _ _ HS HC x y
    ≡-dec-Con ._ (prod ⦃ HA ⦄ ⦃ HC ⦄) x y
      = Product.≡-dec (≡-dec-IndArd _ HA) (≡-dec-Con _ HC) x y
      -- TODO: inline this definition

    ≡-dec-μ ⟨ k₁ , x ⟩ ⟨ k₂ , y ⟩ with k₁ Fin.≟ k₂
    ≡-dec-μ ⟨ k₁ , x ⟩ ⟨ k₁ , y ⟩ | yes refl with ≡-dec-Con _ (lookupHelper DH k₁) x y
    ≡-dec-μ ⟨ k₁ , x ⟩ ⟨ k₁ , y ⟩ | yes refl | yes refl = yes refl
    ≡-dec-μ ⟨ k₁ , x ⟩ ⟨ k₁ , y ⟩ | yes refl | no ¬p = no (¬p ∘ λ { refl → refl })
    ≡-dec-μ ⟨ k₁ , x ⟩ ⟨ k₂ , y ⟩ | no  k≢k = no (k≢k ∘ cong (proj₁ ∘ ⟨_⟩⁻¹))

  deriveDecEq : ∀ {p} ⦃ DH : DecEqHelpers p ⦄ {i} → DecEq (A′ (p , i))
  deriveDecEq ⦃ DH ⦄ .DecEq._≟_ x y
    = map′ (λ p → trans (sym (from∘to _)) (trans (cong from p) (from∘to _)))
           (cong to) (≡-dec-μ DH (to x) (to y))
