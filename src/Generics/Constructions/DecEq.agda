{-# OPTIONS --safe #-}

module Generics.Constructions.DecEq where

open import Generics.Prelude hiding (lookup; _≟_)
open import Generics.Telescope
open import Generics.Desc
open import Generics.All
open import Generics.HasDesc

import Generics.Helpers as Helpers

import Data.Fin.Properties as Fin
import Data.Product.Properties as Product

open import Relation.Nullary.Decidable as Decidable
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary using (DecidableEquality)
open import Relation.Nullary.Product

record DecEq {l} (A : Set l) : Set l where
  field _≟_ : DecidableEquality A

module _ {P I ℓ}
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

    mutual
      decEqIndArg-wf : ∀ (C : ConDesc P V I ℓ) → OnlyFO C
                     → (x y : ⟦ C ⟧IndArg ℓ A′ (p , v))
                     → AllIndArg C A′ Acc x
                     → AllIndArg C A′ Acc y
                     → Dec (x ≡ y)

      decEqIndArg-wf (var i) H x y (lift ax) (lift ay) = decEq-wf x y ax ay
      decEqIndArg-wf (A ⊗ B) (HA ,ω HB) (xa , xb) (ya , yb) (axa , axb) (aya , ayb)
        = map′ (λ (p , q) → cong₂ _,_ p q)
               (λ p → cong proj₁ p , cong proj₂ p)
               (decEqIndArg-wf _ HA xa ya axa aya ×-dec decEqIndArg-wf _ HB xb yb axb ayb)
      decEqIndArg-wf (π p i S C) ()

      decEqCon-wf : (C   : ConDesc P V I ℓ)
                    ⦃ H   : ConHelper p C ⦄
                    (x y : ⟦ C ⟧Con ℓ A′ (p , v , i))
                  → AllCon C A′ Acc x
                  → AllCon C A′ Acc y
                  → Dec (x ≡ y)

      decEqConᵇ-wf-irr : ∀ {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) {vs q}
                       (let ia = ai vs irrelevant q)
                       (S : ⟦ P , V ⟧xtel → Set ℓ₂)
                       (C : ConDesc P (V ⊢< ia > S) I ℓ)
                     → ConHelper p C
                     → (x y : (Conᵇ ℓ e _ A′ S C (p , v , i)))
                     → AllConᵇ e ia A′ S C Acc x
                     → AllConᵇ e ia A′ S C Acc y
                     → Dec (x ≡ y)
      decEqConᵇ-fw-rel : ∀ {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) {vs q}
                       (let ia = ai vs relevant q)
                       (S : ⟦ P , V ⟧xtel → Set ℓ₂)
                       (C : ConDesc P (V ⊢< ia > S) I ℓ)
                     → DecEq (S (p , v))
                     → ConHelper p C
                     → (x y : (Conᵇ ℓ e _ A′ S C (p , v , i)))
                     → AllConᵇ e ia A′ S C Acc x
                     → AllConᵇ e ia A′ S C Acc y
                     → Dec (x ≡ y)
      decEqCon-wf _ ⦃ var ⦄ (lift refl) (lift refl) _ _ = yes refl
      decEqCon-wf ._ ⦃ pi-irr ⦃ _ ⦄ ⦃ H ⦄ ⦄ x y ax ay =
        decEqConᵇ-wf-irr _ _ _ H x y ax ay
      decEqCon-wf ._ ⦃ pi-rel ⦃ dec ⦄ ⦃ H ⦄ ⦄ x y ax ay =
        decEqConᵇ-fw-rel _ _ _ dec H x y ax ay
      decEqCon-wf ._ ⦃ prod ⦃ HA ⦄ ⦄ (xa , xb) (ya , yb) (axa , axb) (aya , ayb) =
        map′ (λ (p , q) → cong₂ _,_ p q)
             (λ p → cong proj₁ p , cong proj₂ p)
             (decEqIndArg-wf _ HA xa ya axa aya ×-dec decEqCon-wf _ xb yb axb ayb)

      decEqConᵇ-wf-irr refl S C H (s₁ , x) (s₂ , y) ax ay with irr≡ _ s₁ s₂
      decEqConᵇ-wf-irr refl S C H (s₁ , x) (s₂ , y) ax ay | refl with decEqCon-wf C ⦃ H ⦄ x y ax ay
      decEqConᵇ-wf-irr refl S C H (s₁ , x) (s₂ , y) ax ay | refl | yes refl = yes refl
      decEqConᵇ-wf-irr refl S C H (s₁ , x) (s₂ , y) ax ay | refl | no  ¬p   = no (¬p ∘ (λ { refl → refl }))

      decEqConᵇ-fw-rel refl S C dec H (s₁ , x) (s₂ , y) ax ay with DecEq._≟_ dec s₁ s₂
      decEqConᵇ-fw-rel refl S C dec H (s  , x) (s  , y) ax ay | yes refl with decEqCon-wf _ ⦃ H ⦄ x y ax ay
      decEqConᵇ-fw-rel refl S C dec H (s  , x) (s  , x) ax ay | yes refl | yes refl = yes refl
      decEqConᵇ-fw-rel refl S C dec H (s  , x) (s  , y) ax ay | yes refl | no x≢y   = no (x≢y ∘ λ { refl → refl })
      decEqConᵇ-fw-rel refl S C dec H (s₁ , x) (s₂ , y) ax ay | no s₁≢s₂ = no (s₁≢s₂ ∘ λ { refl → refl })

      decEqData-wf : (x y : ⟦ D ⟧Data ℓ A′ (p , i))
                   → AllData D A′ Acc x
                   → AllData D A′ Acc y
                   → Dec (x ≡ y)
      decEqData-wf (k₁ , x) (k₂ , y) ax ay with k₁ Fin.≟ k₂
      decEqData-wf (k  , x) (k  , y) ax ay | yes refl with decEqCon-wf _ ⦃ lookupHelper DH k ⦄ x y ax ay
      decEqData-wf (k  , x) (k  , y) ax ay | yes refl | yes refl = yes refl
      decEqData-wf (k  , x) (k  , y) ax ay | yes refl | no x≢y  = no (x≢y ∘ λ { refl → refl })
      decEqData-wf (k₁ , x) (k₂ , y) ax ay | no k₁≢k₂ = no (k₁≢k₂ ∘ cong proj₁)

      decEq-wf : (x y : A′ (p , i)) → Acc x → Acc y → Dec (x ≡ y)
      decEq-wf x y (acc ax) (acc ay)
        = map′ split-injective (cong split) (decEqData-wf (split x) (split y) ax ay)

  deriveDecEq : ∀ {p} ⦃ DH : DecEqHelpers p ⦄ {i} → DecEq (A′ (p , i))
  deriveDecEq ⦃ DH ⦄ .DecEq._≟_ x y
    = decEq-wf DH x y (wf x) (wf y)
