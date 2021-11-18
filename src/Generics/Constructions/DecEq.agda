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
  OnlyFO : ∀ {V} → ConDesc P V I → Setω
  OnlyFO (var _) = Liftω ⊤
  OnlyFO (π _ _ _) = Liftω HigherOrderArgumentsNotSupported
  OnlyFO (A ⊗ B) = OnlyFO A ×ω OnlyFO B

  open HasDesc H
  open Helpers P I DecEq (const ⊤) OnlyFO

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
      decEqIndArg-wf : ∀ (C : ConDesc P V I) → OnlyFO C
                     → (x y : ⟦ C ⟧IndArg A′ (p , v))
                     → AllIndArgω Acc C x
                     → AllIndArgω Acc C y
                     → Dec (x ≡ y)

      decEqIndArg-wf (var i) H x y ax ay = decEq-wf x y ax ay
      decEqIndArg-wf (A ⊗ B) (HA , HB) (xa , xb) (ya , yb) (axa , axb) (aya , ayb)
        = map′ (λ (p , q) → cong₂ _,_ p q)
            (λ p → cong proj₁ p , cong proj₂ p)
            (decEqIndArg-wf _ HA xa ya axa aya ×-dec decEqIndArg-wf _ HB xb yb axb ayb)
      decEqIndArg-wf (π i S C) ()

      decEqCon-wf : (C   : ConDesc P V I)
                    ⦃ H  : ConHelper p C ⦄
                    (x y : ⟦ C ⟧Con A′ (p , v , i))
                  → AllConω Acc C x
                  → AllConω Acc C y
                  → Dec (x ≡ y)
      decEqCon-wf ._ ⦃ var ⦄ refl refl _ _ = yes refl
      decEqCon-wf ._ ⦃ pi-irr ⦃ _ ⦄ ⦃ H ⦄ ⦄ (irrv _ , x) (irrv _ , y) ax ay
        with decEqCon-wf _ ⦃ H ⦄ x y ax ay
      ... | yes refl = yes refl
      ... | no p     = no (p ∘ λ {refl → refl})
      decEqCon-wf ._ ⦃ pi-rel ⦃ dec ⦄ ⦃ H ⦄ ⦄ (s₁ , x) (s₂ , y) ax ay
        with dec .DecEq._≟_ s₁ s₂
      ... | no p     = no (p ∘ (λ { refl → refl }))
      ... | yes refl with decEqCon-wf _ ⦃ H ⦄ x y ax ay
      ... | yes refl = yes refl
      ... | no  p    = no (p ∘ (λ { refl → refl }))
      decEqCon-wf ._ ⦃ prod ⦃ HA ⦄ ⦄ (xa , xb) (ya , yb) (axa , axb) (aya , ayb) =
        map′ (λ (p , q) → cong₂ _,_ p q)
             (λ p → cong proj₁ p , cong proj₂ p)
             (decEqIndArg-wf _ HA xa ya axa aya ×-dec decEqCon-wf _ xb yb axb ayb)

      decEqData-wf : (x y : ⟦ D ⟧Data A′ (p , i))
                   → AllDataω Acc D x
                   → AllDataω Acc D y
                   → Decω (x ≡ω y)
      decEqData-wf (k₁ , x) (k₂ , y) ax ay with k₁ Fin.≟ k₂
      decEqData-wf (k  , x) (k  , y) ax ay | yes refl with decEqCon-wf _ ⦃ lookupHelper DH k ⦄ x y ax ay
      decEqData-wf (k  , x) (k  , y) ax ay | yes refl | yes refl = yesω refl
      decEqData-wf (k  , x) (k  , y) ax ay | yes refl | no x≢y   = noω λ { refl → x≢y refl }
      decEqData-wf (k₁ , x) (k₂ , y) ax ay | no k₁≢k₂ =
        noω λ { refl → k₁≢k₂ refl }

      decEq-wf : (x y : A′ (p , i)) → Acc x → Acc y → Dec (x ≡ y)
      decEq-wf x y (acc ax) (acc ay) with decEqData-wf (split x) (split y) ax ay
      ... | yesω p = yes (split-injective p)
      ... | noω  p = no  (λ e → p (cong≡ω split e))

  deriveDecEq : ∀ {p} ⦃ DH : DecEqHelpers p ⦄ {i} → DecEq (A′ (p , i))
  deriveDecEq ⦃ DH ⦄ .DecEq._≟_ x y
    = decEq-wf DH x y (wf x) (wf y)
