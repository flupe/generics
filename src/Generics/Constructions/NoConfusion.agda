{-# OPTIONS --safe #-}

module Generics.Constructions.NoConfusion where

open import Agda.Builtin.Reflection
open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc
open import Generics.HasDesc

open import Data.Fin.Properties as Fin
open import Data.Product.Properties
open import Data.Empty
open import Relation.Nullary


module NoConfusion {P} {I : ExTele P} {n ℓ} (D : DataDesc P I ℓ n) where

  variable
    V : ExTele P


  NoConfusionIndArg : ∀ {ℓ} (C : ConDesc P V I ℓ) {ℓ₂} {X : ⟦ P , I ⟧xtel → Set (ℓ ⊔ ℓ₂)}
                    → ∀ {pv} → (x y : ⟦ C ⟧IndArg ℓ₂ X pv) → Set (ℓ ⊔ ℓ₂)

  NoConfusionIndArgᵇ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃) (i : ArgInfo)
                       {X : ⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₄)}
                       (S : ⟦ P , V ⟧xtel → Set ℓ₂)
                       (C : ConDesc P (V ⊢< i > S) I ℓ₃)
                     → ∀ {pv} (x y : IndArgᵇ ℓ₄ e i X S C pv) → Set (ℓ₁ ⊔ ℓ₄)

  NoConfusionIndArg (var i) x y = x ≡ y
  NoConfusionIndArg (A ⊗ B) (xa , xb) (ya , yb) = NoConfusionIndArg A xa ya × NoConfusionIndArg B xb yb
  NoConfusionIndArg (π p i S C) x y = NoConfusionIndArgᵇ p i S C x y

  NoConfusionIndArgᵇ refl i S C {pv} x y = x ≡ y


  NoConfusionCon : ∀ {ℓ} (C : ConDesc P V I ℓ) {ℓ₂} {X : ⟦ P , I ⟧xtel → Set (ℓ ⊔ ℓ₂)}
                      → ∀ {pvi} → (x y : ⟦_⟧Con C ℓ₂ X pvi) → Set (ℓ ⊔ ℓ₂)

  NoConfusionConᵇ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃) (i : ArgInfo)
                       {X : ⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₄)}
                       (S : ⟦ P , V ⟧xtel → Set ℓ₂)
                       (C : ConDesc P (V ⊢< i > S) I ℓ₃)
                     → ∀ {pvi} (x y : Conᵇ ℓ₄ e i X S C pvi) → Set (ℓ₁ ⊔ ℓ₄)

  NoConfusionCon (var i) x y = Lift _ ⊤
  NoConfusionCon (π p i S C) x y = NoConfusionConᵇ p i S C x y
  NoConfusionCon (A ⊗ B) (xa , xb) (ya , yb) = NoConfusionIndArg A xa ya × NoConfusionCon B xb yb

  NoConfusionConᵇ refl i S C (xs , xd) (ys , yd) = Σ (xs ≡ ys) λ { refl → NoConfusionCon C xd yd }


  NoConf : ∀ {ℓ′} {X : ⟦ P , I ⟧xtel → Set (ℓ ⊔ ℓ′)}
         → ∀ {pi} (x y : ⟦ D ⟧Data ℓ′ X pi) → Set (ℓ ⊔ ℓ′)
  NoConf (kx , x) (ky , y) with kx Fin.≟ ky
  ... | yes refl = NoConfusionCon (lookupCon D kx) x y
  ... | no _     = Lift _ ⊥


  noConfIndArg-refl : ∀ {ℓ} (C : ConDesc P V I ℓ) {ℓ₂} {X : ⟦ P , I ⟧xtel → Set (ℓ ⊔ ℓ₂)}
                    → ∀ {pvi} → (x : ⟦ C ⟧IndArg ℓ₂ X pvi) → NoConfusionIndArg C x x

  noConfIndArgᵇ-refl : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃) (i : ArgInfo)
                       {X : ⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₄)}
                       (S : ⟦ P , V ⟧xtel → Set ℓ₂)
                       (C : ConDesc P (V ⊢< i > S) I ℓ₃)
                     → ∀ {pvi} (x : IndArgᵇ ℓ₄ e i X S C pvi) → NoConfusionIndArgᵇ e i S C x x

  noConfIndArg-refl (var i) x = refl
  noConfIndArg-refl (A ⊗ B) (xa , xb) = noConfIndArg-refl A xa , noConfIndArg-refl B xb
  noConfIndArg-refl (π p i S C) x = noConfIndArgᵇ-refl p i S C x

  noConfIndArgᵇ-refl refl i S C x = refl


  noConfCon-refl : ∀ {ℓ} (C : ConDesc P V I ℓ) {ℓ₂} {X : ⟦ P , I ⟧xtel → Set (ℓ ⊔ ℓ₂)}
                    → ∀ {pvi} → (x : ⟦_⟧Con C ℓ₂ X pvi) → NoConfusionCon C x x

  noConfConᵇ-refl : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃) (i : ArgInfo)
                    {X : ⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₄)}
                    (S : ⟦ P , V ⟧xtel → Set ℓ₂)
                    (C : ConDesc P (V ⊢< i > S) I ℓ₃)
                  → ∀ {pvi} (x : Conᵇ ℓ₄ e i X S C pvi) → NoConfusionConᵇ e i S C x x

  noConfCon-refl (var i) x = lift tt
  noConfCon-refl (A ⊗ B) (xa , xb) = noConfIndArg-refl A xa , noConfCon-refl B xb
  noConfCon-refl (π p i S C) x = noConfConᵇ-refl p i S C x

  noConfConᵇ-refl refl i S C (_ , x) = refl , noConfCon-refl C x


  noConfIndArg : ∀ {ℓ} (C : ConDesc P V I ℓ) {ℓ₂} {X : ⟦ P , I ⟧xtel → Set (ℓ ⊔ ℓ₂)}
               → ∀ {pvi} {x y : ⟦ C ⟧IndArg ℓ₂ X pvi} → NoConfusionIndArg C x y → x ≡ y

  noConfIndArgᵇ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃) (i : ArgInfo)
                  {X : ⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₄)}
                  (S : ⟦ P , V ⟧xtel → Set ℓ₂)
                  (C : ConDesc P (V ⊢< i > S) I ℓ₃)
                → ∀ {pvi} {x y : IndArgᵇ ℓ₄ e i X S C pvi} → NoConfusionIndArgᵇ e i S C x y → x ≡ y

  noConfIndArg (var i) nc = nc
  noConfIndArg (A ⊗ B) (nca , ncb) = cong₂ _,_ (noConfIndArg A nca) (noConfIndArg B ncb)
  noConfIndArg (π p i S C) nc = noConfIndArgᵇ p i S C nc

  noConfIndArgᵇ refl i S C nc = nc


  noConfCon : ∀ {ℓ} (C : ConDesc P V I ℓ) {ℓ₂} {X : ⟦ P , I ⟧xtel → Set (ℓ ⊔ ℓ₂)}
            → ∀ {pvi} → {x y : ⟦_⟧Con C ℓ₂ X pvi} → NoConfusionCon C x y → x ≡ y

  noConfConᵇ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃) (i : ArgInfo)
               {X : ⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₄)}
               (S : ⟦ P , V ⟧xtel → Set ℓ₂)
               (C : ConDesc P (V ⊢< i > S) I ℓ₃)
             → ∀ {pvi} {x y : Conᵇ ℓ₄ e i X S C pvi} → NoConfusionConᵇ e i S C x y → x ≡ y

  noConfCon (var i) {x = lift refl} {lift refl} nc = refl
  noConfCon (A ⊗ B) (nca , ncb) = cong₂ _,_ (noConfIndArg A nca) (noConfCon B ncb)
  noConfCon (π p i S C) nc = noConfConᵇ p i S C nc

  noConfConᵇ refl i S C (refl , nc) = cong (_ ,_) (noConfCon C nc)


  noConf : ∀ {ℓ′} {X : ⟦ P , I ⟧xtel → Set (ℓ ⊔ ℓ′)}
         → ∀ {pi} {x y : ⟦ D ⟧Data ℓ′ X pi} → x ≡ y → NoConf x y
  noConf {x = kx , x} {ky , _} refl with kx Fin.≟ ky
  ... | yes refl = noConfCon-refl (lookupCon D kx) x
  ... | no kx≢kx = lift (kx≢kx refl)

  noConf₂ : ∀ {ℓ′} {X : ⟦ P , I ⟧xtel → Set (ℓ ⊔ ℓ′)}
          → ∀ {pi} {x y : ⟦ D ⟧Data ℓ′ X pi} → NoConf x y → x ≡ y
  noConf₂ {x = kx , x} {ky , y} nc with kx Fin.≟ ky
  ... | yes refl = cong (kx ,_) (noConfCon (lookupCon D kx) nc)
  ... | no kx≢ky = ⊥-elim (Lift.lower nc)


module Confusion {P} {I : ExTele P} {ℓ} {A : Indexed P I ℓ} (H : HasDesc {P} {I} A) where

  open HasDesc H
  module NC = NoConfusion D

  NoConfusion : ∀ {pi} (x y : A′ pi) → Set ℓ
  NoConfusion x y = NC.NoConf (split x) (split y)

  noConfusion : ∀ {pi} {x y : A′ pi} → x ≡ y → NoConfusion x y
  noConfusion = NC.noConf ∘ cong split

  noConfusion₂ : ∀ {pi} {x y : A′ pi} → NoConfusion x y → x ≡ y
  noConfusion₂ {x = x} {y} = split-injective ∘ NC.noConf₂
