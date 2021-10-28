{-# OPTIONS --sized-types --without-K #-}

module Generics.HasDesc where

open import Data.String.Base
open import Agda.Builtin.Size

open import Generics.Prelude hiding (lookup ; pi)
open import Generics.Telescope
open import Generics.Desc


import Generics.Accessibility as Accessibility


private
  variable
    P  : Telescope ⊤
    I  : ExTele P
    pi : ⟦ P , I ⟧xtel


record HasDesc {ℓ} (A : Indexed P I ℓ) : Setω where
  A′ : ⟦ P , I ⟧xtel → Set ℓ
  A′ = uncurry P I A

  field
    {n} : ℕ
    D   : DataDesc P I n

    names : Vec String n

    constr : ⟦ D ⟧Data A′ pi → A′ pi
    split  : A′ pi → ⟦ D ⟧Data A′ pi

    constr∘split : (x : A′ pi          ) → constr (split x) ≡  x
    split∘constr : (x : ⟦ D ⟧Data A′ pi) → split (constr x) ≡ω x

  open Accessibility A D split public

  field wf : (x : A′ pi) → Acc x ∞

  split-injective : ∀ {pi} {x y : A′ pi} → split x ≡ω split y → x ≡ y
  split-injective {x = x} {y} sx≡sy = begin
    x                ≡⟨ sym (constr∘split x) ⟩
    constr (split x) ≡⟨ congω constr sx≡sy   ⟩
    constr (split y) ≡⟨ constr∘split y       ⟩
    y                ∎ where open ≡-Reasoning

{-

  to : A′ pi → μ D pi
  to x = to-wf x (wf x)

  -- We define `from` using `constr`
  fromIndArg : ∀ {V} {C : ConDesc P V I ℓ} {pv}
             → ⟦ C ⟧IndArg (levelOfTel I) (μ D) pv
             → ⟦ C ⟧IndArg ℓ A′ pv

  fromIndArgᵇ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ai {p} {v}
           → (S : ⟦ P , V ⟧xtel → Set ℓ₂)
           → (C : ConDesc P (V ⊢< ai > S) I ℓ)
           → IndArgᵇ (levelOfTel I) e ai (μ D) S C (p , v)
           → IndArgᵇ ℓ e ai A′ S C (p , v)

  fromCon : ∀ {V} {C : ConDesc P V I ℓ} {pvi}
          → ⟦ C ⟧Con (levelOfTel I) (μ D) pvi
          → ⟦ C ⟧Con ℓ A′ pvi

  fromConᵇ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ai {p} {v}
           → (S : ⟦ P , V ⟧xtel → Set ℓ₂)
           → (C : ConDesc P (V ⊢< ai > S) I ℓ)
           → Conᵇ (levelOfTel I) e ai (μ D) S C (p , v)
           → Conᵇ ℓ e ai A′ S C (p , v)

  from : μ D pi → A′ pi

  fromIndArg {C = var _} x = from x
  fromIndArg {C = π e _ S C} x = fromIndArgᵇ e _ S C x
  fromIndArg {C = A ⊗ B} (xa , xb) = fromIndArg {C = A} xa , fromIndArg {C = B} xb

  fromIndArgᵇ refl _ S C x s = fromIndArg {C = C} (x s)

  fromCon {C = var _} (lift refl) = lift refl
  fromCon {C = π e _ S C} x = fromConᵇ e _ S C x
  fromCon {C = A ⊗ B} (xa , xb) = fromIndArg {C = A} xa , fromCon {C = B} xb

  fromConᵇ refl _ _ C (s , x) = s , fromCon {C = C} x

  from ⟨ k , x ⟩ = constr (k , fromCon {C = lookupCon D k} x)


-}
