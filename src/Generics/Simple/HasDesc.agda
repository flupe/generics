{-# OPTIONS --safe --without-K #-}

module Generics.Simple.HasDesc where

open import Agda.Primitive
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Sigma
open import Agda.Builtin.String
open import Agda.Builtin.Equality
open import Data.Fin.Base
open import Data.Vec.Base
open import Function.Base

open import Generics.Simple.Desc

private
  variable
    ℓ : Level

module _ {ℓ} {I : Set ℓ} (A : I → Set ℓ) where

  Constr : ConDesc I → Set ℓ
  Constr (κ γ  ) = A γ
  Constr (ι γ C) = A γ     → Constr C
  Constr (σ S C) = (s : S) → Constr (C s)

  module _ {n} {D : Desc I n} (to   : ∀ {γ} → A γ → μ D γ) where

    Constr-proof′ : (C : ConDesc I)
                   (tie : {γ : I} → ⟦ C ⟧C (μ D) γ → A γ → Set ℓ)
                   → Constr C → Set ℓ
    Constr-proof′ (κ γ  ) tie constr = tie refl constr
    Constr-proof′ (ι γ C) tie constr = (x : A γ) → Constr-proof′ C (tie ∘ (to x ,_)) (constr x)
    Constr-proof′ (σ S C) tie constr = (s : S)   → Constr-proof′ (C s) (tie ∘ (s ,_)) (constr s)

    Constr-proof : (∀ {γ} → μ D γ → A γ) → ∀ {k} → Constr (lookup D k) → Set ℓ
    Constr-proof from {k} = Constr-proof′ (lookup D k) λ x′ x → x ≡ from ⟨ k , x′ ⟩


record HasDesc {I : Set ℓ} (A : I → Set ℓ) : Set (lsuc ℓ) where
  field
    {n} : ℕ
    D   : Desc I n

    names : Vec String n

    to   : ∀ {i} → A i → μ D i
    from : ∀ {i} → μ D i → A i

    to∘from : ∀ {i} (x : μ D i) → to (from x) ≡ x
    from∘to : ∀ {i} (x : A i  ) → from (to x) ≡ x

  field
    -- constructors of A
    constr : ∀ k → Constr A (lookup D k)

    -- proof that constr indeed holds the constructors of A
    constr-proof : ∀ k → Constr-proof A to from (constr k)
