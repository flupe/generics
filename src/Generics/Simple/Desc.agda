{-# OPTIONS --safe --without-K #-}

module Generics.Simple.Desc where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Data.Product
open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import Data.Fin.Base
open import Data.Vec.Base

private
  variable
    ℓ : Level
    n : ℕ

-- problem: too generic!! (and not quite enough)
data ConDesc (I : Set ℓ) : Set (lsuc ℓ) where
  κ : (γ : I)                         → ConDesc I
  ι : (γ : I)     (C :     ConDesc I) → ConDesc I
  σ : (S : Set ℓ) (C : S → ConDesc I) → ConDesc I

syntax σ S (λ x → B) = σ[ x ∈ S ] B

⟦_⟧C : ∀ {ℓ} {I : Set ℓ} → ConDesc I → (I → Set ℓ) → (I → Set ℓ)
⟦ κ γ   ⟧C X i = γ ≡ i
⟦ ι γ C ⟧C X i = X γ × ⟦ C ⟧C X i
⟦ σ S C ⟧C X i = Σ[ s ∈ S ] ⟦ C s ⟧C X i


Desc : (I : Set ℓ) → ℕ → Set (lsuc ℓ)
Desc I = Vec (ConDesc I)

⟦_⟧D : {I : Set ℓ} → Desc I n → (I → Set ℓ) → (I → Set ℓ) 
⟦_⟧D {n = n} D X i = Σ[ k ∈ Fin n ] ⟦ lookup D k ⟧C X i


data μ {I : Set ℓ} (D : Desc I n) (γ : I) : Set ℓ where
  ⟨_⟩ : ⟦ D ⟧D (μ D) γ → μ D γ
