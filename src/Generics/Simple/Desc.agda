{-# OPTIONS --safe --without-K #-}

module Generics.Simple.Desc where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Data.Product
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Relation.Binary.PropositionalEquality
open import Data.Product.Properties
open import Function.Bundles
open import Data.Unit.Polymorphic

open import Data.Fin.Base
open import Data.Vec.Base
open import Function.Base

private
  variable
    ℓ : Level
    n : ℕ

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


PredC : ∀ {I : Set ℓ} {A : I → Set ℓ} {j} (P : ∀ {γ} → A γ → Set j)
        (C : ConDesc I) → ∀ {γ} → ⟦ C ⟧C A γ → Set j
PredC P (κ γ  ) tt = ⊤
PredC P (ι γ C) (x , d) = P x × PredC P C d
PredC P (σ S C) (s , d) = PredC P (C s) d

PredD : ∀ {I : Set ℓ} {n} (D : Desc I n) {j} (P : ∀ {γ} → μ D γ → Set j)
      → ∀ {γ} → μ D γ → Set j
PredD D P ⟨ k , x ⟩ = PredC P (lookup D k) x


mapC : ∀ {ℓ} {I : Set ℓ} {A B : I → Set ℓ}
     → (∀ {γ} → A γ → B γ)
     → ∀ {C γ} → ⟦ C ⟧C A γ → ⟦ C ⟧C B γ
mapC f {κ γ  } (x    ) = x
mapC f {ι γ C} (x , d) = f x , mapC f d
mapC f {σ S C} (s , d) = s   , mapC f d


mapC-id : ∀ {ℓ} {I : Set ℓ} {A : I → Set ℓ}
          {f   : ∀ {γ} → A γ → A γ}
          (fid : ∀ {γ} (x : A γ) → f x ≡ x)
          {C γ} {x : ⟦ C ⟧C A γ} → mapC f x ≡ x
mapC-id fid {κ γ  } {x = x} = refl
mapC-id {f = f} fid {ι γ C} {x = x , d}
  rewrite fid x = Inverse.f Σ-≡,≡↔≡ (refl , mapC-id fid)
mapC-id fid {σ S C} = Inverse.f Σ-≡,≡↔≡ (refl , mapC-id fid)

mapC-∘  : ∀ {ℓ} {I : Set ℓ} {A B C : I → Set ℓ}
          {f : ∀ {γ} → A γ → B γ}
          {g : ∀ {γ} → B γ → C γ}
        → ∀ {C′ γ} {x : ⟦ C′ ⟧C A γ} → mapC (g ∘ f) x ≡ mapC g (mapC f x)
mapC-∘ {C′ = κ γ  } = refl
mapC-∘ {C′ = ι γ C} = Inverse.f Σ-≡,≡↔≡ (refl , mapC-∘)
mapC-∘ {C′ = σ S C} = Inverse.f Σ-≡,≡↔≡ (refl , mapC-∘)
