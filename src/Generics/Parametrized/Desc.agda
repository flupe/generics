{-# OPTIONS --safe --without-K #-}
module Generics.Parametrized.Desc where

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Data.Unit
open import Data.Product
open import Data.List.Base hiding (lookup; [_])
open import Function.Base
open import Data.Fin.Base hiding (lift)
open import Data.Nat.Base hiding (_⊔_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Level using (Lift; lift)

open import Generics.Parametrized.Telescope


data Desc (P : Telescope ⊤) (V : ExTele P) (I : ExTele P) : Setω where
  var : (((p , v) : Σ[ P ⇒ V ]) → tel I p) → Desc P V I
  π   : ∀ {ℓ} (S : Σ[ P ⇒ V ] → Set ℓ) → Desc P (V ⊢ S) I → Desc P V I
  _⊗_ : Desc P V I → Desc P V I → Desc P V I


C⟦_⟧ℓ : ∀ {P} {V I : ExTele P} → Desc P V I → Level
C⟦ var _     ⟧ℓ = lzero
C⟦ π {ℓ} S D ⟧ℓ = ℓ ⊔ C⟦ D ⟧ℓ
C⟦ A ⊗ B     ⟧ℓ = C⟦ A ⟧ℓ ⊔ C⟦ B ⟧ℓ


C⟦_⟧ : ∀ {P} {V I : ExTele P} (D : Desc P V I) (ℓ : Level)
    → (Σ[ P ⇒ I ] → Set (ℓ ⊔ C⟦ D ⟧ℓ ⊔ telLevel I))
    → (Σ[ P ⇒ V ] → Set (ℓ ⊔ C⟦ D ⟧ℓ ⊔ telLevel I))
C⟦ var i     ⟧ ℓ X pv@(p , v) = X (p , (i pv))
C⟦_⟧ {V = ε} (π {ℓ} S D) ℓ′ X pv@(p , _) = (s : S pv) → C⟦ D ⟧ (ℓ ⊔ ℓ′) X (p , s)
C⟦_⟧ {V = V ⊢ f} (π {ℓ} S D) ℓ′ X pv@(p , v) = (s : S pv) → C⟦ D ⟧ (ℓ ⊔ ℓ′) X (p , v , s)
C⟦ A ⊗ B ⟧ ℓ X pv = C⟦ A ⟧ (ℓ ⊔ C⟦ B ⟧ℓ) X pv × C⟦ B ⟧ (ℓ ⊔ C⟦ A ⟧ℓ) X pv


Extend : ∀ {P} {V I : ExTele P} (D : Desc P V I) (ℓ : Level)
       → (Σ[ P ⇒ I ]     → Set (ℓ ⊔ C⟦ D ⟧ℓ ⊔ telLevel I))
       → (Σ[ P ⇒ V & I ] → Set (ℓ ⊔ C⟦ D ⟧ℓ ⊔ telLevel I))
Extend {P} {I = I} (var x) ℓ X (p , v , i) =
  Lift (ℓ ⊔ telLevel I) (x (p , v) ≡ i)
Extend {V = ε} (π {ℓ′} S D) ℓ X (p , v , i)
  = Σ[ s ∈ S (p , v) ] Extend D (ℓ ⊔ ℓ′) X (p , s , i)
Extend {V = V ⊢ f} (π {ℓ′} S D) ℓ X (p , v , i)
  = Σ[ s ∈ S (p , v) ] Extend D (ℓ ⊔ ℓ′) X (p , (v , s) , i)
Extend (A ⊗ B) ℓ X pvi@(p , v , i) =
  C⟦ A ⟧ (ℓ ⊔ C⟦ B ⟧ℓ) X (p , v) × Extend B (ℓ ⊔ C⟦ A ⟧ℓ) X pvi


data DDesc P (I : ExTele P) : ℕ → Setω where
  []  : DDesc P I 0
  _∷_ : ∀ {n} (D : Desc P ε I) (DS : DDesc P I n) → DDesc P I (suc n)

lookup : ∀ {P} {I : ExTele P} {n} → DDesc P I n → Fin n → Desc P ε I
lookup (D ∷ DS) zero = D
lookup (D ∷ DS) (suc k) = lookup DS k


⟦_⟧ℓ : ∀ {P} {I : ExTele P} {n} → DDesc P I n → Level
⟦ []     ⟧ℓ = lzero
⟦ D ∷ DS ⟧ℓ = C⟦ D ⟧ℓ ⊔ ⟦ DS ⟧ℓ

lvl : ∀ {P} {I : ExTele P} {n} {D : DDesc P I n} ℓ (k : Fin n)
    → ℓ ⊔ C⟦ lookup D k ⟧ℓ ⊔ ⟦ D ⟧ℓ ≡ ℓ ⊔ ⟦ D ⟧ℓ
lvl {D = x ∷ D} ℓ (zero )  = refl
lvl {D = x ∷ D} ℓ (suc k) = cong (ℓ ⊔ C⟦ x ⟧ℓ ⊔_) (lvl {D = D} ℓ k)

shift : ∀ {a b} → a ≡ b → Set a → Set b
shift refl A = A


⟦_⟧ : ∀ {P} {I : ExTele P} {n} (D : DDesc P I n) (ℓ : Level)
       → (Σ[ P ⇒ I ] → Set (ℓ ⊔ ⟦ D ⟧ℓ ⊔ telLevel I))
       → (Σ[ P ⇒ I ] → Set (ℓ ⊔ ⟦ D ⟧ℓ ⊔ telLevel I))
⟦_⟧ {P} {I} {n} D ℓ X (p , i) =
  Σ[ k ∈ Fin n ] (shift (lvl {I = I} {D = D} (ℓ ⊔ telLevel I) k)
    (Extend (lookup D k) (ℓ ⊔ ⟦ D ⟧ℓ) (shift (sym (lvl {D = D} (ℓ ⊔ telLevel I) k)) ∘ X) (p , tt , i)))

data μ {P} {I : ExTele P} {n} (D : DDesc P I n) (pi : Σ[ P ⇒ I ])
     : Set (⟦ D ⟧ℓ ⊔ telLevel I) where
  ⟨_⟩ : ⟦ D ⟧ lzero (μ D) (proj₁ pi , proj₂ pi) → μ D pi

-- (Extend (lookup D k) (ℓ ⊔ telLevel I) (shift (sym (lvl ℓ k)) ∘ X) (p , tt , i)))

