{-# OPTIONS --safe #-}
open import Generics.Prelude hiding (lookup; _≟_)
open import Generics.HasDesc
open import Generics.Desc
open import Generics.Telescope
open import Generics.Reflection

open import Generics.Constructions.Show as Show hiding (show)
open import Generics.Constructions.Case
open import Generics.Constructions.Elim
open import Generics.Constructions.DecEq
open import Generics.Helpers

open import Relation.Nullary
open import Relation.Nullary.Decidable as Decidable

open import Data.String hiding (show; _≟_; length)
open import Data.Maybe.Base


module Parametrized where

open Show.Show ⦃...⦄
open DecEq ⦃...⦄


module Nat where

  natD : HasDesc ℕ
  natD = deriveDesc ℕ

  ---------------------------
  -- Deriving the eliminator

  elimℕ = deriveElim natD

  plus : ℕ → ℕ → ℕ
  plus n = elimℕ (const ℕ) n (const suc)

  mult : ℕ → ℕ → ℕ
  mult n = elimℕ (const ℕ) 0 (const (plus n))

  -- things defined with the eliminator reduce properly on open terms

  plus0 : ∀ {n} → plus n 0 ≡ n
  plus0 = refl

  plusS : ∀ {n m} → plus n (suc m) ≡ suc (plus n m)
  plusS = refl

  mult0 : ∀ {n} → mult n 0 ≡ 0
  mult0 = refl

  multS : ∀ {n m} → mult n (suc m) ≡ plus n (mult n m)
  multS = refl

  -----------------
  -- Deriving show

  instance showℕ : Show ℕ
           showℕ = deriveShow natD
  
  _ : show 2 ≡ "suc (suc (zero))"
  _ = refl

  ------------------------------------
  -- Deriving case analysis principle

  caseℕ = deriveCase natD

  pred : ℕ → ℕ
  pred = caseℕ (const ℕ) 0 id

  pred0 : pred 0 ≡ 0
  pred0 = refl

  predS : ∀ {n} → pred (suc n) ≡ n
  predS = refl

  -------------------------------
  -- Deriving decidable equality

  instance decℕ : DecEq ℕ
           decℕ = deriveDecEq natD

  _ : 3 ≟ 3 ≡ yes refl
  _ = refl

  _ : 3 ≟ 2 ≡ no _
  _ = refl


module Vek where
  private variable A : Set
                   n : ℕ

  data Vek (A : Set) : ℕ → Set where
    nil  : Vek A 0
    cons : ∀ {n} → A → Vek A n → Vek A (suc n)

  vekD : HasDesc Vek
  vekD = deriveDesc Vek

  ---------------------------
  -- Deriving the eliminator

  elimVek = deriveElim vekD

  length : Vek A n → ℕ
  length = elimVek (const ℕ) 0 (λ x xs n → suc n)

  length0 : length (nil {A = A}) ≡ 0
  length0 = refl

  lengthP : (x : Vek A n) → length x ≡ n
  lengthP = elimVek (λ {n} x → length x ≡ n) refl λ x xs Pxs → cong suc Pxs


module WType  where

  private variable A : Set
                   B : A → Set
                   c : Level

  data W (A : Set) (B : A → Set) : Set where
    node : ∀ x → (B x → W A B) → W A B

  wD : HasDesc W
  wD = deriveDesc W

  ---------------------------
  -- Deriving the eliminator
  
  elimW : (Pr : W A B → Set c)
        → (∀ x g → (∀ y → Pr (g y)) → Pr (node x g) )
        → ∀ x → Pr x
  elimW = deriveElim wD

  elimW-node
    : {Pr : W A B → Set c}
      (M : ∀ x g → (∀ y → Pr (g y)) → Pr (node x g) )
    → ∀ {x g} → elimW Pr M (node x g) ≡ M x g (λ y → elimW Pr M (g y))
  elimW-node M = refl
