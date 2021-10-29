{-# OPTIONS --safe #-}
open import Generics.Prelude hiding (lookup; _≟_)
open import Generics.HasDesc
open import Generics.Desc
open import Generics.Telescope
open import Generics.Reflection

open import Generics.Constructions.Show as Show
open import Generics.Constructions.Case
open import Generics.Constructions.Elim
open import Generics.Constructions.Fold
open import Generics.Constructions.Cong
open import Generics.Helpers
-- open import Generics.Constructions.DecEq

open import Relation.Nullary
open import Relation.Nullary.Decidable as Decidable
open import Relation.Binary.HeterogeneousEquality.Core using (_≅_; refl)

open import Data.String hiding (show; _≟_; length)
open import Data.Maybe.Base
open import Data.Nat.Base using (_*_)


module Parametrized where

open Show.Show ⦃...⦄


module Nat where

  instance
    natD : HasDesc ℕ
    natD = deriveDesc ℕ

  ---------------------------
  -- Deriving the eliminator

  plus : ℕ → ℕ → ℕ
  plus n = elim (const ℕ) n (const suc)

  mult : ℕ → ℕ → ℕ
  mult n = elim (const ℕ) 0 (const (plus n))

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
  -- Deriving fold

  foldℕ = deriveFold natD

  t : ℕ
  t = foldℕ 1 suc 2

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

  -----------------------
  -- Deriving congruence

  congℕ = deriveCong natD

  ze≅ze : 0 ≅ 0
  ze≅ze = congℕ Fin.zero

  su≅su : ∀ {n m} → n ≅ m → suc n ≅ suc m
  su≅su = congℕ (suc zero)


  -------------------------------
  -- Deriving decidable equality

  -- instance decℕ : DecEq ℕ
  --          decℕ = deriveDecEq natD

  -- _ : 3 ≟ 3 ≡ yes refl
  -- _ = refl

  -- _ : 3 ≟ 2 ≡ no _
  -- _ = refl

module ListDemo where

  data list (A : Set) : Set where
    []  : list A
    _∷_ : A → list A → list A

  listD : HasDesc list
  listD = deriveDesc list

  foldList = deriveFold listD

  sum : list ℕ → ℕ
  sum = foldList 0 _+_

  []-sum : sum [] ≡ 0
  []-sum = refl

  ∷-sum : ∀ {x xs} → sum (x ∷ xs) ≡ x + sum xs
  ∷-sum = refl

  mul : list ℕ → ℕ
  mul = foldList 1 _*_

module Vek where
  private variable A : Set
                   n : ℕ

  data Vek (A : Set) : ℕ → Set where
    nil  : Vek A 0
    cons : ∀ {n} → A → Vek A n → Vek A (suc n)

  instance
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

  ---------------------------
  -- Deriving fold

  foldVek = deriveFold vekD

  vekToList : ∀ {A n} → Vek A n → List A
  vekToList = foldVek [] _∷_

  -----------------------
  -- Deriving congruence

  congV = deriveCong vekD

  []≅[] : ∀ {A} → nil {A} ≅ nil {A}
  []≅[] = congV zero

  cong-cons : ∀ {A n} {x y : A} → x ≅ y → {xs ys : Vek A n} → xs ≅ ys
            → cons x xs ≅ cons y ys
  cong-cons = congV (suc zero) refl

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


module Irrelevance where

  data Squash (A : Set) : Set where
    squash : .(x : A) → Squash A

  -- Irrelevant arguments are supported
  squashD : HasDesc Squash
  squashD = deriveDesc Squash

  -----------------
  -- Deriving fold

  foldSquash : ∀ {A X : Set} → (.A → X) → Squash A → X
  foldSquash = deriveFold squashD

  ------------------------------
  -- Deriving printing function

  -- Because the value of type A is irrelevant,
  -- we don't require an instance of Show A
  instance showSquash : ∀ {A} → Show (Squash A)
           showSquash = deriveShow squashD

  -- Indeed, we use the argument name when printing irrelevant args
  _ : show (squash 3) ≡ "squash (.x)"
  _ = refl
