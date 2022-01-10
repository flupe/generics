{-# OPTIONS --safe #-}

module Parametrized where

open import Generics

open import Agda.Primitive
open import Function.Base
open import Data.Nat.Base hiding (pred)
open import Data.Fin.Base hiding (pred; _+_)
open import Data.List.Base hiding (sum; length)

open import Relation.Nullary
open import Relation.Nullary.Decidable as Decidable
open import Relation.Binary.HeterogeneousEquality.Core using (_≅_; refl)
open import Relation.Binary.PropositionalEquality

open import Data.String hiding (show; _≟_; length)
open import Data.Maybe.Base


module Nat where

  instance
    natD : HasDesc ℕ
    natD = deriveDesc ℕ

  ---------------------------
  -- Deriving the eliminator

  elimℕ = deriveElim natD

  plus : ℕ → ℕ → ℕ
  plus n = elimℕ (const ℕ) n suc

  mult : ℕ → ℕ → ℕ
  mult n = elimℕ (const ℕ) 0 (plus n)

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
  ze≅ze = congℕ zero

  su≅su : ∀ {n m} → n ≅ m → suc n ≅ suc m
  su≅su = congℕ (suc zero)

  -------------------------------
  -- Deriving decidable equality

  instance decℕ : DecEq ℕ
           decℕ = deriveDecEq natD

  _ : 3 ≟ 3 ≡ yes refl
  _ = refl

  _ : 3 ≟ 2 ≡ no _
  _ = refl


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


module Vec where
  private variable A : Set
                   n : ℕ

  data Vec (A : Set) : ℕ → Set where
    nil  : Vec A 0
    cons : ∀ {n} → A → Vec A n → Vec A (suc n)

  instance
    vekD : HasDesc Vec
    vekD = deriveDesc Vec

  ---------------------------
  -- Deriving the eliminator

  elimVec = deriveElim vekD

  length : Vec A n → ℕ
  length = elimVec (const ℕ) 0 (const suc)

  length0 : length (nil {A}) ≡ 0
  length0 = refl

  lengthP : (x : Vec A n) → length x ≡ n
  lengthP = elimVec (λ {n} x → length x ≡ n) refl (const (cong suc))

  ---------------------------
  -- Deriving fold

  foldVec = deriveFold vekD

  vekToList : ∀ {A n} → Vec A n → List A
  vekToList = foldVec [] _∷_

  -----------------------
  -- Deriving congruence

  congV = deriveCong vekD

  []≅[] : ∀ {A} → nil {A} ≅ nil {A}
  []≅[] = congV zero

  cong-cons : ∀ {A n} {x y : A} → x ≅ y → {xs ys : Vec A n} → xs ≅ ys
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
        → (∀ x {g} → (∀ y → Pr (g y)) → Pr (node x g) )
        → ∀ x → Pr x
  elimW = deriveElim wD

  elimW-node
    : {Pr : W A B → Set c}
      (M : ∀ x {g} → (∀ y → Pr (g y)) → Pr (node x g) )
    → ∀ {x g}
    → elimW Pr M (node x g) ≡ M x (λ y → elimW Pr M (g y))
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

  _ : show (squash 3) ≡ "squash (._)"
  _ = refl
