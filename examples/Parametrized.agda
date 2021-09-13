{-# OPTIONS --allow-unsolved-metas #-}
open import Generics.Prelude hiding (lookup)
open import Generics.HasDesc
open import Generics.Reflection

open import Generics.Constructions.Show
open import Generics.Constructions.Case
open import Generics.Constructions.Elim
open import Generics.Constructions.NoConfusion
open import Generics.Constructions.DecEq

open import Data.String hiding (show)
open import Data.Maybe.Base
open import Relation.Binary renaming (DecidableEquality to DecEq)

module Parametrized where


module Nat where

  natHasDesc : HasDesc ℕ
  natHasDesc = badconvert (testing ℕ)

  postulate P : ℕ → Set

  -- t : ∀ x → P x
  -- t = elim″ natHasDesc P {!!} {!!}

  elimℕ : ∀ {ℓ} (P : ℕ → Set ℓ) → P 0 → (∀ n → P n → P (suc n))
        → ∀ n → P n
  elimℕ P H0 Hn n = elim″ natHasDesc P {!!} H0 Hn n

  showℕ : ℕ → String
  showℕ = show natHasDesc

  decℕ : DecEq ℕ
  decℕ = ≡-dec natHasDesc (tt , ((tt , tt) , tt))

  suc-inj  : ∀ {a b} → ℕ.suc a ≡ ℕ.suc b → a ≡ b
  suc-inj = proj₁ ∘ Confusion.noConfusion natHasDesc

  suc-cong : ∀ {a b} → a ≡ b → ℕ.suc a ≡ ℕ.suc b
  suc-cong = Confusion.noConfusion₂ natHasDesc ∘ (_, lift tt)

  -- t₁ : ∀ x → P x
  -- t₁ = Case.case _ natHasDesc P λ where
  --                                   zero       → λ { (    lift refl) → {!!} }
  --                                   (suc zero) → λ { (n , lift refl) → {!!} }


module Vek where

  data vek (A : Set) : ℕ → Set where
    nil  : vek A 0
    cons : ∀ {n} → A → vek A n → vek A (suc n)

  vekHasDesc : HasDesc vek
  vekHasDesc = badconvert (testing vek)

  postulate P : {A : Set} {n : ℕ} → vek A n → Set

  t : ∀ {A} {n} (x : vek A n) → P x
  t = elim″ vekHasDesc P {!!} {!!} λ x g Pg → {!!}

  showV : {A : Set} → (A → String) → ∀ {n} → vek A n → String
  showV showA =
    show vekHasDesc Nat.showℕ showA

  decV : {A : Set} → (DecEq A) → ∀ {n} → DecEq (vek A n)
  decV decA =
    ≡-dec vekHasDesc
          (tt , ((Nat.decℕ , const (decA , const (tt , tt))) , tt))

  cons-inj₁  : ∀ {A n} {x y} {xs ys : vek A n}
             → vek.cons x xs ≡ vek.cons y ys → x ≡ y
  cons-inj₁ p =
    case Confusion.noConfusion vekHasDesc p of λ where
      (refl , p) → proj₁ p


module W where

  data W (A : Set) (B : A → Set) : Set where
    sup : (x : A) (f : B x → W A B) → W A B

  wHasDesc : HasDesc W
  wHasDesc = badconvert (testing W)

  postulate P : {A : Set} {B : A → Set} → W A B → Set

  -- t : ∀ {A} {B} (x : W A B) → P x
  -- t = elim″ wHasDesc P λ x g Pg → {!!}

module Id where

  data Id (A : Set) (x : A) : A → Set where
    refl : Id A x x

  idHasDesc : HasDesc Id
  idHasDesc = badconvert (testing Id)

  postulate P : {A : Set} {x y : A} → Id A x y → Set

  -- t : ∀ {A} {x y : A} (p : Id A x y) → P p
  -- t = elim″ idHasDesc P {!!}


-- TODO: universe-polymorphism

{-

module Test {ℓ} where

  maybeHasDesc : HasDesc (Maybe {ℓ})
  maybeHasDesc = badconvert (testing Maybe)

-}
