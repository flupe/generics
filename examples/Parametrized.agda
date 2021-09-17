{-# OPTIONS --allow-unsolved-metas #-}
open import Generics.Prelude hiding (lookup)
open import Generics.HasDesc
open import Generics.Reflection

open import Generics.Constructions.Show
open import Generics.Constructions.Case
open import Generics.Constructions.Elim
open import Generics.Constructions.NoConfusion
open import Generics.Constructions.DecEq
open import Generics.Helpers

open import Data.String hiding (show)
open import Data.Maybe.Base

module Parametrized where


natD : HasDesc ℕ
natD = deriveDesc ℕ

instance
  showℕ : Show ℕ
  showℕ = deriveShow natD

  decℕ : DecEq ℕ
  decℕ = deriveDecEq natD

data vek (A : Set) : ℕ → Set where
  nil  : vek A 0
  cons : ∀ {n} → A → vek A n → vek A (suc n)

vekD : HasDesc vek
vekD = deriveDesc vek

instance
  showVek : ∀ {A} ⦃ showA : Show A ⦄ {n} → Show (vek A n)
  showVek = deriveShow vekD

  decVek : {A : Set} → ⦃ DecEq A ⦄ → ∀ {n} → DecEq (vek A n)
  decVek = deriveDecEq vekD

data S : Set where
  ok : (ℕ → S) → S

sD : HasDesc S
sD = deriveDesc S

-- No instance of type OnlyFO ... GOOD!
-- decS : DecEq S
-- decS = deriveDecEq sD

module Nat where
  postulate P : ℕ → Set
  
  elimℕ : ∀ {ℓ} (P : ℕ → Set ℓ) → P 0 → (∀ n → P n → P (suc n))
        → ∀ n → P n
  elimℕ P H0 Hn n = elim″ natD P {!!} H0 Hn n
  
  
  
  suc-inj  : ∀ {a b} → ℕ.suc a ≡ ℕ.suc b → a ≡ b
  suc-inj = proj₁ ∘ Confusion.noConfusion natD
  
  suc-cong : ∀ {a b} → a ≡ b → ℕ.suc a ≡ ℕ.suc b
  suc-cong = Confusion.noConfusion₂ natD ∘ (_, lift tt)

  -- t₁ : ∀ x → P x
  -- t₁ = Case.case _ natHasDesc P λ where
  --                                   zero       → λ { (    lift refl) → {!!} }
  --                                   (suc zero) → λ { (n , lift refl) → {!!} }


module Vek where

  postulate P : {A : Set} {n : ℕ} → vek A n → Set

  t : ∀ {A} {n} (x : vek A n) → P x
  t = elim″ vekD P {!!} {!!} λ x g Pg → {!!}

  cons-inj₁  : ∀ {A n} {x y} {xs ys : vek A n}
             → vek.cons x xs ≡ vek.cons y ys → x ≡ y
  cons-inj₁ p =
    case Confusion.noConfusion vekD p of λ where
      (refl , p) → proj₁ p


module W where

  data W (A : Set) (B : A → Set) : Set where
    sup : (x : A) (f : B x → W A B) → W A B

  wHasDesc : HasDesc W
  wHasDesc = deriveDesc W

  showW : ∀ {A} ⦃ showA : Show A ⦄ {B}
        → Show (W A B)
  showW = deriveShow wHasDesc

  postulate P : {A : Set} {B : A → Set} → W A B → Set

  -- t : ∀ {A} {B} (x : W A B) → P x
  -- t = elim″ wHasDesc P λ x g Pg → {!!}
{-

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

-}
