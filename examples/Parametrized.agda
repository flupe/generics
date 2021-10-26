{-# OPTIONS --allow-unsolved-metas #-}
open import Generics.Prelude hiding (lookup)
open import Generics.HasDesc
open import Generics.Desc
open import Generics.Telescope
open import Generics.Reflection

open import Generics.Constructions.Show as Show hiding (show)
open import Generics.Constructions.Case
open import Generics.Constructions.Elim
open import Generics.Constructions.NoConfusion
open import Generics.Constructions.DecEq
open import Generics.Helpers

open import Data.String hiding (show)
open import Data.Maybe.Base

module Parametrized where

open Show.Show ⦃...⦄

module _ (A : Set) (B : A → Set) where

  data W : Set where
    node : ∀ x → (B x → W) → W

  D : DataDesc ε ε lzero 1
  D = π refl (ai visible relevant quantity-ω)
        (const A) (π refl (ai visible relevant quantity-ω) (λ (_ , (_ , x)) → B x) (var (const tt))
      ⊗ var (const tt))
    ∷ []

  to : W → μ D (tt , tt)
  to (node x f) = ⟨ zero , x , to ∘ f , lift refl ⟩

  from : μ D (tt , tt) → W
  from ⟨ zero , x , f , lift refl ⟩ = node x (from ∘ f)

  from∘to : ∀ x → from (to x) ≡ x
  from∘to (node x f) = {!!}

{-
-- natD : HasDesc ℕ
-- natD = deriveDesc ℕ
-- 
-- open HasDesc natD

to′ : ℕ → μ D (tt , tt)
to′ zero = ⟨ zero , lift refl ⟩
to′ (suc n) = ⟨ suc zero , to′ n , lift refl ⟩

from′ : μ D (tt , tt) → ℕ
from′ ⟨ zero , lift refl ⟩ = 0
from′ ⟨ suc zero , n , lift refl ⟩ = suc (from′ n)

from′∘to′ : ∀ n → from′ (to′ n) ≡ n
from′∘to′ zero = refl
from′∘to′ (suc n) =
  case from′∘to′ n of
    λ where p → {!!}
-}

{-

instance
  showℕ : Show ℕ
  showℕ = deriveShow natD

  decℕ : DecEq ℕ
  decℕ = deriveDecEq natD

  
caseℕ : ∀ {l} (P : ℕ → Set l)
      → P 0
      → (∀ n → P (suc n))
      → ∀ n → P n
caseℕ = deriveCase natD

data vek (A : Set) : ℕ → Set where
  nil  : vek A 0
  cons : ∀ {n} → A → vek A n → vek A (suc n)

vekD : HasDesc vek
vekD = deriveDesc vek

instance
  showVek : ∀ {A} → ⦃ Show A ⦄ → ∀ {n} → Show (vek A n)
  showVek = deriveShow vekD

  decVek : {A : Set} → ⦃ DecEq A ⦄ → ∀ {n} → DecEq (vek A n)
  decVek = deriveDecEq vekD

elimVek : ∀ {A} {ℓ} (P : ∀ {n} → vek A n → Set ℓ)
        → P nil
        → (∀ {n} x (xs : vek A n) → P xs → P (cons x xs))
        → ∀ {n} (x : vek A n) → P x
elimVek = deriveElim vekD

caseVek : ∀ {A} {ℓ} (P : ∀ {n} → vek A n → Set ℓ)
        → P nil
        → (∀ {n} x xs → P (cons x xs))
        → ∀ {n} (x : vek A n) → P x
caseVek = deriveCase vekD


data S : Set where
  ok : (ℕ → S) → S

sD : HasDesc S
sD = deriveDesc S

elimS : (P : S → Set)
      → ((g : ℕ → S) → (∀ x → P (g x)) → P (ok g))
      → ∀ x → P x
elimS = deriveElim sD

-- No instance of type OnlyFO ... GOOD!
-- decS : DecEq S
-- decS = deriveDecEq sD

module Nat where
  suc-inj  : ∀ {a b} → ℕ.suc a ≡ ℕ.suc b → a ≡ b
  suc-inj = proj₁ ∘ Confusion.noConfusion natD
  
  suc-cong : ∀ {a b} → a ≡ b → ℕ.suc a ≡ ℕ.suc b
  suc-cong = Confusion.noConfusion₂ natD ∘ (_, lift tt)

module Vek where

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

  elimW : ∀ {A} {B : A → Set} (P : W A B → Set)
        → (∀ x (f : B x → W A B) → (∀ y → P (f y)) → P (sup x f))
        → ∀ x → P x
  elimW = deriveElim wHasDesc
  
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

-}
