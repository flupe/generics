{-# OPTIONS --safe --without-K #-}

module Generics.HasDesc where

open import Data.String.Base
open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc


record HasDesc {P} {I : ExTele P} {ℓ} (A : Indexed P I ℓ) : Setω where
  A′ : Σ[ P ⇒ I ] → Set ℓ
  A′ = uncurry P I A
  
  field
    {n} : ℕ
    D   : DataDesc P I ℓ n

    names : Vec String n

    to   : ∀ {pi : Σ[ P ⇒ I ]} → A′ pi → μ D pi
    from : ∀ {pi : Σ[ P ⇒ I ]} → μ D pi → A′ pi

    from∘to : ∀ {pi} (x : A′ pi ) → from (to x) ≡ x
    to∘from : ∀ {pi} (x : μ D pi) → to (from x) ≡ x

    constr  : ∀ {pi} → ⟦ D ⟧Data ℓ A′ pi → A′ pi
    split   : ∀ {pi} → A′ pi → ⟦ D ⟧Data ℓ A′ pi

    -- | constr and split are coherent with from
    constr-coh  : ∀ {pi} (x : ⟦ D ⟧Data _ (μ D) pi)
                → constr (mapData _ _ from D x) ≡ from ⟨ x ⟩

    split-coh   : ∀ {pi} (x : ⟦ D ⟧Data _ (μ D) pi)
                → split (from ⟨ x ⟩) ≡ mapData _ _ from D x

  -- because they are coherent, we can show that they are in fact inverse of one another
  constr∘split : ∀ {pi} (x : A′ pi) → constr (split x) ≡ x
  constr∘split x rewrite sym (from∘to x) with to x
  ... | ⟨ x′ ⟩ rewrite split-coh x′ = constr-coh x′

  split∘constr : ∀ (funext : ∀ {a b} {A : Set a} {B : A → Set b} {f g : ∀ x → B x}
                           → (∀ x → f x ≡ g x) → f ≡ g)
                 {pi} (x : ⟦ D ⟧Data ℓ A′ pi) → split (constr x) ≡ x
  split∘constr funext x = begin
    split (constr x)
      ≡˘⟨ cong (split ∘ constr) (mapData-id funext from∘to {D = D} x) ⟩
    split (constr (mapData ℓ ℓ (from ∘ to) D x))
      ≡⟨ cong (split ∘ constr) (mapData-compose funext {f = to} {g = from} {D = D} x) ⟩
    split (constr (mapData _ ℓ from D (mapData ℓ _ to D x)))
      ≡⟨ cong split (constr-coh _) ⟩
    split (from ⟨ mapData ℓ _ to D x ⟩)
      ≡⟨ split-coh _ ⟩
    mapData _ _ from D (mapData _ _ to D x)
      ≡˘⟨ mapData-compose funext {f = to} {g = from} {D = D} x ⟩
    mapData _ _ (from ∘ to) D x
      ≡⟨ mapData-id funext from∘to {D = D} x ⟩
    x ∎
    where open ≡-Reasoning

  split-injective : ∀ {pi} {x y : A′ pi} → split x ≡ split y → x ≡ y
  split-injective {x = x} {y} sx≡sy = begin
    x                ≡˘⟨ constr∘split x ⟩
    constr (split x) ≡⟨ cong constr sx≡sy ⟩
    constr (split y) ≡⟨ constr∘split y ⟩
    y                ∎
    where open ≡-Reasoning
