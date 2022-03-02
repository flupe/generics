{-# OPTIONS --safe --without-K #-}

module Generics.HasDesc where

open import Data.String.Base

open import Generics.Prelude hiding (lookup ; pi)
open import Generics.Telescope
open import Generics.Desc

import Generics.Accessibility as Accessibility


private
  variable
    P  : Telescope ⊤
    I  : ExTele P
    pi : ⟦ P , I ⟧xtel


record HasDesc {ℓ} (A : Indexed P I ℓ) : Setω where
  A′ : ⟦ P , I ⟧xtel → Set ℓ
  A′ = uncurry P I A

  field
    {n} : ℕ
    D   : DataDesc P I n

    names : Vec String n

    constr : ⟦ D ⟧Data A′ pi → A′ pi
    split  : A′ pi → ⟦ D ⟧Data A′ pi

    constr∘split : (x : A′ pi          ) → constr (split x) ≡  x
    split∘constr : (x : ⟦ D ⟧Data A′ pi) → split (constr x) ≡ω x

  open Accessibility A D split public

  field wf : (x : A′ pi) → Acc x


  split-injective : ∀ {pi} {x y : A′ pi} → split x ≡ω split y → x ≡ y
  split-injective {x = x} {y} sx≡sy = begin
    x                ≡⟨ sym (constr∘split x) ⟩
    constr (split x) ≡⟨ congω constr sx≡sy   ⟩
    constr (split y) ≡⟨ constr∘split y       ⟩
    y                ∎ where open ≡-Reasoning

  -- TODO: ≡ω-Reasoning
  constr-injective : ∀ {pi} {x y : ⟦ D ⟧Data A′ pi} → constr x ≡ constr y → x ≡ω y
  constr-injective {x = x} {y} cx≡cy =
    transω (symω (split∘constr x)) (transω (cong≡ω split cx≡cy) (split∘constr y))
