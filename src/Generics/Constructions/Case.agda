{-# OPTIONS --safe --without-K #-}

module Generics.Constructions.Case where

open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc
open import Generics.HasDesc


module Case {P} {I : ExTele P} {ℓ} (A : Indexed P I ℓ) (H : HasDesc {P} {I} {ℓ} A)
            {c} (Pr : ∀ {pi} → uncurry P I A pi → Set c) where

      open HasDesc H

      con-method : Fin n → Set (levelOfTel P ⊔ levelOfTel I ⊔ ℓ ⊔ c)
      con-method k = ∀ {pi} (x : Extend (lookupCon D k)  ℓ A′ pi) → Pr (constr (k , x))

      case-methods : Sets _
      case-methods = con-method

      case : Els case-methods → ∀ {pi} (x : A′ pi) → Pr x
      case methods x with split x | sym (constr∘split x)
      ... | k , x′ | refl = method x′
        where method : ∀ {pi} (x : Extend (lookupCon D k) ℓ A′ pi) → Pr (constr (k , x))
              method = methods k
