{-# OPTIONS --safe --without-K #-}

module Generics.Parametrized.Constructions.Case where

open import Generics.Prelude hiding (lookup)
open import Generics.Parametrized.Telescope
open import Generics.Parametrized.Desc3
open import Generics.Parametrized.HasDesc


module Case {P} {I : ExTele P} {ℓ} (A : Curried′ P I ℓ) (H : HasDesc {P} {I} {ℓ} A)
            {c} (Pr : ∀ {pi} → uncurry′ P I A pi → Set c) where

      open HasDesc H

      con-method : Fin n → Set (levelTel P ⊔ levelTel I ⊔ ℓ ⊔ c)
      con-method k = ∀ {pi} (x : Extend (lookup D k)  ℓ A′ pi) → Pr (constr (k , x))

      case-methods : Vec (Set (levelTel P ⊔ levelTel I ⊔ ℓ ⊔ c)) n
      case-methods = tabulate con-method

      case : Members case-methods → ∀ {pi} (x : A′ pi) → Pr x
      case methods x with split x | sym (constr∘split x)
      ... | k , x′ | refl = subst id (lookupTabulate con-method k) (lookupMember methods k) x′
