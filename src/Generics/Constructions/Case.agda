{-# OPTIONS --safe --without-K #-}

module Generics.Constructions.Case where

open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc
open import Generics.HasDesc


module Case {P} {I : ExTele P} {ℓ} {A : Indexed P I ℓ} (H : HasDesc {P} {I} {ℓ} A) where

  module _ {p} {c} (Pr : Pred′ I λ i → uncurry P I A (p , i) → Set c) where

    Pr′ = unpred′ I _ Pr

    open HasDesc H

    CaseMethods : Fin n → Set (levelOfTel I ⊔ ℓ ⊔ c)
    CaseMethods k = Pred′ I λ i → (x : Extend (lookupCon D k) ℓ A′ (p , tt , i))
                               → Pr′ i (constr (k , x))

    module _ (methods : Els CaseMethods) where

      case : ∀ i → (x : A′ (p , i)) → Pr′ i x
      case i x with split x | sym (constr∘split x)
      ... | k , x′ | refl = method x′
        where method : (x : Extend (lookupCon D k) ℓ A′ (p , tt , i)) → Pr′ i (constr (k , x))
              method = unpred′ I _ (methods k) i

    deriveCase : Arrows CaseMethods (Pred′ I (λ i → (x : A′ (p , i)) → Pr′ i x))
    deriveCase = curryₙ (pred′ I _ ∘ case)
