module Generics.Simple.Constructions.NoConfusion where

open import Agda.Primitive
open import Generics.Simple.Desc
open import Generics.Simple.HasDesc2
open import Data.Unit.Polymorphic
open import Data.Empty.Polymorphic
open import Data.Fin.Base hiding (lift)
open import Data.Fin.Properties as Fin
open import Data.Product
open import Level
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Bool
open import Function.Base

module SoIAmConfusion
  {a b n} {I : Set a} (D : Desc I b n)
  (X : I → Set (a ⊔ b)) where

  -- | Relation between two interpretations of the same constructor
  NoConfusionCon : ∀ {C : ConDesc I b} {i} (x y : ⟦ C ⟧C X i) → Set (a ⊔ b)
  NoConfusionCon {κ _  } (lift refl) (lift refl) = ⊤
  NoConfusionCon {ι i f} (x , dx) (y , dy) = x ≡ y × NoConfusionCon dx dy
  NoConfusionCon {σ _ _} (x , dx) (y , dy) = Σ (x ≡ y) λ { refl → NoConfusionCon dx dy }

  NoConfusion : ∀ {i} (x y : ⟦ D ⟧D X i) → Set (a ⊔ b)
  NoConfusion (kx , x) (ky , y) with kx Fin.≟ ky
  ... | yes refl = NoConfusionCon x y
  ... | no kx≢ky = ⊥

  noConfRefl : ∀ {C : ConDesc I b} {i} (x : ⟦ C ⟧C X i) → NoConfusionCon x x
  noConfRefl {κ γ  } (lift refl) = tt
  noConfRefl {ι γ C} (x , d) = refl , noConfRefl d
  noConfRefl {σ S C} (s , d) = refl , noConfRefl d

  noConf : ∀ {i} {x y : ⟦ D ⟧D X i} → x ≡ y → NoConfusion x y
  noConf {x = kx , x} {ky , y} refl with kx Fin.≟ ky
  ... | yes refl = noConfRefl x
  ... | no kx≢ky = lift (kx≢ky refl)

  noConfCon : ∀ {C : ConDesc I b} {i} {x y : ⟦ C ⟧C X i} → NoConfusionCon x y → x ≡ y
  noConfCon {κ γ  } {x = lift refl} {lift refl} nc = refl
  noConfCon {ι γ C} (refl , nc) = cong _ (noConfCon nc)
  noConfCon {σ S C} (refl , nc) = cong _ (noConfCon nc)

  noConf₂ : ∀ {i} {x y : ⟦ D ⟧D X i} → NoConfusion x y → x ≡ y
  noConf₂ {x = kx , x} {ky , y} with kx Fin.≟ ky
  ... | yes refl = cong (kx ,_) ∘ noConfCon
  ... | no kx≢ky = λ ()


module NoConfusion {a b} {I : Set a} {A : I → Set (a ⊔ b)} ⦃ H : HasDesc {b = b} A ⦄ where
  open HasDesc H

  module C = SoIAmConfusion D A

  NoConfusion : ∀ {i} (x y : A i) → Set (a ⊔ b)
  NoConfusion x y = C.NoConfusion (dissect x) (dissect y)

  noConf : ∀ {i} {x y : A i} → x ≡ y → NoConfusion x y
  noConf {x = x} {y} = C.noConf ∘ cong dissect

  noConf₂ : ∀ {i} {x y : A i} → NoConfusion x y → x ≡ y
  noConf₂ {x = x} {y} = aux ∘ C.noConf₂
    where
      aux : dissect x ≡ dissect y → x ≡ y
      aux p = begin
        x                  ≡⟨ sym (constr∘dissect x) ⟩
        constr (dissect x) ≡⟨ cong constr p ⟩
        constr (dissect y) ≡⟨ constr∘dissect y ⟩
        y                  ∎
        where open ≡-Reasoning

open NoConfusion
