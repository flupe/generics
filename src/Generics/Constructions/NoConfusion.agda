{-# OPTIONS --safe #-}

open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc
open import Generics.HasDesc

open import Relation.Nullary.Decidable as Decidable
open import Data.Empty
open import Relation.Nullary
import Data.Fin as Fin

module Generics.Constructions.NoConfusion
  {P I ℓ} {A : Indexed P I ℓ}
  (H : HasDesc A) (open HasDesc H)
  {p}
  where

private
  variable
    V : ExTele P
    i : ⟦ I ⟧tel p
    v : ⟦ V ⟧tel p


--------------------------
-- NoConfusion


levelNoConfusionCon : (C : ConDesc P V I) → Level
levelNoConfusionCon (var x) = lzero
levelNoConfusionCon (π {ℓ} ai S C) = ℓ ⊔ levelNoConfusionCon C 
levelNoConfusionCon (A ⊗ B) = levelIndArg A ℓ ⊔ levelNoConfusionCon B

NoConfusionCon : (C : ConDesc P V I) (x y : ⟦ C ⟧Con A′ (p , v , i)) → Set (levelNoConfusionCon C)
NoConfusionCon (var _) _ _ = ⊤
NoConfusionCon (π ai S C) (x₁ , x₂) (y₁ , y₂) =
  Σ[ e ∈ x₁ ≡ y₁ ] NoConfusionCon C (subst (λ s → ⟦ C ⟧Con A′ (p , (_ , s) , _)) e x₂) y₂
NoConfusionCon (A ⊗ B) (x₁ , x₂) (y₁ , y₂) = x₁ ≡ y₁ × NoConfusionCon B x₂ y₂

levelNoConfusionData : (x y : ⟦ D ⟧Data A′ (p , i)) → Level
levelNoConfusionData (k₁ , x) (k₂ , y) with k₁ Fin.≟ k₂
... | yes refl  = levelNoConfusionCon (lookupCon D k₁)
... | no k₁≢k₂ = lzero

NoConfusionData : (x y : ⟦ D ⟧Data A′ (p , i)) → Set (levelNoConfusionData x y) 
NoConfusionData (k₁ , x) (k₂ , y) with k₁ Fin.≟ k₂
... | yes refl  = NoConfusionCon _ x y
... | no k₁≢k₂ = ⊥

NoConfusion : (x y : A′ (p , i)) → Set (levelNoConfusionData (split x) (split y))
NoConfusion x y = NoConfusionData (split x) (split y)

noConfCon-refl : (C : ConDesc P V I) (x : ⟦ C ⟧Con A′ (p , v , i)) → NoConfusionCon C x x
noConfCon-refl (var _) x = tt
noConfCon-refl (π ai S C) (s , x) = refl , noConfCon-refl C x
noConfCon-refl (A ⊗ B)    (x , y) = refl , noConfCon-refl B y

noConfData-refl : (x : ⟦ D ⟧Data A′ (p , i)) → NoConfusionData x x
noConfData-refl (k , x) with k Fin.≟ k
... | yes refl = noConfCon-refl (lookupCon D k) x
... | no k≢k  = k≢k refl

noConf-refl : (x : A′ (p , i)) → NoConfusion x x
noConf-refl x = noConfData-refl (split x)

noConf : {x y : A′ (p , i)} → x ≡ y → NoConfusion x y
noConf refl = noConf-refl _

noConfCon′ : (C : ConDesc P V I) {x y : ⟦ C ⟧Con A′ (p , v , i)} → NoConfusionCon C x y → x ≡ y
noConfCon′ (var x) {x = refl} {y = refl} nc = refl
noConfCon′ (π ai S C) (refl , nc) = cong (_ ,_) (noConfCon′ C nc)
noConfCon′ (A ⊗ B) (refl , nc) = cong (_ ,_) (noConfCon′ B nc)

noConfData′ : {x y : ⟦ D ⟧Data A′ (p , i)} → NoConfusionData x y → x ≡ω y
noConfData′ {x = k₁ , x} {k₂ , y} nc with k₁ Fin.≟ k₂
noConfData′ nc | yes refl = cong≡ω _ (noConfCon′ _ nc)
noConfData′ () | no k₁≢k₂

noConf′ : {x y : A′ (p , i)} → NoConfusion x y → x ≡ y
noConf′ nc = split-injective (noConfData′ nc)
