{-# OPTIONS --safe --without-K #-}


open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc
open import Generics.HasDesc

module Generics.Constructions.Case
  {P} {I : ExTele P} {ℓ} {A : Indexed P I ℓ} (H : HasDesc {P} {I} {ℓ} A) where

  module _ {p} {c} (Pr : Pred′ I λ i → uncurry P I A (p , i) → Set c) where

    Pr′ = unpred′ I _ Pr

    open HasDesc H

    levelE : ∀ {V} (C : ConDesc P V I ℓ) → Level
    levelE (var x) = c
    levelE (π {ℓ} p i S C) = ℓ ⊔ levelE C
    levelE (A ⊗ B) = ℓ ⊔ levelE B

    MotiveE : ∀ {V} (C : ConDesc P V I ℓ) v
            → (∀ {i} → Extend C ℓ A′ (p , v , i) → Set c)
            → Set (levelE C)
    MotiveEᵇ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia
            → (S : ⟦ P , V ⟧xtel → Set ℓ₂)
            → (C : ConDesc P (V ⊢< ia > S)  I ℓ)
            → (v : ⟦ V ⟧tel p)
            → (∀ {i} (x : Extendᵇ ℓ e ia A′ S C (p , v , i)) → Set c)
            → Set (ℓ₂ ⊔ levelE C)
    MotiveE (var γ) v X = X (lift refl)
    MotiveE (π e i S C) v X = MotiveEᵇ e i S C v X
    MotiveE (A ⊗ B) v X = (x : ⟦ A ⟧Con ℓ A′ (p , v)) → MotiveE B v λ e → X (x , e)

    MotiveEᵇ refl i S C v X = Π< i > (S (p , v)) λ s → MotiveE C (v , s) (X ∘ (s ,_))

    CaseMethods : Fin n → Set (levelOfTel I ⊔ ℓ ⊔ c)
    CaseMethods k = Pred′ I λ i → (x : Extend (lookupCon D k) ℓ A′ (p , tt , i))
                               → Pr′ i (constr (k , x))

    Motives : (k : Fin n) → Set (levelE (lookupCon D k))
    Motives k = MotiveE (lookupCon D k) tt (λ {i} x → Pr′ i (constr (k , x)))

    module _ (methods : Els Motives) where

      case : ∀ i → (x : A′ (p , i)) → Pr′ i x
      case i x with split x | sym (constr∘split x)
      ... | k , x′ | refl = method x′
        where motive : MotiveE (lookupCon D k) tt λ {i} x → Pr′ i (constr (k , x))
              motive = methods k

              bury : ∀ {V} (C : ConDesc P V I ℓ) {v}
                    (D : ∀ {i} → Extend C ℓ A′ (p , v , i)
                               → Extend (lookupCon D k) ℓ A′ (p , tt , i))
                    (M : MotiveE C v λ {i} x → Pr′ i (constr (k , D x)))
                   → (x : Extend C ℓ A′ (p , v , i))
                   → Pr′ i (constr (k , D x))
              buryᵇ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia
                      (S : ⟦ P , V ⟧xtel → Set ℓ₂)
                      (C : ConDesc P (V ⊢< ia > S) I ℓ)
                      {v}
                      (D : ∀ {i} → Extendᵇ ℓ e ia A′ S C (p , v , i)
                                 → Extend (lookupCon D k) ℓ A′ (p , tt , i))
                      (M : MotiveEᵇ e ia S C v λ {i} x → Pr′ i (constr (k , D x)))
                    → (x : Extendᵇ ℓ e ia A′ S C (p , v , i))
                    → Pr′ i (constr (k , D x))
              bury (var γ) D M (lift refl) = M
              bury (π e i S C) D M x = buryᵇ e i S C D M x
              bury (A ⊗ B) D M (a , b) = bury B (D ∘ (a ,_)) (M a) b
              buryᵇ refl i S C D M (s , x) = bury C (D ∘ (s ,_)) (app< i > M s) x

              method : (x : Extend (lookupCon D k) ℓ A′ (p , tt , i)) → Pr′ i (constr (k , x))
              method = bury (lookupCon D k) id motive

      case′ : Pred′ I λ i → (x : A′ (p , i)) → Pr′ i x
      case′ = pred′ I _ case

    deriveCase : Arrows Motives (Pred′ I (λ i → (x : A′ (p , i)) → Pr′ i x))
    deriveCase = curryₙ case′

