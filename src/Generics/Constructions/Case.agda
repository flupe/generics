{-# OPTIONS --safe --without-K #-}

open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc
open import Generics.HasDesc

module Generics.Constructions.Case
  {P} {I : ExTele P} {ℓ} {A : Indexed P I ℓ} (H : HasDesc {P} {I} {ℓ} A) where

  open HasDesc H

  module _ {p} {c} (Pr : Pred′ I λ i → A′ (p , i) → Set c) where

    Pr′ = unpred′ I _ Pr

    levelCon : ∀ {V} (C : ConDesc P V I ℓ) → Level
    levelCon (var x) = c
    levelCon (π {ℓ} _ _ _ C) = ℓ ⊔ levelCon C
    levelCon (A ⊗ B) = ℓ ⊔ levelCon B


    MotiveCon : ∀ {V} (C : ConDesc P V I ℓ) v
            → (∀ {i} → ⟦ C ⟧Con ℓ A′ (p , v , i) → Set c)
            → Set (levelCon C)

    MotiveConᵇ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia
            → (S : ⟦ P , V ⟧xtel → Set ℓ₂)
            → (C : ConDesc P (V ⊢< ia > S)  I ℓ)
            → (v : ⟦ V ⟧tel p)
            → (∀ {i} (x : Conᵇ ℓ e ia A′ S C (p , v , i)) → Set c)
            → Set (ℓ₂ ⊔ levelCon C)

    MotiveCon (var γ) v X = X (lift refl)
    MotiveCon (π e i S C) v X = MotiveConᵇ e i S C v X
    MotiveCon (A ⊗ B) v X = (x : ⟦ A ⟧IndArg ℓ A′ (p , v)) → MotiveCon B v λ e → X (x , e)

    MotiveConᵇ refl i S C v X = Π< i > (S (p , v)) λ s → MotiveCon C (v , s) (X ∘ (s ,_))


    CaseMethods : Fin n → Set (levelOfTel I ⊔ ℓ ⊔ c)
    CaseMethods k = Pred′ I λ i
                  → (x : ⟦ lookupCon D k ⟧Con ℓ A′ (p , tt , i))
                  → Pr′ i (constr (k , x))

    Motives : (k : Fin n) → Set (levelCon (lookupCon D k))
    Motives k = MotiveCon (lookupCon D k) tt (λ {i} x → Pr′ i (constr (k , x)))

    module _ (methods : Els Motives) where

      case : ∀ i → (x : A′ (p , i)) → Pr′ i x
      case i x with split x | sym (constr∘split x)
      ... | k , x′ | refl = method x′
        where motive : MotiveCon (lookupCon D k) tt λ {i} x → Pr′ i (constr (k , x))
              motive = methods k

              bury : ∀ {V} (C : ConDesc P V I ℓ) {v}
                    (D : ∀ {i} → ⟦_⟧Con C ℓ A′ (p , v , i)
                               → ⟦_⟧Con (lookupCon D k) ℓ A′ (p , tt , i))
                    (M : MotiveCon C v λ {i} x → Pr′ i (constr (k , D x)))
                   → (x : ⟦_⟧Con C ℓ A′ (p , v , i))
                   → Pr′ i (constr (k , D x))
              buryᵇ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia
                      (S : ⟦ P , V ⟧xtel → Set ℓ₂)
                      (C : ConDesc P (V ⊢< ia > S) I ℓ)
                      {v}
                      (D : ∀ {i} → Conᵇ ℓ e ia A′ S C (p , v , i)
                                 → ⟦_⟧Con (lookupCon D k) ℓ A′ (p , tt , i))
                      (M : MotiveConᵇ e ia S C v λ {i} x → Pr′ i (constr (k , D x)))
                    → (x : Conᵇ ℓ e ia A′ S C (p , v , i))
                    → Pr′ i (constr (k , D x))
              bury (var γ) D M (lift refl) = M
              bury (π e i S C) D M x = buryᵇ e i S C D M x
              bury (A ⊗ B) D M (a , b) = bury B (D ∘ (a ,_)) (M a) b
              buryᵇ refl i S C D M (s , x) = bury C (D ∘ (s ,_)) (app< i > M s) x

              method : (x : ⟦_⟧Con (lookupCon D k) ℓ A′ (p , tt , i)) → Pr′ i (constr (k , x))
              method = bury (lookupCon D k) id motive

      case′ : Pred′ I λ i → (x : A′ (p , i)) → Pr′ i x
      case′ = pred′ I _ case

    deriveCase : Arrows Motives (Pred′ I (λ i → (x : A′ (p , i)) → Pr′ i x))
    deriveCase = curryₙ case′
