{-# OPTIONS --safe #-}

open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc
open import Generics.HasDesc

module Generics.Constructions.Case
  {P I ℓ} {A : Indexed P I ℓ}
  (H : HasDesc A) (open HasDesc H)
  {p} {c} (Pr : Pred′ I λ i → A′ (p , i) → Set c)
  where

private
  variable
    V : ExTele P
    i : ⟦ I ⟧tel p
    v : ⟦ V ⟧tel p

Pr′ : uncurry′ I _ (uncurry′ P _ A p) i → Set c
Pr′ {i} = unpred′ I _ Pr i

--------------------------
-- Types of motives

levelCon : ConDesc P V I ℓ → Level
levelCon (var x) = c
levelCon (π {ℓ} _ _ _ C) = ℓ ⊔ levelCon C
levelCon (A ⊗ B) = ℓ ⊔ levelCon B

MotiveCon : (C : ConDesc P V I ℓ)
          → (∀ {i} → ⟦ C ⟧Con ℓ A′ (p , v , i) → Set c)
          → Set (levelCon C)
MotiveConᵇ : ∀ {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia
             (S : ⟦ P , V ⟧xtel → Set ℓ₂)
             (C : ConDesc P (V ⊢< ia > S)  I ℓ)
           → (∀ {i} (x : Conᵇ ℓ e ia A′ S C (p , v , i)) → Set c)
           → Set (ℓ₂ ⊔ levelCon C)
MotiveCon (var γ) X = X (lift refl)
MotiveCon (π e i S C) X = MotiveConᵇ e i S C X
MotiveCon (A ⊗ B) X = (x : ⟦ A ⟧IndArg ℓ A′ (p , _))
                    → MotiveCon B (X ∘ (x ,_))
MotiveConᵇ refl i S C X
  = Π< i > (S (p , _)) λ s → MotiveCon C (X ∘ (s ,_))

Motives : (k : Fin n) → Set (levelCon (lookupCon D k))
Motives k = MotiveCon (lookupCon D k) (λ x → Pr′ (constr (k , x)))

--------------------------
-- Case-analysis principle

module _ (methods : Els Motives) where

  caseData : ∀ {i} → (x : ⟦ D ⟧Data ℓ A′ (p , i)) → Pr′ (constr x)
  caseData (k , x) = caseCon (lookupCon D k) (methods k) x
    where
      caseCon
        : (C   : ConDesc P V I ℓ)
          {mk  : ∀ {i} → ⟦ C ⟧Con ℓ A′ (p , v , i) → ⟦ D ⟧Data ℓ A′ (p , i)}
          (mot : MotiveCon C (Pr′ ∘ constr ∘ mk))
          (x   : ⟦ C ⟧Con ℓ A′ (p , v , i))
        → Pr′ (constr (mk x))
      caseConᵇ
        : ∀ {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) {ia}
          {S   : ⟦ P , V ⟧xtel → Set ℓ₂}
          (C   : ConDesc P (V ⊢< ia > S) I ℓ)
          {mk  : ∀ {i} → Conᵇ ℓ e ia A′ S C (p , v , i) → ⟦ D ⟧Data ℓ A′ (p , i)}
          (mot : MotiveConᵇ e ia S C (Pr′ ∘ constr ∘ mk))
          (x   : Conᵇ ℓ e ia A′ S C (p , v , i))
        → Pr′ (constr (mk x))
      caseCon (var γ) mot (lift refl) = mot
      caseCon (π e _ _ C) mot x = caseConᵇ e C mot x
      caseCon (A ⊗ B) mot (a , b) = caseCon B (mot a) b
      caseConᵇ refl C mot (s , x) = caseCon C (app< _ > mot s) x

  case : (x : A′ (p , i)) → Pr′ x
  case x = subst Pr′ (constr∘split x) (caseData (split x))

deriveCase : Arrows Motives (Pred′ I (λ i → (x : A′ (p , i)) → Pr′ x))
deriveCase = curryₙ (λ m → pred′ I _ λ i → case m)
