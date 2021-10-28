{-# OPTIONS --safe --without-K #-}

open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc
open import Generics.HasDesc

module Generics.Constructions.Case
  {P I ℓ} {A : Indexed P I ℓ}
  (H : HasDesc A) (open HasDesc H)
  {p c} (Pr : Pred′ I λ i → A′ (p , i) → Set c)
  where

private
  variable
    V : ExTele P
    i : ⟦ I ⟧tel p
    v : ⟦ V ⟧tel p

Pr′ : A′ (p , i) → Set c
Pr′ {i} = unpred′ I _ Pr i


--------------------------
-- Types of motives

levelCase : ConDesc P V I → Level
levelCase (var x) = c
levelCase (π {ℓ′} _ _ C) = ℓ′ ⊔ levelCase C
levelCase (A ⊗ B) = levelIndArg A ℓ ⊔ levelCase B

MotiveCon : (C : ConDesc P V I)
          → (∀ {i} → ⟦ C ⟧Con A′ (p , v , i) → Set c)
          → Set (levelCase C)
MotiveCon (var γ) X = X refl
MotiveCon (π ia S C) X = Π< ia > (S _) λ s → MotiveCon C (X ∘ (s ,_))
MotiveCon (A ⊗ B) X = (x : ⟦ A ⟧IndArg A′ (p , _))
                    → MotiveCon B (X ∘ (x ,_))

Motives : ∀ k → Set (levelCase (lookupCon D k))
Motives k = MotiveCon (lookupCon D k) (λ x → Pr′ (constr (k , x)))


--------------------------
-- Case-analysis principle

module _ (methods : Els Motives) where

  caseData : ∀ {i} → (x : ⟦ D ⟧Data A′ (p , i)) → Pr′ (constr x)
  caseData (k , x) = caseCon (lookupCon D k) (methods k) x
    where
      caseCon
        : (C   : ConDesc P V I)
          {mk  : ∀ {i} → ⟦ C ⟧Con A′ (p , v , i) → ⟦ D ⟧Data A′ (p , i)}
          (mot : MotiveCon C λ x → Pr′ (constr (mk x)))
          (x   : ⟦ C ⟧Con A′ (p , v , i))
        → Pr′ (constr (mk x))
      caseCon (var γ) mot refl = mot
      caseCon (π ia _ C) mot (s , x) = caseCon C (app< ia > mot s) x
      caseCon (A ⊗ B) mot (a , b) = caseCon B (mot a) b

  case : (x : A′ (p , i)) → Pr′ x
  case x = subst Pr′ (constr∘split x) (caseData (split x))

deriveCase : Arrows Motives (Pred′ I (λ i → (x : A′ (p , i)) → Pr′ x))
deriveCase = curryₙ (λ m → pred′ I _ λ i → case m)
