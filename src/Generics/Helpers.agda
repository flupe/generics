open import Generics.Prelude
open import Generics.Telescope
open import Generics.Desc
open import Agda.Builtin.Reflection

module Generics.Helpers
         P I ℓ
         {levelArgRel : Level → Level}
         (ArgRel      : ∀ {a} → Set a → Set (levelArgRel a))
         {levelArgIrr : Level → Level}
         (ArgIrr      : ∀ {a} → Set a → Set (levelArgIrr a))
         {levelInd    : ∀ {V} → ConDesc P V I ℓ → Level}
         (Ind         : ∀ {V} (C : ConDesc P V I ℓ) → Set (levelInd C))
         where


  data ConHelper p {V} : ConDesc P V I ℓ → Setω where
    instance var    : ∀ {f} → ConHelper p (var f)
             pi-irr : ∀ {ℓ′ v q} {e : ℓ′ ≤ℓ ℓ}
                      {S : ⟦ P , V ⟧xtel → Set ℓ′}
                      {C : ConDesc P (V ⊢< ai v irrelevant q > S) I ℓ}
                    → ⦃ ∀ {v} → ArgIrr (S (p , v)) ⦄
                    → ⦃ ConHelper p C              ⦄
                    → ConHelper p (π e (ai v irrelevant q) S C)
             pi-rel : ∀ {ℓ′ v q} {e : ℓ′ ≤ℓ ℓ}
                      {S : ⟦ P , V ⟧xtel → Set ℓ′}
                      {C : ConDesc P (V ⊢< ai v relevant q > S) I ℓ}
                    → ⦃ ∀ {v} → ArgRel (S (p , v)) ⦄
                    → ⦃ ConHelper p C              ⦄
                    → ConHelper p (π e (ai v relevant q) S C)
             prod   : {A B : ConDesc P V I ℓ}
                    → ⦃ Ind A       ⦄
                    → ⦃ ConHelper p B ⦄
                    → ConHelper p (A ⊗ B)


  data Helpers p : {n : ℕ} → DataDesc P I ℓ n → Setω where
    instance nil  : Helpers p []
             cons : ∀ {n} {C : ConDesc  P ε I ℓ}
                          {D : DataDesc P I ℓ n}
                  → ⦃ ConHelper p C ⦄
                  → ⦃ Helpers p D   ⦄
                  → Helpers p (C ∷ D)


  lookupHelper : ∀ {n} {D : DataDesc P I ℓ n} {p}
                 (HD : Helpers p D) (k : Fin n)
               → ConHelper p (lookupCon D k)
  lookupHelper (cons ⦃ HC ⦄ ⦃ HD ⦄) zero    = HC
  lookupHelper (cons ⦃ HC ⦄ ⦃ HD ⦄) (suc k) = lookupHelper HD k


