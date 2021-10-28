{-# OPTIONS --safe --without-K #-}
open import Generics.Prelude
open import Generics.Telescope
open import Generics.Desc
open import Agda.Builtin.Reflection

module Generics.Helpers
         P I
         {levelArgRel : Level → Level}
         (ArgRel      : ∀ {a} → Set a → Set (levelArgRel a))
         {levelArgIrr : Level → Level}
         (ArgIrr      : ∀ {a} → Set a → Set (levelArgIrr a))
         (Ind         : ∀ {V} (C : ConDesc P V I) → Setω)
         where


  data ConHelper p {V} : ConDesc P V I → Setω where
    instance var    : ∀ {f} → ConHelper p (var f)
             pi-irr : ∀ {ℓ n v q}
                      {S : ⟦ P , V ⟧xtel → Set ℓ}
                      (let ai = n , arg-info v (modality irrelevant q))
                      {C : ConDesc P (V ⊢< ai > S) I}
                    → ⦃ ∀ {v} → ArgIrr (S (p , v)) ⦄
                    → ⦃ ConHelper p C              ⦄
                    → ConHelper p (π ai S C)
             pi-rel : ∀ {ℓ n v q}
                      {S : ⟦ P , V ⟧xtel → Set ℓ}
                      (let ai = n , arg-info v (modality relevant q))
                      {C : ConDesc P (V ⊢< ai > S) I}
                    → ⦃ ∀ {v} → ArgRel (S (p , v)) ⦄
                    → ⦃ ConHelper p C              ⦄
                    → ConHelper p (π ai S C)
             prod   : {A B : ConDesc P V I}
                    → ⦃ Ind A         ⦄
                    → ⦃ ConHelper p B ⦄
                    → ConHelper p (A ⊗ B)


  data Helpers p : {n : ℕ} → DataDesc P I n → Setω where
    instance nil  : Helpers p []
             cons : ∀ {n} {C : ConDesc  P ε I}
                          {D : DataDesc P I n}
                  → ⦃ ConHelper p C ⦄
                  → ⦃ Helpers p D   ⦄
                  → Helpers p (C ∷ D)


  lookupHelper : ∀ {n} {D : DataDesc P I n} {p}
                 (HD : Helpers p D) (k : Fin n)
               → ConHelper p (lookupCon D k)
  lookupHelper (cons ⦃ HC ⦄ ⦃ HD ⦄) zero    = HC
  lookupHelper (cons ⦃ HC ⦄ ⦃ HD ⦄) (suc k) = lookupHelper HD k


