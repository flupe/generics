{-# OPTIONS --safe #-}
module Elim where

open import Generics.Prelude
open import Generics.Telescope
open import Generics.Desc
open import Generics.HasDesc
open import Generics.Constructions.Elim
import Generics.Accessibility as Accessibility

natD : HasDesc {ε} {ε} {lzero} ℕ
natD = record { NatHasDesc } where
  module NatHasDesc where
    n = 2
    D = (var _) ∷ (var _ ⊗ var _) ∷ []

    names = "zero" ∷ "suc" ∷ []


    constr : ⟦ D ⟧Data lzero (λ _ → ℕ) _ → ℕ
    constr (zero     ,     _) = zero
    constr (suc zero , n , _) = suc n

    split : ℕ → ⟦ D ⟧Data lzero (λ _ → ℕ) _
    split zero    = zero           , (lift refl)
    split (suc n) = (suc zero) , n , (lift refl)

    open Accessibility _ _ _

    split∘constr : (x : ⟦ D ⟧Data _ (const ℕ) (tt , tt)) → split (constr x) ≡ x
    constr∘split : (x : ℕ) → constr (split x) ≡ x

    split∘constr (zero , lift refl) = refl
    split∘constr (suc zero , x , lift refl) = refl

    constr∘split zero = refl
    constr∘split (suc x) = refl

    wf : ∀ x → Acc x
    wf zero = acc (lift tt)
    wf (suc x) = acc (lift (wf x) , lift tt)

elimℕ : ∀ {c} (P : ℕ → Set c)
      → P 0
      → (∀ n → P n → P (suc n))
      → ∀ n → P n
elimℕ = deriveElim natD

elim0 : ∀ {c} (P : ℕ → Set c)
        (P0 : P 0)
        (PS : ∀ n → P n → P (suc n))
      → elimℕ P P0 PS 0 ≡ P0
elim0 P P0 PS = refl

elimS : ∀ {c} (P : ℕ → Set c)
        (P0 : P 0)
        (PS : ∀ n → P n → P (suc n))
      → ∀ n → elimℕ P P0 PS (suc n) ≡ PS n (elimℕ P P0 PS n)
elimS P P0 PS n = refl
