{-# OPTIONS --safe --without-K #-}

module Generics.Telescope.Equality where

-- freely inspired by jespercockx/telescopic
-- note that our telescopes extend to the right
-- while in telescopic they extend to the left
-- a byproduct is that the following defs are overly mutual

open import Generics.Prelude
open import Generics.Telescope


private
  variable
    l     : Level
    A     : Set l
    a x y : A

_≡ⁿ_ : {T : Telescope A} → ⟦ T ⟧tel a → ⟦ T ⟧tel a → Telescope ⊤

substⁿ : {T : Telescope A} (f : ∀ {x} → ⟦ T ⟧tel x → Set l)
         {xs ys : ⟦ T ⟧tel a}
       → ⟦ xs ≡ⁿ ys ⟧tel tt
       → f xs → f ys

reflⁿ : {T : Telescope A} {xs : ⟦ T ⟧tel a}
      → ⟦ xs ≡ⁿ xs ⟧tel tt

substⁿ-refl : {T : Telescope A} (f : ∀ {x} → ⟦ T ⟧tel x → Set l)
              {xs : ⟦ T ⟧tel a} {x : f xs}
            → substⁿ f reflⁿ x ≡ x

Jⁿ : {T : Telescope A} {xs : ⟦ T ⟧tel a}
     (ϕ : ∀ ss → ⟦ xs ≡ⁿ ss ⟧tel tt → Set l)
   → ϕ xs reflⁿ
   → ∀ {ss} (es : ⟦ xs ≡ⁿ ss ⟧tel tt) → ϕ ss es

Jⁿ-refl : {T : Telescope A} {xs : ⟦ T ⟧tel a}
          (ϕ : ∀ ss → ⟦ xs ≡ⁿ ss ⟧tel tt → Set l)
          (φ : ϕ xs reflⁿ)
        → Jⁿ ϕ φ reflⁿ ≡ φ

-- TODO: discard equality between irrelevant values
_≡ⁿ_ {T = ε} tt tt = ε
_≡ⁿ_ {T = T ⊢< n , ai > f} (xs , x) (ys , y) =
  e ∶ xs ≡ⁿ ys , substⁿ (< relevance ai >_ ∘ f ∘ (_ ,_)) e x ≡ y

reflⁿ {T = ε} = tt
reflⁿ {T = T ⊢< n , ai > f} {xs , x} =
  reflⁿ , substⁿ-refl (< relevance ai >_ ∘ f ∘ (_ ,_))

Jⁿ {T = ε} ϕ φ _ = φ
Jⁿ {T = T ⊢< n , ai > f} {xs , x} ϕ φ {ss , s} (es , e) =
  J (λ y ey → ϕ (ss , y) (es , ey)) e t
  where
    d′ : ϕ (xs , substⁿ (< relevance ai >_ ∘ f ∘ (_ ,_)) reflⁿ x)
           (reflⁿ , {!!})
    d′ = {!!}

    d : ϕ (xs , substⁿ (< relevance ai >_ ∘ f ∘ (_ ,_)) reflⁿ x)
          (reflⁿ , refl)
    d = {!!}
    t : ϕ (ss , substⁿ (< relevance ai >_ ∘ f ∘ (_ ,_)) es x)
          (es , refl)
    t = Jⁿ (λ ss′ es′ → ϕ (ss′ , substⁿ (< relevance ai >_ ∘ f ∘ (_ ,_)) es′ x)
                          (es′ , refl))
           d
           es

substⁿ {T = ε} f tt z = z
substⁿ {T = T ⊢< n , ai > g} f {xs , x} {ys , y} (es , e) z =
  subst (f ∘ (ys ,_)) e $
   Jⁿ (λ rs er → f (rs , substⁿ (< relevance ai >_ ∘ g ∘ (_ ,_)) er x))
      (subst (f ∘ (xs ,_)) (sym (substⁿ-refl (< relevance ai >_ ∘ g ∘ (_ ,_)))) z)
      es


substⁿ-refl {T = ε} f = refl
substⁿ-refl {T = T ⊢< n , ai > g} f {xs , x} {z}
  rewrite Jⁿ-refl (λ rs er → f (rs , substⁿ (< relevance ai >_ ∘ g ∘ (_ ,_)) er x))
                  (subst (f ∘ (xs ,_)) (sym (substⁿ-refl (< relevance ai >_ ∘ g ∘ (_ ,_)))) z)
        = subst-subst-sym (substⁿ-refl (< relevance ai >_ ∘ g ∘ (_ ,_)))

Jⁿ-refl {T = ε} ϕ φ = refl
Jⁿ-refl {T = T ⊢< ai > f} ϕ φ = {!!}
