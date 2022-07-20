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

-----------
-- Helpers

private
  J : ∀ {a b} {A : Set a} {x : A} (B : ∀ y → x ≡ y → Set b)
      {y : A} (p : x ≡ y) → B x refl → B y p
  J B refl b = b

  J⁻¹ : ∀ {a b} {A : Set a} {x : A} (B : ∀ y → x ≡ y → Set b)
      → {y : A} (p : x ≡ y) → B y p → B x refl
  J⁻¹ B p = J (λ y e → B y e → B _ refl) p id

  Jω : ∀ {a} {A : Set a} {x : A} (B : (y : A) → x ≡ y → Setω)
     → {y : A} (p : x ≡ y) → B x refl → B y p
  Jω B refl x = x

  Jω⁻¹ : ∀ {a} {A : Set a} {x : A} (B : (y : A) → x ≡ y → Setω)
      → {y : A} (p : x ≡ y) → B y p → B x refl
  Jω⁻¹ B p = Jω (λ y e → B y e → B _ refl) p λ x → x
  
  JJ⁻¹ : ∀ {a b} {A : Set a} {x : A} (B : (y : A) → x ≡ y → Set b)
      → {y : A} {p : x ≡ y}
      → (z : B y p)
      → J B p (J⁻¹ B p z) ≡ z
  JJ⁻¹ B {p = refl} z = refl

  JJω⁻¹ : ∀ {a} {A : Set a} {x : A} (B : (y : A) → x ≡ y → Setω)
      → {y : A} {p : x ≡ y}
      → (z : B y p)
      → Jω B p (Jω⁻¹ B p z) ≡ω z
  JJω⁻¹ B {p = refl} z = refl

  substω : ∀ {a} {A : Set a} (P : A → Setω) {x y : A}
         → x ≡ y → P x → P y
  substω P refl x = x

  substω-substω-sym : ∀ {a} {A : Set a} {P : A → Setω}
                      {x y : A} (x≡y : x ≡ y)
                      {p : P y}
                    → substω P x≡y (substω P (sym x≡y) p) ≡ω p
  substω-substω-sym refl = reflω
         

----------------------
-- Telescope Equality

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
   → ∀ {ss} (es : ⟦ xs ≡ⁿ ss ⟧tel tt)
   → ϕ xs reflⁿ
   → ϕ ss es

Jⁿ-refl : {T : Telescope A} {xs : ⟦ T ⟧tel a}
          (ϕ : ∀ ss → ⟦ xs ≡ⁿ ss ⟧tel tt → Set l)
          (φ : ϕ xs reflⁿ)
        → Jⁿ ϕ reflⁿ φ ≡ φ

-- TODO: discard equality between irrelevant values
_≡ⁿ_ {T = ε} tt tt = ε
_≡ⁿ_ {T = T ⊢< n , ai > f} (xs , x) (ys , y) =
  e ∶ xs ≡ⁿ ys , substⁿ (< relevance ai >_ ∘ f ∘ (_ ,_)) e x ≡ y

reflⁿ {T = ε} = tt
reflⁿ {T = T ⊢< n , ai > f} {xs , x} =
  reflⁿ , substⁿ-refl (< relevance ai >_ ∘ f ∘ (_ ,_))

Jⁿ {T = ε} ϕ _ φ = φ
Jⁿ {T = T ⊢< n , ai > f} {xs , x} ϕ {ss , s} (es , e) φ =
  J (λ y ey → ϕ (ss , y) (es , ey)) e $
     Jⁿ (λ ss′ es′ → ϕ (ss′ , substⁿ (< relevance ai >_ ∘ f ∘ (_ ,_)) es′ x)
                       (es′ , refl)) es d
  where
    d : ϕ (xs , substⁿ (< relevance ai >_ ∘ f ∘ (_ ,_)) reflⁿ x)
          (reflⁿ , refl)
    d = J⁻¹ (λ y ey → ϕ (xs , y) (reflⁿ , ey)) (substⁿ-refl _) φ

substⁿ f pₜ x = Jⁿ (λ ss _ → f ss) pₜ x
substⁿ-refl f {x = x} = Jⁿ-refl (λ ss _ → f ss) x

Jⁿ-refl {T = ε} ϕ φ = refl
Jⁿ-refl {T = T ⊢< n , ai > f} {xs , x} ϕ φ
  rewrite Jⁿ-refl (λ ss′ es′ → ϕ (ss′ , substⁿ (< relevance ai >_ ∘ f ∘ (_ ,_)) es′ x) (es′ , refl))
                  (J⁻¹ (λ y ey → ϕ (xs , y) (reflⁿ , ey)) _ φ)
        = JJ⁻¹ (λ y ey → ϕ (xs , y) (reflⁿ , ey)) φ

------------------------------
-- Telescope Equality in Setω

substωⁿ : {T : Telescope A} (f : ∀ {x} → ⟦ T ⟧tel x → Setω)
          {xs ys : ⟦ T ⟧tel a}
        → ⟦ xs ≡ⁿ ys ⟧tel tt
        → f xs → f ys

substωⁿ-refl : {T : Telescope A} (f : ∀ {x} → ⟦ T ⟧tel x → Setω)
               {xs : ⟦ T ⟧tel a} {x : f xs}
             → substωⁿ f reflⁿ x ≡ω x

Jωⁿ : {T : Telescope A} {xs : ⟦ T ⟧tel a}
      (ϕ : ∀ ss → ⟦ xs ≡ⁿ ss ⟧tel tt → Setω)
    → ∀ {ss} (es : ⟦ xs ≡ⁿ ss ⟧tel tt)
    → ϕ xs reflⁿ
    → ϕ ss es

Jωⁿ-refl : {T : Telescope A} {xs : ⟦ T ⟧tel a}
           (ϕ : ∀ ss → ⟦ xs ≡ⁿ ss ⟧tel tt → Setω)
           (φ : ϕ xs reflⁿ)
         → Jωⁿ ϕ reflⁿ φ ≡ω φ

Jωⁿ {T = ε} ϕ _ φ = φ
Jωⁿ {T = T ⊢< n , ai > f} {xs , x} ϕ {ss , s} (es , e) φ =
  Jω (λ y ey → ϕ (ss , y) (es , ey)) e
     (Jωⁿ (λ ss′ es′ → ϕ (ss′ , substⁿ (< relevance ai >_ ∘ f ∘ (_ ,_)) es′ x)
                        (es′ , refl)) es d)
  where
    d : ϕ (xs , substⁿ (< relevance ai >_ ∘ f ∘ (_ ,_)) reflⁿ x)
          (reflⁿ , refl)
    d = Jω⁻¹ (λ y ey → ϕ (xs , y) (reflⁿ , ey)) (substⁿ-refl (< relevance ai >_ ∘ f ∘ (_ ,_))) φ

substωⁿ f = Jωⁿ _
substωⁿ-refl f {x = x} = Jωⁿ-refl (λ ss _ → f ss) x

Jωⁿ-refl {T = ε} ϕ φ = refl
Jωⁿ-refl {T = T ⊢< n , ai > f} {xs , x} ϕ φ =
  transω (cong≡ωω (λ x → Jω (λ y ey → ϕ (xs , y) (reflⁿ , ey))
                       (substⁿ-refl (< relevance ai >_ ∘ f ∘ (_ ,_))) x) p)
         (JJω⁻¹ (λ y ey → ϕ (xs , y) (reflⁿ , ey)) φ)
  where
    p = Jωⁿ-refl (λ ss′ es′ → ϕ (ss′ , substⁿ (< relevance ai >_ ∘ f ∘ (_ ,_)) es′ x) (es′ , refl))
                 (Jω⁻¹ (λ y ey → ϕ (xs , y) (reflⁿ , ey)) _ φ)
