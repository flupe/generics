{-# OPTIONS --safe --without-K #-}
module Generics.Parametrized.Telescope where

open import Generics.Prelude


data Telescope {a} (A : Set a) : Setω

telLevel : ∀ {a} {A : Set a} → Telescope A → Level
T⟦_⟧     : ∀ {a} {A : Set a} → (T : Telescope A) → A → Set (telLevel T)


data Telescope A where
  ε   : Telescope A
  _▷_ : ∀ (T : Telescope A) {ℓ} (f : Σ A T⟦ T ⟧ → Set ℓ) → Telescope A


infixl 7 _▷_

telLevel ε = lzero
telLevel (_▷_ T {ℓ} f) = telLevel T ⊔ ℓ

T⟦ ε         ⟧ x = ⊤
T⟦ ε ▷ f     ⟧ x = f (x , tt)
T⟦ T ▷ f ▷ g ⟧ x = Σ[ t ∈ T⟦ T ▷ f ⟧ x ] g (x , t)


ExTele : Telescope ⊤ → Setω
ExTele T = Telescope (T⟦ T ⟧ tt)

[_·_] : (P : Telescope ⊤) (V : ExTele P) → Set (telLevel P ⊔ telLevel V)
[ P · V ] = Σ (T⟦ P ⟧ tt) T⟦ V ⟧

[_·_&_] : (P : Telescope ⊤) (V I : ExTele P) → Set (telLevel P ⊔ telLevel V ⊔ telLevel I)
[ P · V & I ] = Σ[ p ∈ T⟦ P ⟧ tt ] T⟦ V ⟧ p × T⟦ I ⟧ p


[_] : ∀ {a} {A : Set a} (T : Telescope A) ℓ x
      (t : T⟦ T ⟧ x → Set (lsuc (a ⊔ ℓ ⊔ telLevel T)))
    → Set (lsuc (a ⊔ ℓ ⊔ telLevel T))
[ ε ] ℓ x t = t tt
[ ε ▷ f ] ℓ x t = (y : f (x , tt)) → t y
[ _▷_ (P ▷ f) {ℓ′} g ] ℓ x t = [ P ▷ f ] (ℓ′ ⊔ ℓ) x (λ p → (y : g (x , p)) → t (p , y))

[_⇒_] : ∀ P (I : ExTele P) ℓ → Set (lsuc (telLevel P ⊔ telLevel I ⊔ ℓ))
[ P ⇒ I ] ℓ = [ P ] (ℓ ⊔ telLevel I) tt λ p → [ I ] ℓ p (const (Set _))


uncurry′ : ∀ {a} {A : Set a} {T : Telescope A} {ℓ x}
          {P : T⟦ T ⟧ x → Set (lsuc (a ⊔ ℓ ⊔ telLevel T))}
          (B : [ T ] ℓ x P)
        → (y : T⟦ T ⟧ x) → P y
uncurry′ {T = ε} B y = B
uncurry′ {T = ε ▷ f} B y = B y
uncurry′ {T = _▷_ (T ▷ f) {ℓ′} g} {ℓ} {x} {P} B (tx , gx) =
  uncurry′ {T = T ▷ f} {ℓ′ ⊔ ℓ} {x} {λ p → (y : g (x , p)) → P (p , y)} B tx gx


uncurry : ∀ P (I : ExTele P) ℓ (A : [ P ⇒ I ] ℓ)
    → (x : [ P · I ]) → Set (ℓ ⊔ telLevel I ⊔ telLevel P)

uncurry P I ℓ A (px , ix) =
  let F = uncurry′ {T = P} {ℓ ⊔ telLevel I} {tt} {λ p → [ I ] ℓ p (const _)} A px
  in uncurry′ {T = I} {_} {px} F ix
