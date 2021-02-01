{-# OPTIONS --safe --without-K #-}
module Generics.Parametrized.Telescope where

open import Generics.Prelude


data Telescope {a} (A : Set a) : Setω

levelTel : ∀ {a} {A : Set a} → Telescope A → Level
tel      : ∀ {a} {A : Set a} → (T : Telescope A) → A → Set (levelTel T)

infixl 7 _⊢_

data Telescope A where
  ε   : Telescope A
  _⊢_ : ∀ (T : Telescope A) {ℓ} (f : Σ A (tel T) → Set ℓ) → Telescope A


levelTel ε = lzero
levelTel (_⊢_ T {ℓ} f) = levelTel T ⊔ ℓ

tel ε           x = ⊤
tel (ε ⊢ f    ) x = f (x , tt)
tel (T ⊢ g ⊢ f) x = Σ[ t ∈ tel (T ⊢ g) x ] f (x , t)


ExTele : Telescope ⊤ → Setω
ExTele T = Telescope (tel T tt)

Σ[_⇒_] : (P : Telescope ⊤) (I : ExTele P) → Set (levelTel P ⊔ levelTel I)
Σ[ P ⇒ V ] = Σ (tel P tt) (tel V)

Σ[_⇒_&_] : (P : Telescope ⊤) (V I : ExTele P) → Set (levelTel P ⊔ levelTel V ⊔ levelTel I)
Σ[ P ⇒ V & I ] = Σ[ p ∈ tel P tt ] tel V p × tel I p


Curried : ∀ {a} {A : Set a} (T : Telescope A) ℓ x (P : tel T x → Set ℓ)
    → Set (ℓ ⊔ levelTel T)
Curried (ε           ) ℓ x P = P tt -- t tt
Curried (_⊢_ ε {ℓ′} g) ℓ x P = Curried ε (ℓ ⊔ ℓ′) x λ tt → (y : g (x , tt)) → P y
Curried (_⊢_ (T ⊢ f) {ℓ′} g) ℓ x P = Curried (T ⊢ f) (ℓ ⊔ ℓ′) x λ p → (y : g (x , p)) → P (p , y) 


uncurry : ∀ {a} {A : Set a} (T : Telescope A) ℓ x
          (P : tel T x → Set ℓ)
          (B : Curried T ℓ x P)
        → (y : tel T x) → P y
uncurry ε ℓ x P B tt = B
uncurry (ε ⊢ f) ℓ x P B y = B y
uncurry (_⊢_ (T ⊢ f) {ℓ′} g) ℓ x P B (tx , gx) =
  uncurry (T ⊢ f) (ℓ ⊔ ℓ′) x (λ p → (y : g (x , p)) → P (p , y)) B tx gx


[_⇒_] : ∀ P (I : ExTele P) ℓ → Set (levelTel P ⊔ levelTel I ⊔ lsuc ℓ)
[ P ⇒ I ] ℓ = Curried P (lsuc ℓ ⊔ levelTel I) tt λ p → Curried I (lsuc ℓ) p (const (Set ℓ))

unroll : ∀ {P} (I : ExTele P) {ℓ} (A : [ P ⇒ I ] ℓ) → Σ[ P ⇒ I ] → Set ℓ
unroll {P} I {ℓ} A (p , i) = uncurry I (lsuc ℓ) p _ (uncurry P _ tt _ A p) i
