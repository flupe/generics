{-# OPTIONS --safe --without-K #-}

module Generics.Telescope where

open import Generics.Prelude

relevance : ArgInfo → Relevance
relevance (arg-info _ (modality r _)) = r

-- visibility of arguments for Curried types
-- TODO: actually store this in the telescope
data Vis : Set where vis hid : Vis

record Irr {i} (A : Set i) : Set i where
  constructor irrv
  field
    .unirr : A

<_>_ : ∀ {i} → Relevance → Set i → Set i
< relevant   > A = A
< irrelevant > A = Irr A

data Telescope {a} (A : Set a) : Setω

levelTel : ∀ {a} {A : Set a} → Telescope A → Level
tel      : ∀ {a} {A : Set a} → (T : Telescope A) → A → Set (levelTel T)

infixl 7 _⊢<_>_

data Telescope A where
  ε      : Telescope A
  _⊢<_>_ : ∀ (T : Telescope A) (r : Relevance) {ℓ} (f : Σ A (tel T) → Set ℓ) → Telescope A

levelTel ε = lzero
levelTel (_⊢<_>_ T r {ℓ} f) = levelTel T ⊔ ℓ

tel ε x = ⊤
tel (T ⊢< r > f) x = Σ[ t ∈ tel T x ] < r > f (x , t)

ExTele : Telescope ⊤ → Setω
ExTele T = Telescope (tel T tt)


Σ[_⇒_] : (P : Telescope ⊤) (I : ExTele P) → Set (levelTel P ⊔ levelTel I)
Σ[ P ⇒ V ] = Σ (tel P tt) (tel V)

Σ[_⇒_&_] : (P : Telescope ⊤) (V I : ExTele P) → Set (levelTel P ⊔ levelTel V ⊔ levelTel I)
Σ[ P ⇒ V & I ] = Σ[ p ∈ tel P tt ] tel V p × tel I p


Curried′ : ∀ {a} {A : Set a} (T : Telescope A) ℓ x → Vis → (tel T x → Set ℓ) → Set (ℓ ⊔ levelTel T)
Curried′ (ε           ) ℓ x v P = P tt
Curried′ (_⊢<_>_ T relevant   {ℓ′} g) ℓ x vis P =
  Curried′ T (ℓ ⊔ ℓ′) x vis λ t → (y : g (x , t))  → P (t , y)
Curried′ (_⊢<_>_ T relevant   {ℓ′} g) ℓ x hid P =
  Curried′ T (ℓ ⊔ ℓ′) x hid λ t → {y : g (x , t)}  → P (t , y)
Curried′ (_⊢<_>_ T irrelevant {ℓ′} g) ℓ x vis P =
  Curried′ T (ℓ ⊔ ℓ′) x vis λ t → .(y : g (x , t)) → P (t , irrv y)
Curried′ (_⊢<_>_ T irrelevant {ℓ′} g) ℓ x hid P =
  Curried′ T (ℓ ⊔ ℓ′) x hid λ t → .{y : g (x , t)} → P (t , irrv y)

uncurry′ : ∀ {a} {A : Set a} (T : Telescope A) ℓ x
          (P : tel T x → Set ℓ)
          {v : Vis}
          (B : Curried′ T ℓ x v P)
        → (y : tel T x) → P y
uncurry′ ε ℓ x P B tt = B
uncurry′ (_⊢<_>_ T relevant   {ℓ′} f) ℓ x P {vis} B (tx , gx) =
  uncurry′ T (ℓ ⊔ ℓ′) x (λ p →  (y : f (x , p)) → P (p , y)) {vis} B tx gx
uncurry′ (_⊢<_>_ T irrelevant {ℓ′} f) ℓ x P {vis} B (tx , irrv gx) =
  uncurry′ T (ℓ ⊔ ℓ′) x (λ p → .(y : f (x , p)) → P (p , irrv y)) {vis} B tx gx
uncurry′ (_⊢<_>_ T relevant   {ℓ′} f) ℓ x P {hid} B (tx , gx) =
  uncurry′ T (ℓ ⊔ ℓ′) x (λ p →  {y : f (x , p)} → P (p , y)) {hid} B tx {gx}
uncurry′ (_⊢<_>_ T irrelevant {ℓ′} f) ℓ x P {hid} B (tx , irrv gx) =
  uncurry′ T (ℓ ⊔ ℓ′) x (λ p → .{y : f (x , p)} → P (p , irrv y)) {hid} B tx {gx}


Curried : ∀ P (I : ExTele P) {ℓ} (Pr : Σ[ P ⇒ I ] → Set ℓ) → Vis → Set (levelTel P ⊔ levelTel I ⊔ ℓ)
Curried P I {ℓ} Pr v = Curried′ P (ℓ ⊔ levelTel I) tt v λ p → Curried′ I ℓ p v λ i → Pr (p , i)

uncurry : ∀ P (I : ExTele P) {ℓ} {Pr : Σ[ P ⇒ I ] → Set ℓ} {v} → Curried P I Pr v → (pi : Σ[ P ⇒ I ]) → Pr pi
uncurry P I C (p , i) = uncurry′ I _ p _ (uncurry′ P _ tt _ C p) i

-- Type of parametrized, indexed sets: (p₁ : A₁) ... (pₙ : Aₙ) (i₁ : B₁) ... (iₚ : Bₚ) → Set ℓ
Indexed : ∀ P (I : ExTele P) ℓ → Set (levelTel P ⊔ levelTel I ⊔ lsuc ℓ)
Indexed P I ℓ = Curried P I (const (Set ℓ)) vis

unindexed : ∀ P (I : ExTele P) ℓ → Indexed P I ℓ → Σ[ P ⇒ I ] → Set ℓ
unindexed P I ℓ = uncurry P I

-- Type of predicates on indexed sets: {p₁ : A₁} ... {pₙ : Aₙ} {i₁ : B₁} ... {iₚ : Bₚ} → X (p₁ ... iₚ) → Set ℓ
Pred : ∀ P (I : ExTele P) {a} (X : Σ[ P ⇒ I ] → Set a) ℓ
     → Set (levelTel P ⊔ levelTel I ⊔ a ⊔ lsuc ℓ)
Pred P I X ℓ = Curried P I (λ pi → X pi → Set ℓ) hid

unpred : ∀ P (I : ExTele P) {a} {X : Σ[ P ⇒ I ] → Set a} ℓ → Pred P I X ℓ
       → (pi : Σ[ P ⇒ I ]) → X pi → Set ℓ
unpred P I ℓ = uncurry P I
