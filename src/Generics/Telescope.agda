{-# OPTIONS --safe --without-K #-}

module Generics.Telescope where

open import Generics.Prelude hiding (curry)

private variable
  l : Level
  A B : Set l
  x y : A


data Telescope (A : Set l) : Setω

private variable T : Telescope A

levelOfTel : Telescope A → Level
⟦_⟧tel     : (T : Telescope A) → A → Set (levelOfTel T)

infixl 7 _⊢<_>_

data Telescope A where
  ε      : Telescope A
  _⊢<_>_ : ∀ (T : Telescope A) (ai : ArgInfo) {ℓ} (f : Σ A ⟦ T ⟧tel → Set ℓ) → Telescope A

levelOfTel ε = lzero
levelOfTel (_⊢<_>_ T _ {ℓ} f) = levelOfTel T ⊔ ℓ

⟦ ε ⟧tel x = ⊤
⟦ T ⊢< i > f ⟧tel x = Σ[ t ∈ ⟦ T ⟧tel x ] < relevance i > f (x , t)



hideInfo : ArgInfo → ArgInfo
hideInfo i = arg-info hidden (getModality i)

ExTele : Telescope ⊤ → Setω
ExTele T = Telescope (⟦ T ⟧tel tt)

⟦_,_⟧xtel : (P : Telescope ⊤) (I : ExTele P) → Set (levelOfTel P ⊔ levelOfTel I)
⟦ P , V ⟧xtel = Σ (⟦ P ⟧tel tt) ⟦ V ⟧tel

⟦_,_&_⟧xtel : (P : Telescope ⊤) (V I : ExTele P) → Set (levelOfTel P ⊔ levelOfTel V ⊔ levelOfTel I)
⟦ P , V & I ⟧xtel = Σ[ p ∈ ⟦ P ⟧tel tt ] ⟦ V ⟧tel p × ⟦ I ⟧tel p

Curried′ : (T : Telescope A) → (⟦ T ⟧tel x → Set l) → Set (l ⊔ levelOfTel T)
Curried′ ε P = P tt
Curried′ (T ⊢< i > g) P = Curried′ T λ t → Π< i > (g (_ , t)) λ y → P (t , y)

Pred′ : (T : Telescope A) → (⟦ T ⟧tel x → Set l) → Set (l ⊔ levelOfTel T)
Pred′ ε P = P tt
Pred′ (T ⊢< i > g) P = Pred′ T λ t → Π< hideInfo i > (g (_ , t)) λ y → P (t , y)

uncurry′ : (T : Telescope A) (P : ⟦ T ⟧tel x → Set l) (B : Curried′ T P) → (y : ⟦ T ⟧tel x) → P y
uncurry′ ε P B tt = B
uncurry′ (T ⊢< i > f) P B (tx , gx) =
  app< i > (uncurry′ T (λ p → Π< i > (f (_ , p)) (λ y → P (p , y))) B tx) _

curry′ : (T : Telescope A) (P : ⟦ T ⟧tel x → Set l) → ((y : ⟦ T ⟧tel x) → P y) → Curried′ T P
curry′ ε P f = f tt
curry′ (T ⊢< i > S) P f =
  curry′ T _ λ t → fun< i > λ s → f (t , s)

unpred′ : (T : Telescope A) (P : ⟦ T ⟧tel x → Set l) (B : Pred′ T P) → (y : ⟦ T ⟧tel x) → P y
unpred′ ε P B tt = B
unpred′ (T ⊢< i > f) P B (tx , gx) =
  app< hideInfo i > (unpred′ T (λ p → Π< hideInfo i > (f (_ , p)) λ y → P (p , y)) B tx) _

pred′ : (T : Telescope A) (P : ⟦ T ⟧tel x → Set l) → ((y : ⟦ T ⟧tel x) → P y) → Pred′ T P
pred′ ε P f = f tt
pred′ (T ⊢< i > S) P f =
  pred′ T _ λ t → fun< hideInfo i > λ s → f (t , s)

Curried : ∀ P (I : ExTele P) {ℓ} (Pr : ⟦ P , I ⟧xtel → Set ℓ) → Set (levelOfTel P ⊔ levelOfTel I ⊔ ℓ)
Curried P I {ℓ} Pr = Curried′ P λ p → Curried′ I λ i → Pr (p , i)

curry : ∀ {P} {I : ExTele P} {ℓ} {Pr : ⟦ P , I ⟧xtel → Set ℓ}
      → ((pi : ⟦ P , I ⟧xtel) →  Pr pi) → Curried P I Pr
curry f = curry′ _ _ λ p → curry′ _ _ λ i → f (p , i)

uncurry : ∀ P (I : ExTele P) {ℓ} {Pr : ⟦ P , I ⟧xtel → Set ℓ} → Curried P I Pr → (pi : ⟦ P , I ⟧xtel) → Pr pi
uncurry P I C (p , i) = uncurry′ I _ (uncurry′ P _ C p) i


-- Type of parametrized, indexed sets: (p₁ : A₁) ... (pₙ : Aₙ) (i₁ : B₁) ... (iₚ : Bₚ) → Set ℓ
Indexed : ∀ P (I : ExTele P) ℓ → Set (levelOfTel P ⊔ levelOfTel I ⊔ lsuc ℓ)
Indexed P I ℓ = Curried P I (const (Set ℓ))

unindexed : ∀ P (I : ExTele P) ℓ → Indexed P I ℓ → ⟦ P , I ⟧xtel → Set ℓ
unindexed P I ℓ = uncurry P I


-- Type of predicates on parametrized & indexed families:
--   {p₁ : A₁} ... {pₙ : Aₙ} {i₁ : B₁} ... {iₚ : Bₚ} → X (p₁ ... iₚ) → Set ℓ
Pred : ∀ P (I : ExTele P) {a} (X : ⟦ P , I ⟧xtel → Set a) ℓ
     → Set (levelOfTel P ⊔ levelOfTel I ⊔ a ⊔ lsuc ℓ)
Pred P I X ℓ = Pred′ P λ p → Pred′ I λ i → X (p , i) → Set ℓ

unpred : ∀ P (I : ExTele P) {a} {X : ⟦ P , I ⟧xtel → Set a} ℓ → Pred P I X ℓ
       → (pi : ⟦ P , I ⟧xtel) → X pi → Set ℓ
unpred P I ℓ C (p , i) = unpred′ I _ (unpred′ P _ C p) i
