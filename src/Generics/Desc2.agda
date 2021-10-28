{-# OPTIONS --safe --without-K #-}

module Generics.Desc2 where

open import Generics.Prelude hiding (lookup; pi)
open import Generics.Telescope


private
  variable
    P      : Telescope ⊤
    V I    : ExTele P
    p      : ⟦ P ⟧tel tt
    a ℓ ℓ′ : Level
    n      : ℕ

----------------
-- Descriptions

data ConDesc (P : Telescope ⊤) (V I : ExTele P) : Setω where
  var : (((p , v) : ⟦ P , V ⟧xtel) → ⟦ I ⟧tel p) → ConDesc P V I
  π   : ∀ (ai : ArgInfo)
        (S : ⟦ P , V ⟧xtel → Set ℓ)
        (C : ConDesc P (V ⊢< ai > S) I)
      → ConDesc P V I
  _⊗_ : (A B : ConDesc P V I) → ConDesc P V I

data DataDesc P (I : ExTele P) : ℕ → Setω where
  []  : DataDesc P I 0
  _∷_ : ∀ {n} (C : ConDesc P ε I) (D : DataDesc P I n) → DataDesc P I (suc n)

lookupCon : ∀ {n} → DataDesc P I n → Fin n → ConDesc P ε I
lookupCon (C ∷ D) (zero ) = C
lookupCon (C ∷ D) (suc k) = lookupCon D k

record Σω {a} (A : Set a) (B : A → Setω) : Setω where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

record _ω×ω_ (A B : Setω) : Setω where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

levelIndArg : ConDesc P V I → Level → Level
levelIndArg (var _) c = c
levelIndArg (π {ℓ} _ _ C) c = ℓ ⊔ levelIndArg C c
levelIndArg (A ⊗ B) c = levelIndArg A c ⊔ levelIndArg B c

⟦_⟧IndArg : (C : ConDesc P V I) → (⟦ P , I ⟧xtel → Set ℓ) → ⟦ P , V ⟧xtel → Set (levelIndArg C ℓ)
⟦ var f    ⟧IndArg X (p , v) = X (p , f (p , v))
⟦ π ia S C ⟧IndArg X (p , v) = (s : < relevance ia > S (p , v)) → ⟦ C ⟧IndArg X (p , v , s)
⟦ A ⊗ B    ⟧IndArg X pv      = ⟦ A ⟧IndArg X pv × ⟦ B ⟧IndArg X pv

⟦_⟧IndArgω : ConDesc P V I → (⟦ P , I ⟧xtel → Setω) → ⟦ P , V ⟧xtel → Setω
⟦ var f    ⟧IndArgω X (p , v) = X (p , f (p , v))
⟦ π ia S C ⟧IndArgω X (p , v) = (s : < relevance ia > S (p , v)) → ⟦ C ⟧IndArgω X (p , v , s)
⟦ A ⊗ B    ⟧IndArgω X pv      = ⟦ A ⟧IndArgω X pv ω×ω ⟦ B ⟧IndArgω X pv

data Conω {P V I} (X : ⟦ P , I ⟧xtel → Setω) p (v : ⟦ V ⟧tel p)
        : ⟦ I ⟧tel p → ConDesc P V I → Setω

⟦_⟧Conω : ConDesc P V I → (⟦ P , I ⟧xtel → Setω) → ⟦ P , V & I ⟧xtel → Setω
⟦ C ⟧Conω X (p , v , i) = Conω X p v i C

data Conω {P V I} X p v where
  var : ∀ {f} → Conω X p v (f (p , v)) (var f)
  π   : ∀ {i ia} {S : ⟦ P , V ⟧xtel → Set ℓ} {C}
        (s : < relevance ia > S (p , v))
        (x : ⟦ C ⟧Conω X (p , (v , s) , i))
      → Conω X p v i (π ia S C)
  _⊗_ : ∀ {A B i} (a : ⟦ A ⟧IndArgω X (p , v)) (b : ⟦ B ⟧Conω X (p , v , i))
      → Conω X p v i (A ⊗ B)

⟦_⟧Dataω : DataDesc P I n → (⟦ P , I ⟧xtel → Setω) → ⟦ P , I ⟧xtel → Setω
⟦_⟧Dataω {n = n} D X (p , i)= Σω (Fin n) (λ k → Conω X p tt i (lookupCon D k))

data μ (D : DataDesc P I n) (pi : ⟦ P , I ⟧xtel) : Setω where
  ⟨_⟩ : ⟦ D ⟧Dataω (μ D) pi → μ D pi
