{-# OPTIONS --safe --without-K #-}

module Generics.Desc where

open import Data.String using (String)
open import Generics.Prelude hiding (lookup)
open import Generics.Telescope


private
  variable
    P   : Telescope ⊤
    V I : ExTele P
    p   : ⟦ P ⟧tel tt
    ℓ   : Level
    n   : ℕ

data ConDesc (P : Telescope ⊤) (V I : ExTele P) : Setω where
  var : (((p , v) : ⟦ P , V ⟧xtel) → ⟦ I ⟧tel p) → ConDesc P V I
  π   : (ai : String × ArgInfo)
        (S : ⟦ P , V ⟧xtel → Set ℓ)
        (C : ConDesc P (V ⊢< ai > S) I)
      → ConDesc P V I
  _⊗_ : (A B : ConDesc P V I) → ConDesc P V I

data DataDesc P (I : ExTele P) : ℕ → Setω where
  []  : DataDesc P I 0
  _∷_ : ∀ {n} (C : ConDesc P ε I) (D : DataDesc P I n) → DataDesc P I (suc n)


lookupCon : DataDesc P I n → Fin n → ConDesc P ε I
lookupCon (C ∷ D) (zero ) = C
lookupCon (C ∷ D) (suc k) = lookupCon D k

levelIndArg : ConDesc P V I → Level → Level
levelIndArg (var _) c = c
levelIndArg (π {ℓ} _ _ C) c = ℓ ⊔ levelIndArg C c
levelIndArg (A ⊗ B) c = levelIndArg A c ⊔ levelIndArg B c

⟦_⟧IndArg : (C : ConDesc P V I)
          → (⟦ P , I ⟧xtel → Set ℓ)
          → (⟦ P , V ⟧xtel → Set (levelIndArg C ℓ))
⟦ var f    ⟧IndArg X (p , v) = X (p , f (p , v))
⟦ π ai S C ⟧IndArg X (p , v) = Π< ai > (S (p , v)) (λ s → ⟦ C ⟧IndArg X (p , v , s))
⟦ A ⊗ B    ⟧IndArg X pv      = ⟦ A ⟧IndArg X pv × ⟦ B ⟧IndArg X pv


levelCon : ConDesc P V I → Level → Level
levelCon {I = I} (var _) c = levelOfTel I
levelCon (π {ℓ} _ _ C) c = ℓ ⊔ levelCon C c
levelCon (A ⊗ B) c = levelIndArg A c ⊔ levelCon B c

⟦_⟧Con : (C : ConDesc P V I)
       → (⟦ P , I     ⟧xtel → Set ℓ)
       → (⟦ P , V & I ⟧xtel → Set (levelCon C ℓ))
⟦ var f    ⟧Con X (p , v , i) = i ≡ f (p , v)
⟦ π (n , ai) S C ⟧Con X (p , v , i) = Σ[ s ∈ < relevance ai > S (p , v) ] ⟦ C ⟧Con X (p , ((v , s) , i))
⟦ A ⊗ B    ⟧Con X pvi@(p , v , i) = ⟦ A ⟧IndArg X (p , v) × ⟦ B ⟧Con X pvi


record ⟦_⟧Data (D : DataDesc P I n) (X : ⟦ P , I ⟧xtel → Set ℓ) (pi : ⟦ P , I ⟧xtel) : Setω where
  constructor _,_
  field
    k   : Fin n
    val : ⟦ lookupCon D k ⟧Con X (proj₁ pi , tt , proj₂ pi)
open ⟦_⟧Data


-- ⟦_⟧Data : DataDesc P I n → (⟦ P , I ⟧xtel → Set ℓ) → ⟦ P , I ⟧xtel → Setω
-- ⟦_⟧Data {n = n} D X (p , i) = Σℓω (Fin n) (λ k → ⟦ lookupCon D k ⟧Con X (p , tt , i))
