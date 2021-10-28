{-# OPTIONS --safe --without-K #-}

module Generics.Mu where

open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc


private
  variable
    P   : Telescope ⊤
    V I : ExTele P
    p   : ⟦ P ⟧tel tt
    ℓ   : Level
    n   : ℕ

⟦_⟧IndArgω : ConDesc P V I → (⟦ P , I ⟧xtel → Setω) → ⟦ P , V ⟧xtel → Setω
⟦ var f    ⟧IndArgω X (p , v) = X (p , f (p , v))
⟦ π ia S C ⟧IndArgω X (p , v) = (s : < relevance ia > S (p , v)) → ⟦ C ⟧IndArgω X (p , v , s)
⟦ A ⊗ B    ⟧IndArgω X pv      = ⟦ A ⟧IndArgω X pv ×ω ⟦ B ⟧IndArgω X pv

⟦_⟧Conω : ConDesc P V I → (⟦ P , I ⟧xtel → Setω) → ⟦ P , V & I ⟧xtel → Setω
⟦ var f ⟧Conω X (p , v , i) = Liftω (i ≡ f (p , v))
⟦ π ia S C ⟧Conω X (p , v , i) = Σω (< relevance ia > S _) λ s → ⟦ C ⟧Conω X (p , (v , s) , i)
⟦ A ⊗ B ⟧Conω X (p , v , i) = ⟦ A ⟧IndArgω X (p , v) ×ω ⟦ B ⟧Conω X (p , v , i)

⟦_⟧Dataω : DataDesc P I n → (⟦ P , I ⟧xtel → Setω) → ⟦ P , I ⟧xtel → Setω
⟦_⟧Dataω {n = n} D X (p , i) =
  Σω (Fin n) λ k → ⟦ lookupCon D k ⟧Conω X (p , tt , i)

data μ (D : DataDesc P I n) (pi : ⟦ P , I ⟧xtel) : Setω where
  ⟨_⟩ : ⟦ D ⟧Dataω (μ D) pi → μ D pi
