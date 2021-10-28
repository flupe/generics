{-# OPTIONS --safe --without-K #-}

module Generics.Mu.All where

open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc
open import Generics.Mu


private
  variable
    P   : Telescope ⊤
    p   : ⟦ P ⟧tel tt
    V I : ExTele P
    ℓ c : Level
    n   : ℕ


AllIndArgωω
  : {X : ⟦ P , I ⟧xtel → Setω}
    (Pr : ∀ {i} → X (p , i) → Setω)
    (C : ConDesc P V I)
  → ∀ {v} → ⟦ C ⟧IndArgω X (p , v) → Setω
AllIndArgωω Pr (var _) x = Pr x
AllIndArgωω Pr (π ia S C) x = (s : < relevance ia > S _) → AllIndArgωω Pr C (x s)
AllIndArgωω Pr (A ⊗ B) (xa , xb) = AllIndArgωω Pr A xa ×ω AllIndArgωω Pr B xb


AllConωω
  : {X : ⟦ P , I ⟧xtel → Setω}
    (Pr : ∀ {i} → X (p , i) → Setω)
    (C : ConDesc P V I)
  → ∀ {v i} → ⟦ C ⟧Conω X (p , v , i) → Setω
AllConωω Pr (var f) x = ⊤ω
AllConωω Pr (π ia S C) (_ , x) = AllConωω Pr C x
AllConωω Pr (A ⊗ B) (xa , xb) = AllIndArgωω Pr A xa ×ω AllConωω Pr B xb


AllDataωω : {X  : ⟦ P , I ⟧xtel → Setω}
           (Pr : ∀ {i} → X (p , i) → Setω)
           (D : DataDesc P I n)
         → ∀ {i} (x : ⟦ D ⟧Dataω X (p , i))
         → Setω
AllDataωω Pr D (k , x) = AllConωω Pr (lookupCon D k) x


All : ∀ (D : DataDesc P I n) {c}
      (Pr : ∀ {i} → μ D (p , i) → Set c)
    → ∀ {i} → μ D (p , i) → Setω
All D Pr ⟨ x ⟩ = AllDataωω (λ x → Liftω (Pr x)) D x
