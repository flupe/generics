{-# OPTIONS --safe --without-K #-}
module Generics.All where

open import Generics.Prelude
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


levelAllIndArg : ConDesc P V I → Level → Level
levelAllIndArg (var _) c = c
levelAllIndArg (π {ℓ} _ _ C) c = ℓ ⊔ levelAllIndArg C c
levelAllIndArg (A ⊗ B) c = levelAllIndArg A c ⊔ levelAllIndArg B c

AllIndArg
  : {X : ⟦ P , I ⟧xtel → Set ℓ}
    (Pr : ∀ {i} → X (p , i) → Set c)
    (C : ConDesc P V I)
  → ∀ {v} → ⟦ C ⟧IndArg X (p , v) → Set (levelAllIndArg C c)
AllIndArg Pr (var _) x = Pr x
AllIndArg Pr (π (n , ai) S C) x = (s : < relevance ai > S _) → AllIndArg Pr C (app< n , ai > x s)
AllIndArg Pr (A ⊗ B) (xa , xb) = AllIndArg Pr A xa × AllIndArg Pr B xb

AllIndArgω
  : {X : ⟦ P , I ⟧xtel → Set ℓ}
    (Pr : ∀ {i} → X (p , i) → Setω)
    (C : ConDesc P V I)
  → ∀ {v} → ⟦ C ⟧IndArg X (p , v) → Setω
AllIndArgω Pr (var _) x = Pr x
AllIndArgω Pr (π (n , ai) S C) x = (s : < relevance ai > S _) → AllIndArgω Pr C (app< n , ai > x s)
AllIndArgω Pr (A ⊗ B) (xa , xb) = AllIndArgω Pr A xa ×ω AllIndArgω Pr B xb


levelAllCon : ConDesc P V I → Level → Level
levelAllCon (var _) c = lzero
levelAllCon (π {ℓ} _ _ C) c = levelAllCon C c
levelAllCon (A ⊗ B) c = levelAllIndArg A c ⊔ levelAllCon B c

AllCon
  : {X : ⟦ P , I ⟧xtel → Set ℓ}
    (Pr : ∀ {i} → X (p , i) → Set c)
    (C : ConDesc P V I)
  → ∀ {v i} → ⟦ C ⟧Con X (p , v , i) → Set (levelAllCon C c)
AllCon Pr (var _) x = ⊤
AllCon Pr (π _ _ C) (_ , x) = AllCon Pr C x
AllCon Pr (A ⊗ B) (xa , xb) = AllIndArg Pr A xa × AllCon Pr B xb

AllConω
  : {X : ⟦ P , I ⟧xtel → Set ℓ}
    (Pr : ∀ {i} → X (p , i) → Setω)
    (C : ConDesc P V I)
  → ∀ {v i} → ⟦ C ⟧Con X (p , v , i) → Setω
AllConω Pr (var f) x = ⊤ω
AllConω Pr (π ia S C) (_ , x) = AllConω Pr C x
AllConω Pr (A ⊗ B) (xa , xb) = AllIndArgω Pr A xa ×ω AllConω Pr B xb


AllData : {X  : ⟦ P , I ⟧xtel → Set ℓ}
          (Pr : ∀ {i} → X (p , i) → Set c)
          (D : DataDesc P I n)
        → ∀ {i} ((k , x) : ⟦ D ⟧Data X (p , i))
        → Set (levelAllCon (lookupCon D k) c)
AllData Pr D (k , x) = AllCon Pr (lookupCon D k) x

AllDataω : {X  : ⟦ P , I ⟧xtel → Set ℓ}
           (Pr : ∀ {i} → X (p , i) → Setω)
           (D : DataDesc P I n)
         → ∀ {i} (x : ⟦ D ⟧Data X (p , i))
         → Setω
AllDataω Pr D (k , x) = AllConω Pr (lookupCon D k) x
