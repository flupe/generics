{-# OPTIONS --without-K --sized-types #-}
module Generics.All where

open import Generics.Prelude
open import Generics.Telescope
open import Generics.Desc
open import Generics.Mu

open import Agda.Builtin.Size

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
    (Pr : ∀ {i} → X (p , i) → Size → Setω)
    (C : ConDesc P V I)
  → ∀ {v} → ⟦ C ⟧IndArg X (p , v) → Size → Setω
AllIndArgω Pr (var _) x j = Pr x j
AllIndArgω Pr (π (n , ai) S C) x j = (s : < relevance ai > S _) → AllIndArgω Pr C (app< n , ai > x s) j
AllIndArgω Pr (A ⊗ B) (xa , xb) j = AllIndArgω Pr A xa j ×ω AllIndArgω Pr B xb j


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
    (Pr : ∀ {i} → X (p , i) → Size → Setω)
    (C : ConDesc P V I)
  → ∀ {v i} → ⟦ C ⟧Con X (p , v , i) → Size → Setω
AllConω Pr (var f) x j = ⊤ω
AllConω Pr (π ia S C) (_ , x) j = AllConω Pr C x j
AllConω Pr (A ⊗ B) (xa , xb) j = AllIndArgω Pr A xa j ×ω AllConω Pr B xb j


AllData : {X  : ⟦ P , I ⟧xtel → Set ℓ}
          (Pr : ∀ {i} → X (p , i) → Set c)
          (D : DataDesc P I n)
        → ∀ {i} ((k , x) : ⟦ D ⟧Data X (p , i))
        → Set (levelAllCon (lookupCon D k) c)
AllData Pr D (k , x) = AllCon Pr (lookupCon D k) x

AllDataω : {X  : ⟦ P , I ⟧xtel → Set ℓ}
           (Pr : ∀ {i} → X (p , i) → Size → Setω)
           (D : DataDesc P I n)
         → ∀ {i} (x : ⟦ D ⟧Data X (p , i))
         → Size → Setω
AllDataω Pr D (k , x) j = AllConω Pr (lookupCon D k) x j
