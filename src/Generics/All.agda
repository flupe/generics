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
AllIndArg Pr (π ia S C) x = (s : < relevance ia > S _) → AllIndArg Pr C (app< ia > x s)
AllIndArg Pr (A ⊗ B) (xa , xb) = AllIndArg Pr A xa × AllIndArg Pr B xb

AllIndArgω
  : {X : ⟦ P , I ⟧xtel → Set ℓ}
    (Pr : ∀ {i} → X (p , i) → Setω)
    (C : ConDesc P V I)
  → ∀ {v} → ⟦ C ⟧IndArg X (p , v) → Setω
AllIndArgω Pr (var _) x = Pr x
AllIndArgω Pr (π ia S C) x = (s : < relevance ia > S _) → AllIndArgω Pr C (app< ia > x s)
AllIndArgω Pr (A ⊗ B) (xa , xb) = AllIndArgω Pr A xa ×ω AllIndArgω Pr B xb

AllIndArgωω
  : {X : ⟦ P , I ⟧xtel → Setω}
    (Pr : ∀ {i} → X (p , i) → Setω)
    (C : ConDesc P V I)
  → ∀ {v} → ⟦ C ⟧IndArgω X (p , v) → Setω
AllIndArgωω Pr (var _) x = Pr x
AllIndArgωω Pr (π ia S C) x = (s : < relevance ia > S _) → AllIndArgωω Pr C (x s)
AllIndArgωω Pr (A ⊗ B) (xa , xb) = AllIndArgωω Pr A xa ×ω AllIndArgωω Pr B xb

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

record ⊤ω : Setω where
  instance constructor tt

AllConω
  : {X : ⟦ P , I ⟧xtel → Set ℓ}
    (Pr : ∀ {i} → X (p , i) → Setω)
    (C : ConDesc P V I)
  → ∀ {v i} → ⟦ C ⟧Con X (p , v , i) → Setω
AllConω Pr (var f) x = ⊤ω
AllConω Pr (π ia S C) (_ , x) = AllConω Pr C x
AllConω Pr (A ⊗ B) (xa , xb) = AllIndArgω Pr A xa ×ω AllConω Pr B xb

AllConωω
  : {X : ⟦ P , I ⟧xtel → Setω}
    (Pr : ∀ {i} → X (p , i) → Setω)
    (C : ConDesc P V I)
  → ∀ {v i} → ⟦ C ⟧Conω X (p , v , i) → Setω
AllConωω Pr (var f) x = ⊤ω
AllConωω Pr (π ia S C) (_ , x) = AllConωω Pr C x
AllConωω Pr (A ⊗ B) (xa , xb) = AllIndArgωω Pr A xa ×ω AllConωω Pr B xb

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

{-


mutual
  mapAllIndArg : ∀ {V} {ℓ₁ ℓ₂ ℓ₃} (C : ConDesc P V I ℓ₁)
             {X : ⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₂)}
             {Y : ⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₃)}
             (f : ∀ {i} → X (p , i) → Y (p , i))
             {c} (Pr : ∀ {i} → Y (p , i) → Set c)
             {v} {x : ⟦ C ⟧IndArg ℓ₂ X (p , v)}
           → AllIndArg C X (Pr ∘ f) x
           → AllIndArg C Y Pr (mapIndArg ℓ₂ ℓ₃ f C x)
  mapAllIndArg (var i) f Pr H = H
  mapAllIndArg (A ⊗ B) f Pr (HA , HB) = mapAllIndArg A f Pr HA , mapAllIndArg B f Pr HB
  mapAllIndArg (π p i S C) f Pr H = mapAllIndArgᵇ f Pr p i C H

  mapAllIndArgᵇ : ∀ {V} {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅}
              {X  : ⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₄)}
              {Y  : ⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₅)}
              (f  : ∀ {i} → X (p , i) → Y (p , i))
              {c} (Pr : ∀ {i} → Y (p , i) → Set c)
              (e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
              (ia : ArgInfo)
              {S  : ⟦ P , V ⟧xtel → Set ℓ₂}
              (C  : ConDesc P (V ⊢< ia > S) I ℓ₃)
            → ∀ {v} {x : IndArgᵇ ℓ₄ e ia X S C (p , v)}
            → AllIndArgᵇ e ia X S C (Pr ∘ f) x
            → AllIndArgᵇ e ia Y S C Pr (mapIndArgᵇ ℓ₄ ℓ₅ f e ia S C x)
  mapAllIndArgᵇ f Pr refl i C H s = mapAllIndArg C f Pr (H s)

mutual
  mapAllCon : ∀ {V} {ℓ₁ ℓ₂ ℓ₃} (C : ConDesc P V I ℓ₁)
                 {X : ⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₂)}
                 {Y : ⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₃)}
                 (f : ∀ {i} → X (p , i) → Y (p , i))
                 {c} (Pr : ∀ {i} → Y (p , i) → Set c)
                 {v i} {x : ⟦ C ⟧Con ℓ₂ X (p , v , i)}
               → AllCon C X (Pr ∘ f) x
               → AllCon C Y Pr (mapCon ℓ₂ ℓ₃ f C x)
  mapAllCon (var i) f Pr H = H
  mapAllCon (A ⊗ B) f Pr (HA , HB) = mapAllIndArg A f Pr HA , mapAllCon B f Pr HB
  mapAllCon (π p i S C) f Pr H = mapAllConᵇ f Pr p i C H

  mapAllConᵇ : ∀ {V} {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅}
                  {X  : ⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₄)}
                  {Y  : ⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₅)}
                  (f  : ∀ {i} → X (p , i) → Y (p , i))
                  {c} (Pr : ∀ {i} → Y (p , i) → Set c)
                  (e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
                  (ia : ArgInfo)
                  {S  : ⟦ P , V ⟧xtel → Set ℓ₂}
                  (C  : ConDesc P (V ⊢< ia > S) I ℓ₃)
                → ∀ {v i} {x : Conᵇ ℓ₄ e ia X S C (p , v , i)}
                → AllConᵇ e ia X S C (Pr ∘ f) x
                → AllConᵇ e ia Y S C Pr (mapConᵇ ℓ₄ ℓ₅ f e ia S C x)
  mapAllConᵇ f Pr refl _ C H = mapAllCon C f Pr H

-}