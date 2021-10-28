{-# OPTIONS --safe #-}

open import Generics.Prelude
open import Generics.Telescope
open import Generics.Desc
open import Generics.Mu
open import Generics.All

module Generics.Desc.Elim
  {P I n} {D : DataDesc P I n}
  {p c} (Pr : ∀ {i} → μ D (p , i) → Set c)
  (f : ∀ {i} (x : μ D (p , i)) → All D Pr x → Pr x) where

private
  variable
    V : ExTele P
    i : ⟦ I ⟧tel p
    v : ⟦ V ⟧tel p

private
  Pr′ : ∀{i} → μ D (p , i) → Setω
  Pr′ x = Liftω (Pr x)

all : (x : μ D (p , i)) → All D Pr x

allIndArg : (C : ConDesc P V I)
            (x : ⟦ C ⟧IndArgω (μ D) (p , v))
          → AllIndArgωω Pr′ C x
allIndArg (var _) x = liftω (f x (all x))
allIndArg (A ⊗ B) (xa , xb) = allIndArg A xa , allIndArg B xb
allIndArg (π _ _ C) x s = allIndArg C (x s)

allCon : (C : ConDesc P V I)
         (x : ⟦ C ⟧Conω (μ D) (p , v , i))
       → AllConωω Pr′ C x
allCon (var _) x = tt
allCon (A ⊗ B) (xa , xb) = allIndArg A xa , allCon B xb
allCon (π _ _ C) (_ , x) = allCon C x

all ⟨ k , x ⟩ = allCon (lookupCon D k) x

elim : (x : μ D (p , i)) → Pr x
elim x = f x (all x)
