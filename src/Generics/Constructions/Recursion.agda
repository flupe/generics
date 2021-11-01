{-# OPTIONS --safe #-}

open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc
open import Generics.All
open import Generics.HasDesc
import Generics.Helpers as Helpers


module Generics.Constructions.Recursion
  {P I ℓ} {A : Indexed P I ℓ}
  (H : HasDesc A) (open HasDesc H)
  {p c} (Pr : Pred′ I (λ i → A′ (p , i) → Set c))
  where

private
  variable
    V : ExTele P
    i : ⟦ I ⟧tel p
    v : ⟦ V ⟧tel p

Pr′ : A′ (p , i) → Set c
Pr′ {i} = unpred′ I _ Pr i

Below : (x : A′ (p , i)) → Acc x → Setω

BelowIndArg : (C : ConDesc P V I)
              (x : ⟦ C ⟧IndArg A′ (p , v))
            → AllIndArgω Acc C x
            → Setω
BelowIndArg (var _) x = Below x
BelowIndArg (π ai S C) x a = ∀ s → BelowIndArg C (app< ai > x s) (a s)
BelowIndArg (A ⊗ B) (x , y) (ax , ay)
  = BelowIndArg A x ax ×ω BelowIndArg B y ay

BelowCon : (C : ConDesc P V I)
           (x : ⟦ C ⟧Con A′ (p , v , i))
         → AllConω Acc C x
         → Setω
BelowCon (var _) x _ = ⊤ω
BelowCon (π ai S C) (s , x) = BelowCon C x
BelowCon (A ⊗ B) (f , x) (af , ax)
  =  BelowIndArg A f af
  ×ω BelowCon B x ax

Below x (acc a) with split x
... | (k , x) = BelowCon _ x a

module _ (f : ∀ {i} (x : A′ (p , i)) (a : Acc x) → Below x a → Pr′ x) where


  below : (x : A′ (p , i)) (a : Acc x) → Below x a
  below x (acc a) with split x
  ... | (k , x) = belowCon _ x a
    where
      belowIndArg : (C : ConDesc P V I)
                    (x : ⟦ C ⟧IndArg A′ (p , v))
                    (a : AllIndArgω Acc C x)
                  → BelowIndArg C x a
      belowIndArg (var _) x a = below x a
      belowIndArg (π ai _ C) x a s =
        belowIndArg C (app< ai > x s) (a s)
      belowIndArg (A ⊗ B) (x , y) (ax , ay)
        = belowIndArg A x ax
        , belowIndArg B y ay

      belowCon : (C : ConDesc P V I)
                 (x : ⟦ C ⟧Con A′ (p , v , i))
                 (a : AllConω Acc C x)
               → BelowCon C x a
      belowCon (var _) _ _ = tt
      belowCon (π _ _ C) (_ , x) a = belowCon C x a
      belowCon (A ⊗ B) (f , x) (af , ax)
        = belowIndArg A f af
        , belowCon B x ax

  rec : (x : A′ (p , i)) → Pr′ x
  rec x = f x (wf x) (below x (wf x))
