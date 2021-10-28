{-# OPTIONS --safe #-}
module Generics.Constructions.Show where

open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc
open import Generics.All
open import Generics.HasDesc
import Generics.Helpers as Helpers

import Data.Vec.Base as Vec
import Data.String   as String
open import Data.Maybe as Maybe
open import Data.These hiding (alignWith)

open String hiding (show)


record Show {l} (A : Set l) : Set l where field show : A → String
open Show ⦃...⦄ public


private
  dummyShow : ∀ {l} (A : Set l) → Show A
  dummyShow A .show _ = ""

  join : These String String → String
  join (this x) = x
  join (that x) = x
  join (these x y) = x ++ " , " ++ y


module _
  {P I ℓ} {A : Indexed P I ℓ} (H : HasDesc A)
  (open HasDesc H)
  (open Helpers P I Show (const ⊤) (λ _ → Liftω ⊤))
  where

  ShowHelpers : ∀ p → Setω
  ShowHelpers p = Helpers p D

  module _ {p} (helpers : ShowHelpers p) where

    variable
      V : ExTele P
      v : ⟦ V ⟧tel p
      i : ⟦ I ⟧tel p

    showData-wf : (x : ⟦ D ⟧Data A′ (p , i))
                → AllDataω Acc D x
                → Maybe String

    show-wf : (x : A′ (p , i)) → Acc x → Maybe String
    show-wf x (acc a) = showData-wf (split x) a

    showData-wf (k , x) a = just $
      Vec.lookup names k
      ++ fromMaybe "" (Maybe.map (λ x → " (" ++ x ++ ")")
                                 (showCon (lookupCon D k) (lookupHelper helpers k) x a))
      where
        showIndArg : (C : ConDesc P V I)
                     (x : ⟦ C ⟧IndArg A′ (p , v))
                   → AllIndArgω Acc C x
                   → Maybe String
        showIndArg (var _) x a = show-wf x a
        showIndArg (π ia S C) x a = just "?f"
        showIndArg (A ⊗ B) (xa , xb) (aa , ab)
          = alignWith join (showIndArg A xa aa) (showIndArg B xb ab)

        showCon : (C : ConDesc P V I)
                  (H : ConHelper p C)
                  (x : ⟦ C ⟧Con A′ (p , v , i))
                → AllConω Acc C x
                → Maybe String
        showCon ._ var refl tt = nothing
        showCon ._ (pi-irr ⦃ _ ⦄ ⦃ H ⦄) (s , x) a
          = alignWith join (just "._") (showCon _ H x a)
        showCon ._ (pi-rel ⦃ S ⦄ ⦃ H ⦄) (s , x) a
          = alignWith join (just (show ⦃ S ⦄ s)) (showCon _ H x a)
        showCon ._ (prod {A} {B} ⦃ HA ⦄ ⦃ HB ⦄) (xa , xb) (aa , ab)
          = alignWith join (showIndArg A xa aa) (showCon B HB xb ab)

    show′ : (x : A′ (p , i)) → Maybe String
    show′ x = show-wf x (wf x)

  deriveShow : ∀ {p} ⦃ SH : ShowHelpers p ⦄ {i} → Show (A′ (p , i))
  deriveShow ⦃ SH ⦄ .show = fromMaybe "" ∘ show′ SH
