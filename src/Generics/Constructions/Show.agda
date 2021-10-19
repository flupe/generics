{-# OPTIONS --safe #-}
module Generics.Constructions.Show where

open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc
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


module _ {P} {I : ExTele P} {ℓ}
         {A : Indexed P I ℓ}
         (H : HasDesc {P} {I} {ℓ} A) where

  open HasDesc H
  open Helpers P I ℓ Show (const ⊤) (λ _ → Liftω ⊤)

  ShowHelpers : ∀ p → Setω
  ShowHelpers p = Helpers p D

  private module _ {p : ⟦ P ⟧tel tt} (SH : ShowHelpers p) where

    variable
      V : ExTele P
      v : ⟦ V ⟧tel p
      i : ⟦ I ⟧tel p

    showIndArg : ∀ (C : ConDesc P V I ℓ) → ⟦ C ⟧IndArg _ (μ D) (p , v) → Maybe String
    showCon : ∀ (C : ConDesc P V I ℓ)
            → ConHelper p C
            → ⟦ C ⟧Con (levelOfTel I) (μ D) (p , v , i) → Maybe String
    showμ : μ D (p , i) → Maybe String

    showConᵇ : ∀ {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) (ia : ArgInfo)
               (S : ⟦ P , V ⟧xtel → Set ℓ₂)
               (C : ConDesc P (V ⊢< ia > S) I ℓ)
             → Show (S (p , v))
             → ConHelper p C
             → Conᵇ (levelOfTel I) e ia (μ D) S C (p , v , i) → Maybe String

    showIndArg (var i) x = showμ x
    showIndArg (π p i S C) x = just "?f" -- cannot display higher order arguments
    showIndArg (A ⊗ B) (xa , xb) = Maybe.alignWith join (showIndArg A xa) (showIndArg B xb)

    showCon _ var x = nothing
    showCon _ (pi-irr {e = e} {S} {C} ⦃ _ ⦄ ⦃ HC ⦄) x
      = showConᵇ e _ S C (dummyShow _) HC x
    showCon _ (pi-rel {e = e} {S} {C} ⦃ SS ⦄ ⦃ HC ⦄) x
      = showConᵇ e _ S C SS HC x
    showCon _ (prod {A} {B} ⦃ HA ⦄ ⦃ HB ⦄) (xa , xb)
      = alignWith join (showIndArg A xa) (showCon B HB xb)

    showConᵇ refl (ai visible relevant q) S C showS HC (s , x)
      = alignWith join (just (show ⦃ showS ⦄ s)) (showCon C HC x)
    showConᵇ refl (ai visible irrelevant q) S C showS HC (s , x)
      = alignWith join (just "_") (showCon C HC x)
    showConᵇ refl (arg-info _ m) S C showS HC (s , x) = showCon C HC x

    showμ ⟨ k , x ⟩ = just $
      Vec.lookup names k
      ++ fromMaybe "" (Maybe.map (λ x → " (" ++ x ++ ")")
                      (showCon (lookupCon D k) (lookupHelper SH k) x))

  deriveShow : ∀ {p} ⦃ SH : ShowHelpers p ⦄ {i} → Show (A′ (p , i))
  deriveShow ⦃ SH ⦄ .show = fromMaybe "" ∘ showμ SH ∘ to
