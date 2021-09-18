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

    show⟦⟧ : ∀ {V} (C : ConDesc P V I ℓ) {v : ⟦ V ⟧tel p} → ⟦ C ⟧Con (levelOfTel I) (μ D) (p , v) → Maybe String
    showExtend : ∀ {V} (C : ConDesc P V I ℓ) {v : ⟦ V ⟧tel p} {i : ⟦ I ⟧tel p}
               → ConHelper p C
               → Extend C (levelOfTel I) (μ D) (p , v , i) → Maybe String
    showμ : {i : ⟦ I ⟧tel p} → μ D (p , i) → Maybe String

    showExtendb : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) (ia : ArgInfo)
                  (S : ⟦ P , V ⟧xtel → Set ℓ₂)
                  (C : ConDesc P (V ⊢< ia > S) I ℓ) {v : ⟦ V ⟧tel p} {i′ : ⟦ I ⟧tel p}
                → Show (S (p , v))
                → ConHelper p C
                → Extendᵇ (levelOfTel I) e ia (μ D) S C (p , v , i′) → Maybe String

    show⟦⟧ (var i) x = showμ x
    show⟦⟧ (π p i S C) x = just "?f" -- cannot display higher order arguments
    show⟦⟧ (A ⊗ B) (xa , xb) = Maybe.alignWith join (show⟦⟧ A xa) (show⟦⟧ B xb)

    showExtend _ var x = nothing
    showExtend _ (pi-irr {e = e} {S} {C} ⦃ _ ⦄ ⦃ HC ⦄) x
      = showExtendb e _ S C (dummyShow _) HC x
    showExtend _ (pi-rel {e = e} {S} {C} ⦃ SS ⦄ ⦃ HC ⦄) x
      = showExtendb e _ S C SS HC x
    showExtend _ (prod {A} {B} ⦃ HA ⦄ ⦃ HB ⦄) (xa , xb)
      = alignWith join (show⟦⟧ A xa) (showExtend B HB xb)

    showExtendb refl (arg-info visible (modality relevant   q)) S C showS HC (s , x)
      = alignWith join (just (show ⦃ showS ⦄ s)) (showExtend C HC x)
    showExtendb refl (arg-info visible (modality irrelevant q)) S C showS HC (s , x)
      = alignWith join (just "_") (showExtend C HC x)
    showExtendb refl (arg-info _ m) S C showS HC (s , x) = showExtend C HC x

    showμ ⟨ k , x ⟩ = just $
      Vec.lookup names k
      ++ fromMaybe "" (Maybe.map (λ x → " (" ++ x ++ ")")
                      (showExtend (lookupCon D k) (lookupHelper SH k) x))

  deriveShow : ∀ {p} ⦃ SH : ShowHelpers p ⦄ {i} → Show (A′ (p , i))
  deriveShow ⦃ SH ⦄ .show = fromMaybe "" ∘ showμ SH ∘ to
