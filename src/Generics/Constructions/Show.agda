open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc
open import Generics.HasDesc

import Data.Vec.Base as Vec
import Data.String   as String
open import Data.Maybe as Maybe
open import Data.These

open String hiding (show)


module Generics.Constructions.Show
  {P} {I : ExTele P} {ℓ} {A : Indexed P I ℓ} (H : HasDesc {P} {I} {ℓ} A) where

  open HasDesc H

  levelConHelper : ∀ {P} {V I : ExTele P} {ℓ} (C : Desc P V I ℓ) → Level
  levelConHelper (var i) = lzero
  levelConHelper (A ⊗ B) = levelConHelper B
  levelConHelper (π {ℓ′} p i S C) = ℓ′ ⊔ levelConHelper C

  ConHelper : ∀ {P} {V I : ExTele P} {ℓ} (C : Desc P V I ℓ) (pv : Σ[ P ⇒ V ]) → Set (levelConHelper C)
  ConHelper (var i) pv = ⊤
  ConHelper (A ⊗ B) pv = ConHelper B pv
  ConHelper (π e ia S C) (p , v) = (< relevance ia > S (p , v) → String) × ((s : < relevance ia > S (p , v)) → ConHelper C (p , (v , s)))

  levelHelper : ∀ {P} {I : ExTele P} {ℓ n} → DataDesc P I ℓ n → Level
  levelHelper [] = lzero
  levelHelper (C ∷ D) = levelConHelper C ⊔ levelHelper D

  Helper : ∀ {P} {I : ExTele P} {ℓ n} (D : DataDesc P I ℓ n) (p : ⟦ P ⟧tel tt) → Set (levelHelper D)
  Helper [] p = ⊤
  Helper (C ∷ D) p = ConHelper C (p , tt) × Helper D p

  get-helper : ∀ {P} {I : ExTele P} {ℓ n} {D : DataDesc P I ℓ n} {p : ⟦ P ⟧tel tt}
             → Helper D p
             → (k : Fin n)
             → ConHelper (lookup D k) (p , tt)
  get-helper {D = C ∷ D} (HC , _ ) zero = HC
  get-helper {D = C ∷ D} (_ , HD) (suc k) = get-helper HD k

  join : These String String → String
  join (this x) = x
  join (that x) = x
  join (these x y) = x ++ " , " ++ y

  module _ {p : ⟦ P ⟧tel tt} (SH : Helper D p) where

    mutual
      show⟦⟧ : ∀ {V} (C : Desc P V I ℓ) {v : ⟦ V ⟧tel p} → ⟦ C ⟧ (levelOfTel I) (μ D) (p , v) → Maybe String
      show⟦⟧ (var i) x = showμ x
      show⟦⟧ (π p i S C) x = just "?f" -- cannot display higher order arguments
      show⟦⟧ (A ⊗ B) (xa , xb) = Maybe.alignWith join (show⟦⟧ A xa) (show⟦⟧ B xb)

      showExtend : ∀ {V} (C : Desc P V I ℓ) {v : ⟦ V ⟧tel p} {i : ⟦ I ⟧tel p}
                 → ConHelper C (p , v)
                 → Extend C (levelOfTel I) (μ D) (p , v , i) → Maybe String
      showExtend (var i) H x = nothing
      showExtend (A ⊗ B) HB (xa , xb) = Maybe.alignWith join (show⟦⟧ A xa) (showExtend B HB xb)
      showExtend (π p i S C) (showS , HC) x = showExtendb p i S C showS HC x

      showExtendb : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) (ia : ArgInfo)
                    (S : Σ[ P ⇒ V ] → Set ℓ₂)
                    (C : Desc P (V ⊢< ia > S) I ℓ) {v : ⟦ V ⟧tel p} {i′ : ⟦ I ⟧tel p}
                  → (< relevance ia > S (p , v) → String)
                  → ((s : < relevance ia > S (p , v)) → ConHelper C (p , (v , s)))
                  → Extendᵇ (levelOfTel I) e ia (μ D) S C (p , v , i′) → Maybe String
      showExtendb refl i S C showS HC (s , x) with visibility i
      ... | visible = Maybe.alignWith join (just (showS s)) (showExtend C (HC s) x)
      ... | _       = showExtend C (HC s) x

      showμ : {i : ⟦ I ⟧tel p} → μ D (p , i) → Maybe String
      showμ ⟨ k , x ⟩ = just $
        Vec.lookup names k
        ++ fromMaybe "" (Maybe.map (λ x → " (" ++ x ++ ")")
                        (showExtend (lookup D k) (get-helper SH k) x))

  show : ∀ {pi@(p , i) : Σ[ P ⇒ I ]} → Helper D p → A′ pi → String
  show SH = fromMaybe "" ∘ showμ SH ∘ to
