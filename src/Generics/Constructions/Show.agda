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

  countConHelper : ∀ {P} {V I : ExTele P} {ℓ} (C : ConDesc P V I ℓ) → ℕ
  countConHelper (var i) = 0
  countConHelper (A ⊗ B) = countConHelper B
  countConHelper (π p i S C) = suc (countConHelper C)

  levelConHelper : ∀ {P} {V I : ExTele P} {ℓ} (C : ConDesc P V I ℓ) → Levels (countConHelper C)
  levelConHelper (var i) = []l
  levelConHelper (A ⊗ B) = levelConHelper B
  levelConHelper {V = V} (π {ℓ′} p i S C) = (levelOfTel V ⊔ ℓ′) ∷l levelConHelper C

  ConHelper : ∀ {P} {V I : ExTele P} {ℓ} (C : ConDesc P V I ℓ) (p : ⟦ P ⟧tel tt) → Sets (levelConHelper C)
  ConHelper (var i)      p = []S
  ConHelper (A ⊗ B)      p = ConHelper B p
  ConHelper (π e ia S C) p = (∀ {v} → < relevance ia > S (p , v) → String) ∷S ConHelper C p

  countHelper : ∀ {P} {I : ExTele P} {ℓ n} → DataDesc P I ℓ n → ℕ
  countHelper [] = 0
  countHelper (C ∷ D) = countConHelper C + countHelper D

  levelHelper : ∀ {P} {I : ExTele P} {ℓ n} (D : DataDesc P I ℓ n) → Levels (countHelper D)
  levelHelper []      = []l
  levelHelper (C ∷ D) = levelConHelper C ++l levelHelper D

  Helper : ∀ {P} {I : ExTele P} {ℓ n} (D : DataDesc P I ℓ n) (p : ⟦ P ⟧tel tt) → Sets (levelHelper D)
  Helper [] p = []S
  Helper (C ∷ D) p = ConHelper C p ++S Helper D p

  get-helper : ∀ {P} {I : ExTele P} {ℓ n} {D : DataDesc P I ℓ n} {p : ⟦ P ⟧tel tt}
             → Els (Helper D p)
             → (k : Fin n)
             → Els (ConHelper (lookup D k) p)
  get-helper {D = C ∷ D} helpers zero = ++El-proj₁ helpers
  get-helper {D = C ∷ D} helpers (suc k) = get-helper {D = D} (++El-proj₂ helpers) k

  join : These String String → String
  join (this x) = x
  join (that x) = x
  join (these x y) = x ++ " , " ++ y

  module _ {p : ⟦ P ⟧tel tt} (SH : Els (Helper D p)) where

    mutual
      show⟦⟧ : ∀ {V} (C : ConDesc P V I ℓ) {v : ⟦ V ⟧tel p} → ⟦ C ⟧Con (levelOfTel I) (μ D) (p , v) → Maybe String
      show⟦⟧ (var i) x = showμ x
      show⟦⟧ (π p i S C) x = just "?f" -- cannot display higher order arguments
      show⟦⟧ (A ⊗ B) (xa , xb) = Maybe.alignWith join (show⟦⟧ A xa) (show⟦⟧ B xb)

      showExtend : ∀ {V} (C : ConDesc P V I ℓ) {v : ⟦ V ⟧tel p} {i : ⟦ I ⟧tel p}
                 → Els (ConHelper C p)
                 → Extend C (levelOfTel I) (μ D) (p , v , i) → Maybe String
      showExtend (var i) H x = nothing
      showExtend (A ⊗ B) HB (xa , xb) = Maybe.alignWith join (show⟦⟧ A xa) (showExtend B HB xb)
      showExtend (π p i S C) HC x = showExtendb p i S C (headEl HC) (tailEl HC) x

      showExtendb : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) (ia : ArgInfo)
                    (S : ⟦ P , V ⟧xtel → Set ℓ₂)
                    (C : ConDesc P (V ⊢< ia > S) I ℓ) {v : ⟦ V ⟧tel p} {i′ : ⟦ I ⟧tel p}
                  → (< relevance ia > S (p , v) → String)
                  → (Els (ConHelper C p))
                  → Extendᵇ (levelOfTel I) e ia (μ D) S C (p , v , i′) → Maybe String
      showExtendb refl i S C showS HC (s , x) with visibility i
      ... | visible = Maybe.alignWith join (just (showS s)) (showExtend C HC x)
      ... | _       = showExtend C HC x

      showμ : {i : ⟦ I ⟧tel p} → μ D (p , i) → Maybe String
      showμ ⟨ k , x ⟩ = just $
        Vec.lookup names k
        ++ fromMaybe "" (Maybe.map (λ x → " (" ++ x ++ ")")
                        (showExtend (lookup D k) (get-helper {D = D} SH k) x))

  show : ∀ {pi@(p , i) : ⟦ P , I ⟧xtel} → Arrows (Helper D p) (A′ pi → String)
  show = curryₙ λ SH → fromMaybe "" ∘ showμ SH ∘ to
