{-# OPTIONS --safe #-}

open import Generics.Prelude hiding (lookup)
import Data.Vec.Base as Vec
open import Generics.Telescope
open import Generics.Desc
open import Generics.HasDesc

import Data.String as String
open import Data.String hiding (show)


module Generics.Constructions.Show
  {P} {I : ExTele P} {ℓ} {A : Curried′ P I ℓ} (H : HasDesc {P} {I} {ℓ} A) where

  open HasDesc H

  levelConHelper : ∀ {P} {V I : ExTele P} {ℓ} (C : CDesc P V I ℓ) → Level
  levelConHelper (var i) = lzero
  levelConHelper (A ⊗ B) = levelConHelper B
  levelConHelper (π {ℓ′} p S C) = ℓ′ ⊔ levelConHelper C

  ConHelper : ∀ {P} {V I : ExTele P} {ℓ} (C : CDesc P V I ℓ) (pv : Σ[ P ⇒ V ]) → Set (levelConHelper C)
  ConHelper (var i) pv = ⊤
  ConHelper (A ⊗ B) pv = ConHelper B pv
  ConHelper (π e S C) (p , v) = (S (p , v) → String) × ((s : S (p , v)) → ConHelper C (p , (v , s)))

  levelHelper : ∀ {P} {I : ExTele P} {ℓ n} → Desc P I ℓ n → Level
  levelHelper [] = lzero
  levelHelper (C ∷ D) = levelConHelper C ⊔ levelHelper D

  Helper : ∀ {P} {I : ExTele P} {ℓ n} (D : Desc P I ℓ n) (p : tel P tt) → Set (levelHelper D)
  Helper [] pi = ⊤
  Helper (C ∷ D) p = ConHelper C (p , tt) × Helper D p

  get-helper : ∀ {P} {I : ExTele P} {ℓ n} {D : Desc P I ℓ n} {p : tel P tt}
             → Helper D p
             → (k : Fin n)
             → ConHelper (lookup D k) (p , tt)
  get-helper {D = C ∷ D} (HC , _ ) zero = HC
  get-helper {D = C ∷ D} (_ , HD) (suc k) = get-helper HD k

  module _ {p : tel P tt} (SH : Helper D p) where

    mutual
      show⟦⟧ : ∀ {V} (C : CDesc P V I ℓ) {v : tel V p} → C⟦ C ⟧ (levelTel I) (μ D) (p , v) → String
      show⟦⟧ (var i) x = showμ x
      show⟦⟧ (π p S C) x = "?f" -- cannot display higher order arguments
      show⟦⟧ (A ⊗ B) (xa , xb) = show⟦⟧ A xa ++ " , " ++ show⟦⟧ B xb

      showExtend : ∀ {V} (C : CDesc P V I ℓ) {v : tel V p} {i : tel I p}
                 → ConHelper C (p , v)
                 → Extend C (levelTel I) (μ D) (p , v , i) → String
      showExtend (var i) H x = ""
      showExtend (A ⊗ B) HB (xa , xb) = show⟦⟧ A  xa ++ " , " ++ showExtend B HB xb
      showExtend (π p S C) (showS , HC) x = showExtendb p S C showS HC x

      showExtendb : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ)
                    (S : Σ[ P ⇒ V ] → Set ℓ₂)
                    (C : CDesc P (V ⊢ S) I ℓ) {v : tel V p} {i : tel I p}
                  → (S (p , v) → String)
                  → ((s : S (p , v)) → ConHelper C (p , (v , s)))
                  → Extendb (levelTel I) e (μ D) S C (p , v , i) → String
      showExtendb refl S C showS HC (s , x) = showS s ++ showExtend C (HC s) x

      showμ : {i : tel I p} → μ D (p , i) → String
      showμ ⟨ k , x ⟩ = Vec.lookup names k ++ " (" ++ showExtend (lookup D k) (get-helper SH k) x ++ ")"


  show : ∀ {pi@(p , i) : Σ[ P ⇒ I ]} → Helper D p → A′ pi → String
  show SH = showμ SH ∘ to
