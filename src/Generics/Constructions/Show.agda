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
  ConHelper (π e ia S C) (p , v) = (< ArgI.rel ia > S (p , v) → String)
                                 × ((s : < ArgI.rel ia > S (p , v)) → ConHelper C (p , (v , s)))

  open import Data.Sum

  ConHelperMaybe : ∀ {P} {V I : ExTele P} {ℓ} (C : Desc P V I ℓ) (pv : Σ[ P ⇒ V ])
                 → Maybe (ConHelper C pv)
  ConHelperMaybe (var x) pv = just _
  ConHelperMaybe (A ⊗ B) pv = ConHelperMaybe B pv
  ConHelperMaybe C pv = nothing

  levelHelper : ∀ {P} {I : ExTele P} {ℓ n} → DataDesc P I ℓ n → Level
  levelHelper [] = lzero
  levelHelper (C ∷ D) = levelConHelper C ⊔ levelHelper D

  open import Function.Base using (case_of_)

  data LProd : Setω where
    [] : LProd
    _∷_ : ∀ {ℓ} → Set ℓ → LProd → LProd

  levelLProd : LProd → Level
  levelLProd [] = lzero
  levelLProd (_∷_ {ℓ} _ lp) = ℓ ⊔ levelLProd lp

  ⟦_⟧LProd : (lp : LProd) → Set (levelLProd lp)
  ⟦ []     ⟧LProd = ⊤
  ⟦ A ∷ lp ⟧LProd = A × ⟦ lp ⟧LProd

  ⟦_↦_⟧LProd : ∀ {ℓ} → (lp : LProd) → Set ℓ → Set (ℓ ⊔ levelLProd lp)
  ⟦ []     ↦ B ⟧LProd = B
  ⟦ A ∷ lp ↦ B ⟧LProd = A → ⟦ lp ↦ B ⟧LProd

  curryLProd : ∀ {ℓ} {B : Set ℓ} → (lp : LProd) →
               (⟦ lp ⟧LProd → B) → ⟦ lp ↦ B ⟧LProd
  curryLProd []       f = f _
  curryLProd (_ ∷ lp) f = λ a → curryLProd lp (f ∘′ (a ,_))

  Helper : ∀ {P} {I : ExTele P} {ℓ n} (D : DataDesc P I ℓ n) (p : tel P tt) → LProd
  Helper [] pi = []
  Helper (C ∷ D) p with ConHelperMaybe C (p , tt)
  ... | just _  = Helper D p
  ... | nothing = ConHelper C (p , tt) ∷ Helper D p

  get-helper : ∀ {P} {I : ExTele P} {ℓ n} (D : DataDesc P I ℓ n) {p : tel P tt}
             → ⟦ Helper D p ⟧LProd
             → (k : Fin n)
             → ConHelper (lookup D k) (p , tt)
  get-helper (C ∷ D) {p} hp k with ConHelperMaybe C (p , tt)
  get-helper (C ∷ D)     hp zero    | just pr  = pr
  get-helper (C ∷ D)     hp (suc k) | just _   = get-helper D hp k
  get-helper (C ∷ D) {p} hp zero    | nothing  = proj₁ hp
  get-helper (C ∷ D) {p} hp (suc k) | nothing  = get-helper D (proj₂ hp) k

  join : These String String → String
  join (this x) = x
  join (that x) = x
  join (these x y) = x ++ " , " ++ y

  module _ {p : tel P tt} (SH : ⟦ Helper D p ⟧LProd) where

    mutual
      show⟦⟧ : ∀ {V} (C : Desc P V I ℓ) {v : tel V p} → ⟦ C ⟧ (levelTel I) (μ D) (p , v) → Maybe String
      show⟦⟧ (var i) x = showμ x
      show⟦⟧ (π p i S C) x = just "?f" -- cannot display higher order arguments
      show⟦⟧ (A ⊗ B) (xa , xb) = Maybe.alignWith join (show⟦⟧ A xa) (show⟦⟧ B xb)

      showExtend : ∀ {V} (C : Desc P V I ℓ) {v : tel V p} {i : tel I p}
                 → ConHelper C (p , v)
                 → Extend C (levelTel I) (μ D) (p , v , i) → Maybe String
      showExtend (var i) H x = nothing
      showExtend (A ⊗ B) HB (xa , xb) = Maybe.alignWith join (show⟦⟧ A xa) (showExtend B HB xb)
      showExtend (π p i S C) (showS , HC) x = showExtendb p i S C showS HC x

      showExtendb : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) (ia : ArgI)
                    (S : Σ[ P ⇒ V ] → Set ℓ₂)
                    (C : Desc P (V ⊢< ia > S) I ℓ) {v : tel V p} {i′ : tel I p}
                  → (< ArgI.rel ia > S (p , v) → String)
                  → ((s : < ArgI.rel ia > S (p , v)) → ConHelper C (p , (v , s)))
                  → Extendᵇ (levelTel I) e ia (μ D) S C (p , v , i′) → Maybe String
      showExtendb refl i S C showS HC (s , x) with ArgI.vis i
      ... | visible = Maybe.alignWith join (just (showS s)) (showExtend C (HC s) x)
      ... | _       = showExtend C (HC s) x

      showμ : {i : tel I p} → μ D (p , i) → Maybe String
      showμ ⟨ k , x ⟩ = just $
        Vec.lookup names k
        ++ fromMaybe "" (Maybe.map (λ x → " (" ++ x ++ ")")
                        (showExtend (lookup D k) (get-helper D SH k) x))

  show : ∀ {pi@(p , i) : Σ[ P ⇒ I ]} → ⟦ Helper D p ↦ (A′ pi → String) ⟧LProd
  show {p , i} = curryLProd (Helper D p) (λ SH → fromMaybe "" ∘ showμ SH ∘ to)
