module Generics.Constructions.DecEq where

open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc
open import Generics.HasDesc
open import Data.Fin.Properties as Fin

open import Relation.Nullary.Decidable as Decidable
open import Data.Empty
open import Relation.Nullary
import Data.Product.Properties as Product
open import Relation.Binary using (DecidableEquality)

module _ {P} {I : ExTele P} {ℓ} {A : Curried′ P I ℓ} (H : HasDesc {P} {I} A) where

  open HasDesc H

  HelperExtend′ : ∀ {V ℓ} (C : CDesc P V I ℓ) → Σ[ P ⇒ V ] → Set (levelC C)
  HelperExtend′ (var i) pv = ⊤
  HelperExtend′ (π p S C) pv = Lift _ ⊥
  HelperExtend′ (A ⊗ B) pv = HelperExtend′ A pv × HelperExtend′ B pv

  HelperExtend : ∀ {V ℓ} (C : CDesc P V I ℓ) → Σ[ P ⇒ V ] → Set (levelC C)
  HelperExtend (var i) pv = ⊤
  HelperExtend (A ⊗ B) pv = HelperExtend′ A pv × HelperExtend B pv
  HelperExtend (π e S C) pv@(p , v) =
    DecidableEquality (S pv) × ((s : S pv) → HelperExtend C (p , v , s))

  levelHelper : ∀ {ℓ n} → Desc P I ℓ n → Level
  levelHelper [] = lzero
  levelHelper (C ∷ D) = levelC C ⊔ levelHelper D

  Helper : ∀ {ℓ n} (D : Desc P I ℓ n) → tel P tt → Set (levelHelper D)
  Helper [] p = ⊤
  Helper (C ∷ D) p = HelperExtend C (p , tt) × Helper D p


  lookupHelper : ∀ {ℓ n } {D : Desc P I ℓ n} {p} → Helper D p → (k : Fin n) → HelperExtend (lookup D k) (p , tt)
  lookupHelper {D = C ∷ D} (CH , DH) zero = CH
  lookupHelper {D = C ∷ D} (CH , DH) (suc k) = lookupHelper DH k


  module _ {p} (H : Helper D p) where
    mutual
      ≡-dec-⟦⟧ : ∀ {V} (C : CDesc P V I ℓ) {v : tel V p}
                → HelperExtend′ C (p , v)
                → DecidableEquality (C⟦ C ⟧ (levelTel I) (μ D) (p , v))
      ≡-dec-⟦⟧ (var i) H x y = ≡-dec-μ x y
      ≡-dec-⟦⟧ (A ⊗ B) (HA , HB) x y = Product.≡-dec (≡-dec-⟦⟧ A HA) (≡-dec-⟦⟧ B HB) x y
      ≡-dec-⟦⟧ (π p S C) ()

      ≡-dec-Extend : ∀ {V} (C : CDesc P V I ℓ) {v : tel V p} {i : tel I p}
                   → HelperExtend C (p , v)
                   → DecidableEquality (Extend C (levelTel I) (μ D) (p , v , i))
      ≡-dec-Extend (var i) H (lift refl) (lift refl) = yes refl
      ≡-dec-Extend (A ⊗ B) (HA , HB) x y = Product.≡-dec (≡-dec-⟦⟧ A HA) (≡-dec-Extend B HB) x y
      ≡-dec-Extend (π p S C) (DS , HC) x y = ≡-dec-Extend′ p S C DS HC x y

      ≡-dec-Extend′ : ∀ {V} {ℓ₁ ℓ₂}
                      (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ)
                      (S : Σ[ P ⇒ V ] → Set ℓ₂)
                      (C : CDesc P (V ⊢ S) I ℓ)
                      {v : tel V p} {i : tel I p}
                    → DecidableEquality (S (p , v)) 
                    → ((s : S (p , v)) → HelperExtend C (p , v , s))
                    → DecidableEquality (Extendb (levelTel I) e (μ D) S C (p , v , i))
      ≡-dec-Extend′ refl S C DS HC x y = Product.≡-dec DS (λ {s} → ≡-dec-Extend C (HC s)) x y 

      ≡-dec′ : ∀ {pi} → DecidableEquality (⟦ D ⟧ (levelTel I) (μ D) pi)
      ≡-dec′ (kx , x) (ky , y) with kx Fin.≟ ky
      ... | yes refl = map′ (cong (kx ,_)) (λ where refl → refl) (≡-dec-Extend {!lookup D kx!} {!!} {!!} {!!}) -- map′ (cong (kx ,_)) {!!} {!!}
      ... | no p     = no (p ∘ cong proj₁)

      ≡-dec-μ : ∀ {i : tel I p} → DecidableEquality (μ D (p , i))
      ≡-dec-μ ⟨ x ⟩ ⟨ y ⟩ = map′ (cong ⟨_⟩) (cong ⟨_⟩⁻¹) (≡-dec′ x y)


      ≡-dec : ∀ {i : tel I p} → DecidableEquality (A′ (p , i))
      ≡-dec x y = map′ (λ p → trans (sym (from∘to _)) (trans (cong from p) (from∘to _))) (cong to) (≡-dec-μ (to x) (to y))
