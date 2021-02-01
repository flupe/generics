{-# OPTIONS --safe #-}
module Generics.Parametrized.Desc4 where

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Data.Unit
open import Data.Product
open import Data.List.Base hiding (lookup; [_]; all)
open import Function.Base
open import Data.Fin.Base hiding (lift)
open import Data.Nat.Base hiding (_⊔_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Level using (Lift; lift)

open import Generics.Parametrized.Telescope


_≤ℓ_ : (a b : Level) → Set
a ≤ℓ b = a ⊔ b ≡ b


data CDesc (P : Telescope ⊤) (V I : ExTele P) : Setω where
  var : (((p , v) : Σ[ P ⇒ V ]) → tel I p) → CDesc P V I
  _⊗_ : (A B : CDesc P V I) → CDesc P V I
  π   : ∀ {ℓ} (S : Σ[ P ⇒ V ] → Set ℓ) → CDesc P (V ⊢ S) I → CDesc P V I


levelC : ∀ {P} {V I : ExTele P} → CDesc P V I → Level
levelC (var i) = lzero
levelC (A ⊗ B) = levelC A ⊔ levelC B
levelC (π {ℓ} S C) = ℓ ⊔ levelC C


C⟦_⟧ : ∀ {P} {V I : ExTele P} (C : CDesc P V I) {ℓ₁ ℓ₂ ℓ₃}
     → ℓ₁ ≡ ℓ₂ ⊔ ℓ₃
     → (Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ levelTel I))
     → Σ[ P ⇒ V ] → Set (ℓ₁ ⊔ levelTel I)
C⟦ var i ⟧ refl X x = {!!}
C⟦ A ⊗ B ⟧ p X x = {!!}
C⟦ π S C ⟧ p X x = {!!}

{-
mutual
  C⟦_⟧ : ∀ {P} {V I : ExTele P} {ℓ} (C : CDesc P V I)
       → (Σ[ P ⇒ I ] → Set (ℓ ⊔ levelTel I))
       → Σ[ P ⇒ V ] → Set (ℓ ⊔ levelTel I)
  C⟦ var i ⟧ X pv@(p , _) = X (p , i pv)
  C⟦ A ⊗ B ⟧ X pv = C⟦ A ⟧ X pv × C⟦ B ⟧ X pv
  C⟦_⟧ {I} (π e S C) X pv@(p , v) = C⟦⟧b (sym e) X S C pv



  C⟦⟧b : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂ ℓ₃}
        → ℓ₁ ≡ ℓ₂ ⊔ ℓ₃
        → (Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ levelTel I))
        → (S : Σ[ P ⇒ V ] → Set ℓ₂)
        → CDesc P (V ⊢ S)  I ℓ₃
        → Σ[ P ⇒ V ] → Set (ℓ₁ ⊔ levelTel I)
  C⟦⟧b {V = ε    } refl X S C pv@(p , v) = (s : S pv) → C⟦ C ⟧ X (p , s)
  C⟦⟧b {V = V ⊢ f} refl X S C pv@(p , v) = (s : S pv) → C⟦ C ⟧ X (p , v , s)


mutual
  Extend : ∀ {P} {V I : ExTele P} {ℓ} (C : CDesc P V I ℓ)
         → (Σ[ P ⇒ I ] → Set (ℓ ⊔ levelTel I))
         → Σ[ P ⇒ V & I ] → Set (ℓ ⊔ levelTel I)
  Extend {I = I} {ℓ} (var x) X pvi@(p , v , i) = Lift (ℓ ⊔ levelTel I) (i ≡ x (p , v))
  Extend (A ⊗ B)   X pvi@(p , v , _) = C⟦ A ⟧ X (p , v) × Extend B X pvi
  Extend (π e S C) X pvi@(p , v , i) = Extendb (sym e) X S C pvi

  Extendb : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂ ℓ₃}
          → ℓ₁ ≡ ℓ₂ ⊔ ℓ₃
          → (Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ levelTel I))
          → (S : Σ[ P ⇒ V ] → Set ℓ₂)
          → CDesc P (V ⊢ S)  I ℓ₃
          → Σ[ P ⇒ V & I ] → Set (ℓ₁ ⊔ levelTel I)
  Extendb {V = ε    } refl X S C pvi@(p , v , i) = Σ[ s ∈ S (p , v) ] Extend C X (p , s , i)
  Extendb {V = V ⊢ f} refl X S C pvi@(p , v , i) = Σ[ s ∈ S (p , v) ] Extend C X (p , (v , s) , i)


data Desc P (I : ExTele P) ℓ : ℕ → Setω where
  []  : Desc P I ℓ 0
  _∷_ : ∀ {n} (C : CDesc P ε I ℓ) (D : Desc P I ℓ n) → Desc P I ℓ (suc n)


lookup : ∀ {P} {I : ExTele P} {ℓ n} → Desc P I ℓ n → Fin n → CDesc P ε I ℓ
lookup (C ∷ D) (zero ) = C
lookup (C ∷ D) (suc k) = lookup D k

⟦_⟧ : ∀ {P} {I : ExTele P} {ℓ n} (D : Desc P I ℓ n)
    → (Σ[ P ⇒ I ] → Set (ℓ ⊔ levelTel I))
    → Σ[ P ⇒ I ] → Set (ℓ ⊔ levelTel I)
⟦_⟧ {n = n} D X (p , i) = Σ[ k ∈ Fin n ] Extend (lookup D k) X (p , tt , i)


data μ {P} {I : ExTele P} {ℓ n} (D : Desc P I ℓ n) (pi : Σ[ P ⇒ I ]) : Set (ℓ ⊔ levelTel I) where
  ⟨_⟩ : ⟦ D ⟧ (μ D) pi → μ D pi


mutual
  All⟦⟧ : ∀ {P} {V I : ExTele P} {ℓ} (C : CDesc P V I ℓ)
          (X  : Σ[ P ⇒ I ] → Set (ℓ ⊔ levelTel I)) {c}
          (Pr : ∀ {pi} → X pi → Set c)
        → ∀ {pv} → C⟦ C ⟧ X pv → Set (c ⊔ ℓ)
  All⟦⟧ {ℓ = ℓ} (var i) X {c} Pr x   = Lift (ℓ ⊔ c) (Pr x)
  All⟦⟧ (A ⊗ B) X Pr (⟦A⟧ , ⟦B⟧) = All⟦⟧ A X Pr ⟦A⟧ × All⟦⟧ B X Pr ⟦B⟧
  All⟦⟧ (π e S C) X Pr x = All⟦⟧b (sym e) X S C Pr x


  All⟦⟧b : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂ ℓ₃}
        (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
        (X : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ levelTel I)) {c}
        (S : Σ[ P ⇒ V ] → Set ℓ₂)
        (C : CDesc P (V ⊢ S) I ℓ₃)
        (Pr : ∀ {pi} → X pi → Set c)
       → ∀ {pv} → C⟦⟧b e X S C pv → Set (c ⊔ ℓ₁)
  All⟦⟧b {V = ε    } refl X S C Pr {pv} x = (s : S pv) → All⟦⟧ C X Pr (x s)
  All⟦⟧b {V = V ⊢ f} refl X S C Pr {pv} x = (s : S pv) → All⟦⟧ C X Pr (x s)


mutual
  AllExtend : ∀ {P} {V I : ExTele P} {ℓ} (C : CDesc P V I ℓ)
              (X  : Σ[ P ⇒ I ] → Set (ℓ ⊔ levelTel I)) {c}
              (Pr : ∀ {pi} → X pi → Set c)
            → ∀ {pvi} → Extend C X pvi → Set (c ⊔ ℓ)
  AllExtend (var i) X Pr x   = Lift _ ⊤
  AllExtend (A ⊗ B) X Pr (⟦A⟧ , EB) = All⟦⟧ A X Pr ⟦A⟧ × AllExtend B X Pr EB
  AllExtend (π e S C) X Pr x = AllExtendb (sym e) X S C Pr x

  AllExtendb : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂ ℓ₃}
               (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
               (X : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ levelTel I)) {c}
               (S : Σ[ P ⇒ V ] → Set ℓ₂)
               (C : CDesc P (V ⊢ S) I ℓ₃)
               (Pr : ∀ {pi} → X pi → Set c)
             → ∀ {pvi} → Extendb e X S C pvi → Set (c ⊔ ℓ₃)
  AllExtendb {V = ε    } refl X S C Pr (s , d) = AllExtend C X Pr d
  AllExtendb {V = V ⊢ f} refl X S C Pr (s , d) = AllExtend C X Pr d


All : ∀ {P} {I : ExTele P} {ℓ n} (D : Desc P I ℓ n) {c}
      (Pr : ∀ {pi} → μ D pi → Set c)
    → ∀ {pi} → μ D pi → Set (c ⊔ ℓ)
All D Pr ⟨ k , x ⟩ = AllExtend (lookup D k) (μ D) Pr x


module Induction {P} {I : ExTele P} {ℓ n} (D : Desc P I ℓ n)
                 {c} (Pr : ∀ {pi} → μ D pi → Set c) where

  module _ (f : ∀ {pi} (x : μ D pi) → All D Pr x → Pr x) where

    mutual 
      all⟦⟧ : {V : ExTele P} (C : CDesc P V I ℓ)
            → ∀ {pv} (x : C⟦ C ⟧ (μ D) pv) → All⟦⟧ C (μ D) Pr x
      all⟦⟧ (var i) x = lift (f x (all x))
      all⟦⟧ (A ⊗ B) (⟦A⟧ , ⟦B⟧) = all⟦⟧ A ⟦A⟧ , all⟦⟧ B ⟦B⟧
      all⟦⟧ (π e S C) x = all⟦⟧b (sym e) S C x

      all⟦⟧b : ∀ {V : ExTele P} {ℓ₁ ℓ₂}
               (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ)
               (S : Σ[ P ⇒ V ] → Set ℓ₂)
               (C : CDesc P (V ⊢ S) I ℓ)
             → ∀ {pv} (x : C⟦⟧b e (μ D) S C pv) →  All⟦⟧b e (μ D) S C Pr x
      all⟦⟧b {V = ε    } refl S C x s = all⟦⟧ C (x s)
      all⟦⟧b {V = V ⊢ f} refl S C x s = all⟦⟧ C (x s)

      allExtend : {V : ExTele P} (C : CDesc P V I ℓ)
                → ∀ {pvi} (x : Extend C (μ D) pvi) → AllExtend C (μ D) Pr x
      allExtend (var i) x = lift tt
      allExtend (A ⊗ B) (⟦A⟧ , EB) = all⟦⟧ A ⟦A⟧ , allExtend B EB
      allExtend (π e S C) x = allExtendb (sym e) S C x

      allExtendb : ∀ {V : ExTele P} {ℓ₁ ℓ₂}
                   (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ)
                   (S : Σ[ P ⇒ V ] → Set ℓ₂)
                   (C : CDesc P (V ⊢ S) I ℓ)
                 → ∀ {pvi} (x : Extendb e (μ D) S C pvi) → AllExtendb e (μ D) S C Pr x
      allExtendb {ε    } refl S C (s , EC) = allExtend C EC
      allExtendb {V ⊢ f} refl S C (s , EC) = allExtend C EC

      all : ∀ {pi} (x : μ D pi) → All D Pr x
      all ⟨ k , x ⟩ = allExtend (lookup D k) x

      ind : ∀ {pi} (x : μ D pi) → Pr x
      ind x = f x (all x)

-}
