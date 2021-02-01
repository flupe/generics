{-# OPTIONS --safe #-}
module Generics.Parametrized.Desc3 where

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
a ≤ℓ b = b ≡ a ⊔ b


data CDesc (P : Telescope ⊤) (V I : ExTele P) ℓ : Setω where
  var : (((p , v) : Σ[ P ⇒ V ]) → tel I p) → CDesc P V I ℓ
  π   : ∀ {ℓ′} (p : ℓ′ ≤ℓ ℓ) (S : Σ[ P ⇒ V ] → Set ℓ′) → CDesc P (V ⊢ S) I ℓ → CDesc P V I ℓ
  _⊗_ : (A B : CDesc P V I ℓ) → CDesc P V I ℓ


mutual
  C⟦_⟧ : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂} (C : CDesc P V I ℓ₁)
       → (Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂))
       → Σ[ P ⇒ V ] → Set (ℓ₁ ⊔ ℓ₂)
  C⟦ var i ⟧ X pv@(p , _) = X (p , i pv)
  C⟦_⟧ {ℓ₂ = ℓ₂} (A ⊗ B) X pv = C⟦_⟧ {ℓ₂ = ℓ₂} A X pv × C⟦_⟧ {ℓ₂ = ℓ₂} B X pv
  C⟦_⟧ {ℓ₂ = ℓ₂} (π {ℓ} e S C) X pv@(p , v) = C⟦⟧b {ℓ₂ = ℓ} {ℓ₄ = ℓ₂} e X S C pv

  C⟦⟧b : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
       → ℓ₁ ≡ ℓ₂ ⊔ ℓ₃
       → (Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄))
       → (S : Σ[ P ⇒ V ] → Set ℓ₂)
       → CDesc P (V ⊢ S) I ℓ₃
       → Σ[ P ⇒ V ] → Set (ℓ₁ ⊔ ℓ₄)
  C⟦⟧b {V = ε    } {ℓ₄ = ℓ₄} refl X S C pv@(p , v) = (s : S pv) → C⟦_⟧ {ℓ₂ = ℓ₄} C X (p , s)
  C⟦⟧b {V = V ⊢ f} {ℓ₄ = ℓ₄} refl X S C pv@(p , v) = (s : S pv) → C⟦_⟧ {ℓ₂ = ℓ₄} C X (p , v , s)


mutual
  Extend : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂} (C : CDesc P V I ℓ₁)
         → (Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂))
         → Σ[ P ⇒ V & I ] → Set (ℓ₁ ⊔ ℓ₂ ⊔ levelTel I)
  Extend {I = I} {ℓ₁} {ℓ₂} (var x) X pvi@(p , v , i) = Lift (ℓ₁ ⊔ ℓ₂ ⊔ levelTel I) (i ≡ x (p , v))
  Extend {ℓ₂ = ℓ₂} (A ⊗ B)   X pvi@(p , v , _) = C⟦_⟧ {ℓ₂ = ℓ₂} A X (p , v) × Extend {ℓ₂ = ℓ₂} B X pvi
  Extend {ℓ₂ = ℓ₂} (π e S C) X pvi@(p , v , i) = Extendb {ℓ₄ = ℓ₂} e X S C pvi

  Extendb : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
          → ℓ₁ ≡ ℓ₂ ⊔ ℓ₃
          → (Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄))
          → (S : Σ[ P ⇒ V ] → Set ℓ₂)
          → CDesc P (V ⊢ S)  I ℓ₃
          → Σ[ P ⇒ V & I ] → Set (ℓ₁ ⊔ ℓ₄ ⊔ levelTel I)
  Extendb {V = ε    } {ℓ₄ = ℓ₄} refl X S C pvi@(p , v , i) =
    Σ[ s ∈ S (p , v) ] Extend {ℓ₂ = ℓ₄} C X (p , s , i)
  Extendb {V = V ⊢ f} {ℓ₄ = ℓ₄} refl X S C pvi@(p , v , i) =
    Σ[ s ∈ S (p , v) ] Extend {ℓ₂ = ℓ₄} C X (p , (v , s) , i)


data Desc P (I : ExTele P) ℓ : ℕ → Setω where
  []  : Desc P I ℓ 0
  _∷_ : ∀ {n} (C : CDesc P ε I ℓ) (D : Desc P I ℓ n) → Desc P I ℓ (suc n)


lookup : ∀ {P} {I : ExTele P} {ℓ n} → Desc P I ℓ n → Fin n → CDesc P ε I ℓ
lookup (C ∷ D) (zero ) = C
lookup (C ∷ D) (suc k) = lookup D k



⟦_⟧ : ∀ {P} {I : ExTele P} {ℓ n} (D : Desc P I ℓ n)
    → (Σ[ P ⇒ I ] → Set (ℓ ⊔ levelTel I))
    → Σ[ P ⇒ I ] → Set (ℓ ⊔ levelTel I)
⟦_⟧ {P} {I} {ℓ} {n} D X (p , i) = Σ[ k ∈ Fin n ] Extend {ℓ₂ = levelTel I} (lookup D k) X (p , tt , i)


data μ {P} {I : ExTele P} {ℓ n} (D : Desc P I ℓ n) (pi : Σ[ P ⇒ I ]) : Set (ℓ ⊔ levelTel I) where
  ⟨_⟩ : ⟦ D ⟧ (μ D) pi → μ D pi


mutual
  All⟦⟧ : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂} (C : CDesc P V I ℓ₁)
          (X  : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂)) {c}
          (Pr : ∀ {pi} → X pi → Set c)
        → ∀ {pv} → C⟦_⟧ {ℓ₂ = ℓ₂} C X pv → Set (c ⊔ ℓ₁)
  All⟦⟧ {ℓ₁ = ℓ} (var i) X {c} Pr x   = Lift (ℓ ⊔ c) (Pr x)
  All⟦⟧ (A ⊗ B) X Pr (⟦A⟧ , ⟦B⟧) = All⟦⟧ A X Pr ⟦A⟧ × All⟦⟧ B X Pr ⟦B⟧
  All⟦⟧ (π e S C) X Pr x = All⟦⟧b e X S C Pr x


  All⟦⟧b : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
        (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
        (X : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄)) {c}
        (S : Σ[ P ⇒ V ] → Set ℓ₂)
        (C : CDesc P (V ⊢ S) I ℓ₃)
        (Pr : ∀ {pi} → X pi → Set c)
       → ∀ {pv} → C⟦⟧b {ℓ₄ = ℓ₄} e X S C pv → Set (c ⊔ ℓ₁)
  All⟦⟧b {V = ε    } refl X S C Pr {pv} x = (s : S pv) → All⟦⟧ C X Pr (x s)
  All⟦⟧b {V = V ⊢ f} refl X S C Pr {pv} x = (s : S pv) → All⟦⟧ C X Pr (x s)


mutual
  AllExtend : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂} (C : CDesc P V I ℓ₁)
              (X  : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂)) {c}
              (Pr : ∀ {pi} → X pi → Set c)
            → ∀ {pvi} → Extend {ℓ₂ = ℓ₂} C X pvi → Set (c ⊔ ℓ₁)
  AllExtend (var i) X Pr x   = Lift _ ⊤
  AllExtend (A ⊗ B) X Pr (⟦A⟧ , EB) = All⟦⟧ A X Pr ⟦A⟧ × AllExtend B X Pr EB
  AllExtend (π e S C) X Pr x = AllExtendb e X S C Pr x

  AllExtendb : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
               (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
               (X : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄)) {c}
               (S : Σ[ P ⇒ V ] → Set ℓ₂)
               (C : CDesc P (V ⊢ S) I ℓ₃)
               (Pr : ∀ {pi} → X pi → Set c)
             → ∀ {pvi} → Extendb {ℓ₄ = ℓ₄} e X S C pvi → Set (c ⊔ ℓ₃)
  AllExtendb {V = ε    } refl X S C Pr (s , d) = AllExtend C X Pr d
  AllExtendb {V = V ⊢ f} refl X S C Pr (s , d) = AllExtend C X Pr d


All : ∀ {P} {I : ExTele P} {ℓ n} (D : Desc P I ℓ n) {c}
      (Pr : ∀ {pi} → μ D pi → Set c)
    → ∀ {pi} → μ D pi → Set (c ⊔ ℓ)
All D Pr ⟨ k , x ⟩ = AllExtend (lookup D k) (μ D) Pr x
