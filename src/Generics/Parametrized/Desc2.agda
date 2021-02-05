{-# OPTIONS --safe #-}
module Generics.Parametrized.Desc2 where

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

coerce : ∀ {a b} → a ≡ b → Set a → Set b
coerce refl = id

data CDesc (P : Telescope ⊤) (V I : ExTele P) : Setω where
  var : (((p , v) : Σ[ P ⇒ V ]) → tel I p) → CDesc P V I
  π   : ∀ {ℓ} (S : Σ[ P ⇒ V ] → Set ℓ) → CDesc P (V ⊢ S) I → CDesc P V I
  _⊗_ : (A B : CDesc P V I) → CDesc P V I

levelC : ∀ {P} {V I : ExTele P} → CDesc P V I → Level
levelC (var i) = lzero
levelC (π {ℓ} S C) = ℓ ⊔ levelC C
levelC (A ⊗ B) = levelC A ⊔ levelC B


C⟦_⟧ : ∀ {P} {V I : ExTele P} (C : CDesc P V I) ℓ
     → (Σ[ P ⇒ I ] → Set (ℓ ⊔ levelC C ⊔ levelTel I))
     → (Σ[ P ⇒ V ] → Set (ℓ ⊔ levelC C ⊔ levelTel I))
C⟦ var i ⟧ ℓ X pv@(p , v) = X (p , i pv)
C⟦ A ⊗ B ⟧ ℓ X pv = C⟦ A ⟧ (ℓ ⊔ levelC B) X pv × C⟦ B ⟧ (ℓ ⊔ levelC A) X pv
C⟦_⟧ {V = ε    } (π {ℓ′} S C) ℓ X pv@(p , v) = (s : S pv) → C⟦ C ⟧ (ℓ ⊔ ℓ′) X (p , s)
C⟦_⟧ {V = V ⊢ f} (π {ℓ′} S C) ℓ X pv@(p , v) = (s : S pv) → C⟦ C ⟧ (ℓ ⊔ ℓ′) X (p , v , s)


Extend : ∀ {P} {V I : ExTele P} (C : CDesc P V I) ℓ
       → (Σ[ P ⇒ I     ] → Set (ℓ ⊔ levelC C ⊔ levelTel I))
       → (Σ[ P ⇒ V & I ] → Set (ℓ ⊔ levelC C ⊔ levelTel I))
Extend {I = I} (var x) ℓ X pvi@(p , v , i)  = Lift (ℓ ⊔ levelTel I) (i ≡ x (p , v))
Extend (A ⊗ B) ℓ X pvi@(p , v , i) = C⟦ A ⟧ (ℓ ⊔ levelC B) X (p , v) × Extend B (ℓ ⊔ levelC A) X pvi
Extend {V = ε    } (π {ℓ′} S C) ℓ X pvi@(p , v , i) =
  Σ[ s ∈ S (p , v) ] Extend C (ℓ ⊔ ℓ′) X (p , s , i) 
Extend {V = V ⊢ f} (π {ℓ′} S C) ℓ X pvi@(p , v , i) =
  Σ[ s ∈ S (p , v) ] Extend C (ℓ ⊔ ℓ′) X (p , (v , s) , i)


data Desc P (I : ExTele P) : ℕ → Setω where
  []  : Desc P I 0
  _∷_ : ∀ {n} (C : CDesc P ε I) → Desc P I n → Desc P I (suc n)


lookup : ∀ {P} {I : ExTele P} {n} → Desc P I n → Fin n → CDesc P ε I
lookup (C ∷ CS) (zero ) = C
lookup (C ∷ CS) (suc k) = lookup CS k


levelD : ∀ {P} {I : ExTele P} {n} → Desc P I n → Level
levelD []      = lzero
levelD (C ∷ D) = levelC C ⊔ levelD D

data Coerce {b} : ∀ {a} → a ≡ b → Set a → Set b where
  coerce′ : ∀ {A} → A → Coerce refl A

uncoerce : ∀ {a b} {p : a ≡ b} {A : Set a} → coerce p A → A
uncoerce {p = refl} x = x

lC≤lD : ∀ {P} {I : ExTele P} {n} (D : Desc P I n) (k : Fin n)
      → levelD D ≡ levelD D ⊔ levelC (lookup D k)
lC≤lD (C ∷ D) zero    = refl
lC≤lD (C ∷ D) (suc k) = cong (levelC C ⊔_) (lC≤lD D k)

⟦_⟧ : ∀ {P} {I : ExTele P} {n} (D : Desc P I n)
    → (Σ[ P ⇒ I ] → Set (levelD D ⊔ levelTel I))
    → (Σ[ P ⇒ I ] → Set (levelD D ⊔ levelTel I))
⟦_⟧ {I = I} {n} D X pi@(p , i) = Σ[ k ∈ Fin n ] 
  let eq = cong (levelTel I ⊔_) (lC≤lD D k)
      X′ = coerce eq ∘ X
  in coerce (sym eq) (Extend (lookup D k) (levelD D) X′ (p , tt , i))


data μ {P} {I : ExTele P} {n} (D : Desc P I n) (pi : Σ[ P ⇒ I ])
     : Set (levelD D ⊔ levelTel I) where
  ⟨_⟩ : ⟦ D ⟧ (μ D) (proj₁ pi , proj₂ pi) → μ D pi


All⟦⟧   : ∀ {P} {V I : ExTele P} {C : CDesc P V I} {ℓ}
          {X  : Σ[ P ⇒ I ] → Set (ℓ ⊔ levelC C ⊔ levelTel I)} {c}
          (Pr : ∀ {pi} → X pi → Set c)
        → ∀ {pv} → C⟦ C ⟧ ℓ X pv → Set (ℓ ⊔ levelC C ⊔ c)
All⟦⟧ {C = var i} {ℓ} {c = c} Pr x = Lift (ℓ ⊔ c) (Pr x)
All⟦⟧ {C = A ⊗ B} Pr (⟦A⟧ , ⟦B⟧) = All⟦⟧ {C = A} Pr ⟦A⟧ × All⟦⟧ {C = B} Pr ⟦B⟧
All⟦⟧ {V = ε    } {C = π {ℓ′} S C} Pr {pv@(p , v)} x = (s : S (p , v)) → All⟦⟧ {C = C} Pr (x s)
All⟦⟧ {V = V ⊢ f} {C = π {ℓ′} S C} Pr {pv@(p , v)} x = (s : S (p , v)) → All⟦⟧ {C = C} Pr (x s)


AllExtend : ∀ {P} {V I : ExTele P} {ℓ} {C : CDesc P V I}
            {X  : Σ[ P ⇒ I ] → Set (ℓ ⊔ levelC C ⊔ levelTel I)} {c}
            (Pr : ∀ {pi} → X pi → Set c)
          → ∀ {pvi} → Extend C ℓ X pvi → Set (ℓ ⊔ levelC C ⊔ c)
AllExtend {C = var i} Pr x = Lift _ ⊤
AllExtend {C = A ⊗ B} Pr (⟦A⟧ , EB) = All⟦⟧ {C = A} Pr ⟦A⟧ × AllExtend {C = B} Pr EB
AllExtend {V = ε    } {C = π {ℓ′} S C} Pr (s , EC) = AllExtend {C = C} Pr EC
AllExtend {V = V ⊢ f} {C = π {ℓ′} S C} Pr (s , EC) = AllExtend {C = C} Pr EC

All : ∀ {P} {I : ExTele P} {n} (D : Desc P I n) {c}
      (Pr : ∀ {pi} → μ D pi → Set c)
    → ∀ {pi} → μ D pi → Set (levelD D ⊔ c)
All {I = I} D {c} Pr ⟨ k , x ⟩ =
  let eq = cong (levelTel I ⊔_) (lC≤lD D k)
      x′  = uncoerce {p = sym eq} x
      X′  = coerce eq ∘ μ D
      Pr′ {pi} = Pr {pi} ∘ uncoerce {p = eq}
      S  = AllExtend {C = lookup D k} {X = X′} Pr′ x′
  in coerce (cong (c ⊔_) (sym (lC≤lD D k))) S





      

