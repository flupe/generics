{-# OPTIONS --safe --without-K #-}
module Generics.Parametrized.Desc where

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Data.Unit
open import Data.Product
open import Data.List.Base hiding (lookup; [_])
open import Function.Base
open import Data.Fin.Base hiding (lift)
open import Data.Nat.Base hiding (_⊔_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Level using (Lift; lift)

open import Generics.Parametrized.Telescope


_≤ℓ_ : (a b : Level) → Set
a ≤ℓ b = a ⊔ b ≡ b

_≥ℓ_ : (a b : Level) → Set
a ≥ℓ b = a ≡ a ⊔ b


data CDesc (P : Telescope ⊤) (V : ExTele P) (I : ExTele P) ℓ : Setω where
  var : (((p , v) : Σ[ P ⇒ V ]) → tel I p) → CDesc P V I ℓ
  π   : ∀ {ℓ′} → ℓ ≥ℓ ℓ′ → (S : Σ[ P ⇒ V ] → Set ℓ′) → CDesc P (V ⊢ S) I ℓ → CDesc P V I ℓ
  _⊗_ : (A B : CDesc P V I ℓ) → CDesc P V I ℓ


shift : ∀ {a b} → a ≡ b → Set a → Set b
shift refl x = x

unshift : ∀ {a b} {p : a ≡ b} {A : Set a} → shift p A → A
unshift {p = refl} x = x

≤ℓ-trans : ∀ {a b c} → a ≤ℓ b → b ≤ℓ c → a ≤ℓ c
≤ℓ-trans p q rewrite sym q | sym p = refl

≤ℓ⊔ : ∀ a b → a ≤ℓ (a ⊔ b)
≤ℓ⊔ a b = refl


C⟦_⟧ : ∀ {P} {V I : ExTele P} {ℓ} (C : CDesc P V I ℓ)
     → (Σ[ P ⇒ I ] → Set (ℓ ⊔ levelTel I))
     → (Σ[ P ⇒ V ] → Set (ℓ ⊔ levelTel I))
C⟦ var i   ⟧ X pv@(p , _) = X (p , (i pv))
C⟦ A ⊗ B   ⟧ X pv = C⟦ A ⟧ X pv × C⟦ B ⟧ X pv
C⟦_⟧ {V = ε    } {I} (π ℓ≥ℓ′ S C) X pv@(p , v) =
  shift (cong (_⊔ levelTel I) (sym ℓ≥ℓ′)) ((s : S pv) → C⟦ C ⟧ X (p , s))
C⟦_⟧ {V = V ⊢ f} {I} (π ℓ≥ℓ′ S C) X pv@(p , v) =
  shift (cong (_⊔ levelTel I) (sym ℓ≥ℓ′)) ((s : S pv) → C⟦ C ⟧ X (p , v , s))


Extend : ∀ {P} {V I : ExTele P} {ℓ} (C : CDesc P V I ℓ)
       → (Σ[ P ⇒ I     ] → Set (ℓ ⊔ levelTel I))
       → (Σ[ P ⇒ V & I ] → Set (ℓ ⊔ levelTel I))
Extend {I = I} {ℓ} (var x) X (p , v , i) = Lift (ℓ ⊔ levelTel I) (i ≡ x (p , v))
Extend (A ⊗ B) X pvi@(p , v , i) = C⟦ A ⟧ X (p , v) × Extend B X pvi
Extend {V = ε    } {I} (π ℓ≥ℓ′ S C) X pvi@(p , v , i) =
  shift (cong (_⊔ levelTel I) (sym ℓ≥ℓ′)) (Σ[ s ∈ S (p , v) ] Extend C X (p , s , i))
Extend {V = V ⊢ f} {I} (π ℓ≥ℓ′ S C) X pvi@(p , v , i) = 
  shift (cong (_⊔ levelTel I) (sym ℓ≥ℓ′)) (Σ[ s ∈ S (p , v) ] Extend C X (p , (v , s) , i))


data Desc P (I : ExTele P) ℓ : ℕ → Setω where
  []  : Desc P I ℓ 0
  _∷_ : ∀ {n} (C : CDesc P ε I ℓ) (CS : Desc P I ℓ n) → Desc P I ℓ (suc n)


lookup : ∀ {P} {I : ExTele P} {ℓ} {n} → Desc P I ℓ n → Fin n → CDesc P ε I ℓ
lookup (C ∷ CS) (zero ) = C
lookup (C ∷ CS) (suc k) = lookup CS k


⟦_⟧ : ∀ {P} {I : ExTele P} {ℓ n} (D : Desc P I ℓ n)
    → (Σ[ P ⇒ I ] → Set (ℓ ⊔ levelTel I))
    → (Σ[ P ⇒ I ] → Set (ℓ ⊔ levelTel I))
⟦_⟧ {n = n} D X pi@(p , i) = Σ[ k ∈ Fin n ] Extend (lookup D k) X (p , tt , i)


data μ {P} {I : ExTele P} {ℓ} {n} (D : Desc P I ℓ n) (pi : Σ[ P ⇒ I ])
     : Set (ℓ ⊔ levelTel I) where
  ⟨_⟩ : ⟦ D ⟧ (μ D) (proj₁ pi , proj₂ pi) → μ D pi


All⟦⟧   : ∀ {P} {V I : ExTele P} {ℓ} {C : CDesc P V I ℓ}
          {X  : Σ[ P ⇒ I ] → Set (ℓ ⊔ levelTel I)} {c}
          (Pr : ∀ {pi} → X pi → Set c)
        → ∀ {pi} → C⟦ C ⟧ X pi → Set (ℓ ⊔ c)
All⟦⟧ {ℓ = ℓ} {C = var i} {c = c} Pr x = Lift (ℓ ⊔ c) (Pr x)
All⟦⟧ {C = A ⊗ B} Pr (⟦A⟧ , ⟦B⟧) = All⟦⟧ {C = A} Pr ⟦A⟧ × All⟦⟧ {C = B} Pr ⟦B⟧
All⟦⟧ {V = ε} {ℓ = ℓ} {C = π {ℓ′} ℓ≥ℓ′ S C} {X} {c = c} Pr {pv@(p , v)} x =
  let x′ = unshift {A = (s : S pv) → C⟦ C ⟧ X (p , s)} x
  in shift (cong (_⊔ c) (sym ℓ≥ℓ′)) ((s : S (p , tt)) → All⟦⟧ {C = C} Pr (x′ s))

All⟦⟧ {V = V ⊢ f} {C = π ℓ≥ℓ′ S C} {X} {c} Pr {pv@(p , v)} x = 
  let x′ = unshift {A = (s : S pv) → C⟦ C ⟧ X (p , v , s)} x
  in shift (cong (_⊔ c) (sym ℓ≥ℓ′)) ((s : S (p , v)) → All⟦⟧ {C = C} Pr (x′ s))


AllExtend : ∀ {P} {V I : ExTele P} {ℓ} {C : CDesc P V I ℓ}
            {X  : Σ[ P ⇒ I ] → Set (ℓ ⊔ levelTel I)} {c}
            (Pr : ∀ {pi} → X pi → Set c)
          → ∀ {pi} → Extend C X pi → Set (ℓ ⊔ levelTel I ⊔ c)
AllExtend {C = var i      } Pr x = Lift _ ⊤
AllExtend {C = A ⊗ B      } Pr (C⟦A⟧ , EB) = All⟦⟧ {C = A} Pr C⟦A⟧ × AllExtend {C = B} Pr EB
AllExtend {V = ε    } {C = π ℓ≥ℓ′ S C} {X = X} Pr {pi@(p , v , i)} x =
  let (x′ , d) = unshift {A = Σ[ s ∈ S (p , v) ] Extend C X (p , s , i)} x
  in AllExtend {C = C} Pr d
AllExtend {V = V ⊢ f} {C = π ℓ≥ℓ′ S C} {X = X} Pr {pi@(p , v , i)} x =
  let (x′ , d) = unshift {A = Σ[ s ∈ S (p , v) ] Extend C X (p , (v , s) , i)} x
  in AllExtend {C = C} Pr d


All : ∀ {P} {I : ExTele P} {ℓ n} (D : Desc P I ℓ n) {c}
      (Pr : ∀ {pi} → μ D pi → Set c)
    → ∀ {pi} → μ D pi → Set (ℓ ⊔ levelTel I ⊔ c)
All {P} {V} {I} D Pr ⟨ k , x ⟩ = AllExtend {C = lookup D k} Pr x
