{-# OPTIONS --safe #-}
module Generics.Parametrized.Constructions.NoConfusion where

open import Generics.Prelude hiding (lookup)
open import Generics.Parametrized.Telescope
open import Generics.Parametrized.Desc3
open import Generics.Parametrized.HasDesc

open import Data.Fin.Properties as Fin
open import Data.Product.Properties
open import Data.Empty
open import Relation.Nullary


module NoConfusion {P} {I : ExTele P} {n ℓ} (D : Desc P I ℓ n) where

      mutual
        NoConfusion : ∀ {V} {ℓ} (C : CDesc P V I ℓ) {ℓ₂} {X : Σ[ P ⇒ I ] → Set (ℓ ⊔ ℓ₂)}
                    → ∀ {pv} → (x y : C⟦ C ⟧ ℓ₂ X pv) → Set (ℓ ⊔ ℓ₂)
        NoConfusion (var i) x y = x ≡ y
        NoConfusion (A ⊗ B) (xa , xb) (ya , yb) = NoConfusion A xa ya × NoConfusion B xb yb
        NoConfusion (π p S C) x y = NoConfusion′ p S C x y

        NoConfusion′ : ∀ {V} {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
                       {X : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄)}
                       (S : Σ[ P ⇒ V ] → Set ℓ₂)
                       (C : CDesc P (V ⊢ S) I ℓ₃)
                     → ∀ {pv} (x y : C⟦⟧b ℓ₄ e X S C pv) → Set (ℓ₁ ⊔ ℓ₄)
        NoConfusion′ {ε    } refl S C {pv} x y = x ≡ y
        NoConfusion′ {V ⊢ f} refl S C {pv} x y = x ≡ y


      mutual
        NoConfusionExtend : ∀ {V} {ℓ} (C : CDesc P V I ℓ) {ℓ₂} {X : Σ[ P ⇒ I ] → Set (ℓ ⊔ ℓ₂)}
                          → ∀ {pvi} → (x y : Extend C ℓ₂ X pvi) → Set (ℓ ⊔ ℓ₂)
        NoConfusionExtend (var i) x y = Lift _ ⊤
        NoConfusionExtend (π p S C) x y = NoConfusionExtend′ p S C x y
        NoConfusionExtend (A ⊗ B) (xa , xb) (ya , yb) = NoConfusion A xa ya × NoConfusionExtend B xb yb

        NoConfusionExtend′ : ∀ {V} {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
                             {X : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄)}
                             (S : Σ[ P ⇒ V ] → Set ℓ₂)
                             (C : CDesc P (V ⊢ S) I ℓ₃)
                           → ∀ {pvi} (x y : Extendb ℓ₄ e X S C pvi) → Set (ℓ₁ ⊔ ℓ₄)
        NoConfusionExtend′ {ε    } refl S C (xs , xd) (ys , yd) =
          Σ (xs ≡ ys) λ { refl → NoConfusionExtend C xd yd }
        NoConfusionExtend′ {V ⊢ f} refl S C (xs , xd) (ys , yd) =
          Σ (xs ≡ ys) λ { refl → NoConfusionExtend C xd yd }


      NoConf : ∀ {ℓ′} {X : Σ[ P ⇒ I ] → Set (ℓ ⊔ ℓ′)}
             → ∀ {pi} (x y : ⟦ D ⟧ ℓ′ X pi) → Set (ℓ ⊔ ℓ′)
      NoConf (kx , x) (ky , y) with kx Fin.≟ ky
      ... | yes refl = NoConfusionExtend (lookup D kx) x y
      ... | no _     = Lift _ ⊥

      mutual
        noConf-refl : ∀ {V} {ℓ} (C : CDesc P V I ℓ) {ℓ₂} {X : Σ[ P ⇒ I ] → Set (ℓ ⊔ ℓ₂)}
                    → ∀ {pvi} → (x : C⟦ C ⟧ ℓ₂ X pvi) → NoConfusion C x x
        noConf-refl (var i) x = refl
        noConf-refl (A ⊗ B) (xa , xb) = noConf-refl A xa , noConf-refl B xb
        noConf-refl (π p S C) x = noConf′-refl p S C x

        noConf′-refl : ∀ {V} {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
                       {X : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄)}
                       (S : Σ[ P ⇒ V ] → Set ℓ₂)
                       (C : CDesc P (V ⊢ S) I ℓ₃)
                     → ∀ {pvi} (x : C⟦⟧b ℓ₄ e X S C pvi) → NoConfusion′ e S C x x
        noConf′-refl {ε    } refl S C x = refl
        noConf′-refl {V ⊢ f} refl S C x = refl

      mutual
        noConfExtend-refl : ∀ {V} {ℓ} (C : CDesc P V I ℓ) {ℓ₂} {X : Σ[ P ⇒ I ] → Set (ℓ ⊔ ℓ₂)}
                          → ∀ {pvi} → (x : Extend C ℓ₂ X pvi) → NoConfusionExtend C x x
        noConfExtend-refl (var i) x = lift tt
        noConfExtend-refl (A ⊗ B) (xa , xb) = noConf-refl A xa , noConfExtend-refl B xb
        noConfExtend-refl (π p S C) x = noConfExtend′-refl p S C x

        noConfExtend′-refl : ∀ {V} {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
                                  {X : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄)}
                                  (S : Σ[ P ⇒ V ] → Set ℓ₂)
                                  (C : CDesc P (V ⊢ S) I ℓ₃)
                                → ∀ {pvi} (x : Extendb ℓ₄ e X S C pvi) → NoConfusionExtend′ e S C x x
        noConfExtend′-refl {ε    } refl S C (_ , x) = refl , noConfExtend-refl C x
        noConfExtend′-refl {V ⊢ f} refl S C (_ , x) = refl , noConfExtend-refl C x


      mutual
        noConf⟦⟧ : ∀ {V} {ℓ} (C : CDesc P V I ℓ) {ℓ₂} {X : Σ[ P ⇒ I ] → Set (ℓ ⊔ ℓ₂)}
                 → ∀ {pvi} {x y : C⟦ C ⟧ ℓ₂ X pvi} → NoConfusion C x y → x ≡ y
        noConf⟦⟧ (var i) nc = nc
        noConf⟦⟧ (A ⊗ B) (nca , ncb) = cong₂ _,_ (noConf⟦⟧ A nca) (noConf⟦⟧ B ncb)
        noConf⟦⟧ (π p S C) nc = noConf⟦⟧′ p S C nc

        noConf⟦⟧′ : ∀ {V} {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
                    {X : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄)}
                    (S : Σ[ P ⇒ V ] → Set ℓ₂)
                    (C : CDesc P (V ⊢ S) I ℓ₃)
                  → ∀ {pvi} {x y : C⟦⟧b ℓ₄ e X S C pvi} → NoConfusion′ e S C x y → x ≡ y
        noConf⟦⟧′ {ε    } refl S C nc = nc
        noConf⟦⟧′ {V ⊢ f} refl S C nc = nc


      mutual
        noConfExtend : ∀ {V} {ℓ} (C : CDesc P V I ℓ) {ℓ₂} {X : Σ[ P ⇒ I ] → Set (ℓ ⊔ ℓ₂)}
                     → ∀ {pvi} → {x y : Extend C ℓ₂ X pvi} → NoConfusionExtend C x y → x ≡ y
        noConfExtend (var i) {x = lift refl} {lift refl} nc = refl
        noConfExtend (A ⊗ B) (nca , ncb) = cong₂ _,_ (noConf⟦⟧ A nca) (noConfExtend B ncb)
        noConfExtend (π p S C) nc = noConfExtend′ p S C nc

        noConfExtend′ : ∀ {V} {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
                        {X : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄)}
                        (S : Σ[ P ⇒ V ] → Set ℓ₂)
                        (C : CDesc P (V ⊢ S) I ℓ₃)
                      → ∀ {pvi} {x y : Extendb ℓ₄ e X S C pvi} → NoConfusionExtend′ e S C x y → x ≡ y
        noConfExtend′ {ε    } refl S C (refl , nc) = cong (_ ,_) (noConfExtend C nc)
        noConfExtend′ {V ⊢ f} refl S C (refl , nc) = cong (_ ,_) (noConfExtend C nc)


      noConf : ∀ {ℓ′} {X : Σ[ P ⇒ I ] → Set (ℓ ⊔ ℓ′)}
             → ∀ {pi} {x y : ⟦ D ⟧ ℓ′ X pi} → x ≡ y → NoConf x y
      noConf {x = kx , x} {ky , _} refl with kx Fin.≟ ky
      ... | yes refl = noConfExtend-refl (lookup D kx) x
      ... | no kx≢kx = lift (kx≢kx refl) 


      noConf₂ : ∀ {ℓ′} {X : Σ[ P ⇒ I ] → Set (ℓ ⊔ ℓ′)}
              → ∀ {pi} {x y : ⟦ D ⟧ ℓ′ X pi} → NoConf x y → x ≡ y
      noConf₂ {x = kx , x} {ky , y} nc with kx Fin.≟ ky
      ... | yes refl = cong (kx ,_) (noConfExtend (lookup D kx) nc)
      ... | no kx≢ky = ⊥-elim (Lift.lower nc)


module Confusion {P} {I : ExTele P} {ℓ} {A : Curried′ P I ℓ} (H : HasDesc {P} {I} A) where

  open HasDesc H
  module NC = NoConfusion D

  NoConfusion : ∀ {pi} (x y : A′ pi) → Set ℓ
  NoConfusion x y = NC.NoConf (split x) (split y)

  noConfusion : ∀ {pi} {x y : A′ pi} → x ≡ y → NoConfusion x y
  noConfusion = NC.noConf ∘ cong split

  noConfusion₂ : ∀ {pi} {x y : A′ pi} → NoConfusion x y → x ≡ y
  noConfusion₂ {x = x} {y} = split-injective ∘ NC.noConf₂
