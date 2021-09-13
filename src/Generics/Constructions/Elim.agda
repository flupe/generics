{-# OPTIONS --safe #-}

module Generics.Constructions.Elim where

open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc
open import Generics.HasDesc

import Generics.Constructions.Induction as Induction


module Elim {P} {I : ExTele P} {ℓ} {A : Indexed P I ℓ} (H : HasDesc {P} {I} {ℓ} A)
            {c} (Pr : Pred P I (uncurry P I A) c) where

      open HasDesc H

      Pr′ : {p : ⟦ P , I ⟧xtel} → uncurry P I A p → Set c
      Pr′ {p} = unpred P I _ Pr p

      -- induction hypothesis: every recursive occurence satisfies Pr
      IH : ∀ (C : Desc P ε I ℓ) {pi} → Extend C ℓ A′ pi → Set (ℓ ⊔ c)
      IH C x = AllExtend C A′ Pr′ x

      Method : Fin n → Set (levelOfTel P ⊔ levelOfTel I ⊔ ℓ ⊔ c)
      Method k = ∀ {pi} {x : Extend (lookup D k)  ℓ A′ pi}
               → IH (lookup D k) x
               → Pr′ (constr (k , x))

      Methods : Sets _
      Methods = Method

      Pr″ : ∀ {pi} → μ D pi → Set c
      Pr″ = Pr′ ∘ from

      module Ind = Induction Pr″

      module _ (methods : Els Methods) where

         to-hypothesis : ∀ {p} (X : μ D p) → All D Pr″ X → Pr″ X
         to-hypothesis {p} ⟨ k , x ⟩ all
           rewrite sym (constr-coh (k , x)) = method (mapAllExtend C from Pr′ all)
           where
             C = lookup D k

             method : ∀ {pi} {x : Extend C ℓ A′ pi} → IH C x → Pr′ (constr (k , x))
             method = methods k

         elim : ∀ {pi} (x : A′ pi) → Pr′ x
         elim x rewrite sym (from∘to x) = Ind.ind to-hypothesis (to x)

module _ {P} {I : ExTele P} {ℓ} {A : Indexed P I ℓ} (H : HasDesc {P} {I} {ℓ} A)
         {c} (Pr : Pred P I (uncurry P I A) c)
         (funext : ∀ {a b} → Extensionality a b) where

  open HasDesc H
  open Elim H Pr

  level⟦⟧ : ∀ {V} (C : Desc P V I ℓ) → Level → Level
  level⟦⟧ (var x) c = c
  level⟦⟧ (π {ℓ} p i S C) c = ℓ ⊔ level⟦⟧ C c
  level⟦⟧ (A ⊗ B) c = level⟦⟧ A c ⊔ level⟦⟧ B c

  level : ∀ {V} (C : Desc P V I ℓ) → Level
  level (var x) = c
  level (π {ℓ} p i S C) = ℓ ⊔ level C
  level (A ⊗ B) = level⟦⟧ A ℓ ⊔ level⟦⟧ A c ⊔ level B

  mutual

    motive⟦⟧ : ∀ {V} (C : Desc P V I ℓ) → ⟦ P , V ⟧xtel → Set (level⟦⟧ C ℓ)
    motive⟦⟧ (var x) pv@(p , v) = A′ (p , x pv)
    motive⟦⟧ (π e i S C) pv = motive⟦⟧ᵇ e i S C pv
    motive⟦⟧ (A ⊗ B) pv = motive⟦⟧ A pv × motive⟦⟧ B pv

    motive⟦⟧ᵇ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia
                (S : ⟦ P , V ⟧xtel → Set ℓ₂) (C : Desc P (V ⊢< ia > S)  I ℓ)
              → ⟦ P , V ⟧xtel → Set (ℓ₂ ⊔ level⟦⟧ C ℓ)
    motive⟦⟧ᵇ refl i S C pv@(p , v) =
      Π< i > (S pv) (λ x → motive⟦⟧ C (p , v , x))

  mutual

    mott : ∀ {V} {C : Desc P V I ℓ} {pv} → motive⟦⟧ C pv → ⟦ C ⟧ ℓ A′ pv
    mott {C = var x} = id
    mott {C = π e i S C} {pv} m = mott′ e i S C pv m
    mott {C = A ⊗ B} (mA , mB) = mott {C = A} mA , mott {C = B} mB

    mott′ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia (S : ⟦ P , V ⟧xtel → Set ℓ₂)
            (C : Desc P (V ⊢< ia > S)  I ℓ)
            (pv : ⟦ P , V ⟧xtel)
          → motive⟦⟧ᵇ e ia S C pv → ⟦⟧ᵇ ℓ e ia A′ S C pv
    mott′ refl i S C pv@(p , v) m x = mott {C = C} (app< i > m x)

    mmott : ∀ {V} {C : Desc P V I ℓ} {pv} (x : ⟦ C ⟧ ℓ A′ pv)
          → All⟦⟧ C A′ Pr′ x → motive⟦⟧ C pv
    mmott {C = var i} x H = x
    mmott {C = π e i S C} x H = mmott′ e i S C _ x H
    mmott {C = A ⊗ B} (xa , xb) (HA , HB) = mmott {C = A} xa HA , mmott {C = B} xb HB


    mmott′ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia (S : ⟦ P , V ⟧xtel → Set ℓ₂)
             (C : Desc P (V ⊢< ia > S)  I ℓ)
             (pv : ⟦ P , V ⟧xtel) (x : ⟦⟧ᵇ ℓ e ia A′ S C pv)
           → All⟦⟧ᵇ e ia A′ S C Pr′ x → motive⟦⟧ᵇ e ia S C pv
    mmott′ refl i S C pv x H = fun< i > λ s → mmott {C = C} (x s) (H s)

  mutual

    motive⟦⟧P : ∀ {V} (C : Desc P V I ℓ) (pv : ⟦ P , V ⟧xtel) → motive⟦⟧ C pv → Set (level⟦⟧ C c)
    motive⟦⟧P (var x    ) pv X = Pr′ X
    motive⟦⟧P (π e i S C) pv X = motive⟦⟧P′ e i S C pv X
    motive⟦⟧P (A ⊗ B) pv (mA , mB) = motive⟦⟧P A pv mA × motive⟦⟧P B pv mB

    motive⟦⟧P′ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia
                 (S : ⟦ P , V ⟧xtel → Set ℓ₂)
                 (C : Desc P (V ⊢< ia > S)  I ℓ)
                 (pv : ⟦ P , V ⟧xtel)
               → motive⟦⟧ᵇ e ia S C pv → Set (ℓ₂ ⊔ level⟦⟧ C c)
    motive⟦⟧P′ refl i S C pv@(p , v) m = Π< i > (S pv) λ x → motive⟦⟧P C (p , v , x) (app< i > m x)

  mutual

    mottt : ∀ {V} {C : Desc P V I ℓ} {pv} {m : motive⟦⟧ C pv} → All⟦⟧ C A′ Pr′ (mott {C = C} m) → motive⟦⟧P C pv m
    mottt {C = var i    } (lift H) = H
    mottt {C = π e i S C} H = mmottt′ e i S C _ H
    mottt {C = A ⊗ B    } (HA , HB) = mottt {C = A} HA , mottt {C = B} HB

    mmottt′ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia
              (S : ⟦ P , V ⟧xtel → Set ℓ₂) (C : Desc P (V ⊢< ia > S)  I ℓ)
              (pv : ⟦ P , V ⟧xtel) {m : motive⟦⟧ᵇ e ia S C pv}
            → All⟦⟧ᵇ e ia A′ S C Pr′ (mott′ e ia S C pv m) → motive⟦⟧P′ e ia S C pv m
    mmottt′ refl i S C pv H = fun< i > λ s → mottt {C = C} (H s)

  mutual

    motiveE : ∀ {V} (C : Desc P V I ℓ)
              ((p , v) : ⟦ P , V ⟧xtel)
            → (∀ {i} (x : Extend C ℓ A′ (p , v , i)) → Set c)
            → Set (level C)
    motiveE (var x) pv f = f (lift refl)
    motiveE (π e i S C) pv f = motiveE′ e i S C pv f
    motiveE (A ⊗ B) pv f =
      (g : motive⟦⟧ A pv) (Pg : motive⟦⟧P A pv g) → motiveE B pv (f ∘ (mott {C = A} g ,_))

    motiveE′ : ∀ {V} {ℓ₁ ℓ₂}
            → (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ)
            → (ia : ArgInfo)
            → (S : ⟦ P , V ⟧xtel → Set ℓ₂)
            → (C : Desc P (V ⊢< ia > S)  I ℓ)
            → ((p , v) : ⟦ P , V ⟧xtel)
            → (∀ {i′} (x : Extendᵇ ℓ e ia A′ S C (p , v , i′)) → Set c)
            → Set (ℓ₂ ⊔ level C)
    motiveE′ refl i S C pv@(p , v) f = Π< i > (S pv) λ x → motiveE C (p , v , x) (f ∘ (x ,_))

  motive : ∀ k → Set (levelOfTel P ⊔ level (lookup D k))
  motive k = ∀ {p : ⟦ P ⟧tel tt} → motiveE (lookup D k) (p , tt) λ x → Pr′ (constr (k , x))

  mutual
    rew : ∀ {V} {C : Desc P V I ℓ} {pv : ⟦ P , V ⟧xtel}
          (x : ⟦ C ⟧ ℓ A′ pv)
          (H : All⟦⟧ C A′ Pr′ x)
        → mott {C = C} (mmott {C = C} x H) ≡ x
    rew {C = var i    } x H = refl
    rew {C = π p i S C} x H = rewᵇ x H
    rew {C = A ⊗ B} (a , b) (HA , HB)
      rewrite rew {C = A} a HA
            | rew {C = B} b HB = refl

    rewᵇ : ∀ {V} {ℓ₁ ℓ₂} {p : ℓ₁ ≡ ℓ₂ ⊔ ℓ} {i} {S : ⟦ P , V ⟧xtel → Set ℓ₂}
           {C : Desc P (V ⊢< i > S)  I ℓ}
           {pv : ⟦ P , V ⟧xtel}
           (x : ⟦⟧ᵇ ℓ p i A′ S C pv)
           (H : All⟦⟧ᵇ p i A′ S C Pr′ x)
         → mott′ p i S C pv (mmott′ p i S C pv x H) ≡ x
    rewᵇ {p = refl} {arg-info visible (modality relevant _)} {C = C} x H =
      funext (λ y → rew {C = C} (x y) (H y))
    rewᵇ {p = refl} {arg-info visible (modality irrelevant _)} {C = C} x H =
      funext (λ y → rew {C = C} (x y) (H y))
    rewᵇ {p = refl} {arg-info hidden (modality relevant _)} {C = C} x H =
      funext (λ y → rew {C = C} (x y) (H y))
    rewᵇ {p = refl} {arg-info hidden (modality irrelevant _)} {C = C} x H =
      funext (λ y → rew {C = C} (x y) (H y))
    rewᵇ {p = refl} {arg-info instance′ (modality relevant _)} {C = C} x H =
      funext (λ y → rew {C = C} (x y) (H y))
    rewᵇ {p = refl} {arg-info instance′ (modality irrelevant _)} {C = C} x H =
      funext (λ y → rew {C = C} (x y) (H y))

  module _ {k} where

    mutual
      mmmE : ∀ {V} {C : Desc P V I ℓ} {(p , v , i) : ⟦ P , V & I ⟧xtel}
          → (x : Extend C ℓ A′ (p , v , i))
          → {f : ∀ {i} (x : Extend C ℓ A′ (p , v , i)) → Set c}
          → motiveE C (p , v) f
          → (g : Extend C ℓ A′ (p , v , i) → Extend (lookup D k) ℓ A′ (p , tt , i))
          → (f x → Pr′ (constr (k , g x)))
          → AllExtend C A′ Pr′ x
          → Pr′ (constr (k , g x))
      mmmE {C = var x} (lift refl) m f tie _ = tie m
      mmmE {C = π e i S C} x m mk tie H = mmmE′ e i S C x m mk tie H
      mmmE {C = A ⊗ B} (xa , xb) {g} m f tie (HA , HB)  =
        mmmE {C = B} xb (m (mmott {C = A} xa HA)
                           (mottt {C = A} (subst (All⟦⟧ A A′ Pr′) (sym p) HA)))
                        (f ∘ (xa ,_))
                        (subst (λ X → g (X , xb) → Pr′ (constr (k , f (xa , xb)))) (sym p) tie)
                        HB
        where p = rew {C = A} xa HA

      mmmE′ : ∀ {V}{ℓ₁ ℓ₂}
            → (e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ)
            → (ia : ArgInfo)
            → (S  : ⟦ P , V ⟧xtel → Set ℓ₂)
            → (C  : Desc P (V ⊢< ia > S)  I ℓ)
            → {(p , v , i′) : ⟦ P , V & I ⟧xtel}
            → (x  : Extendᵇ ℓ e ia A′ S C (p , v , i′))
            → {f  : ∀ {i′} → Extendᵇ ℓ e ia A′ S C (p , v , i′) → Set c}
            → motiveE′ e ia S C (p , v) f
            → (g  : Extendᵇ ℓ e ia A′ S C (p , v , i′) → Extend (lookup D k) ℓ A′ (p , tt , i′))
            → (f x → Pr′ (constr (k , g x)))
            → AllExtendᵇ e ia A′ S C Pr′ x
            → Pr′ (constr (k , g x))
      mmmE′ refl i S C (s , d) {f} m mk tie H = mmmE {C = C} d (app< i > m s) (mk ∘ (s ,_)) tie H

  GoodMethods : Sets _
  GoodMethods = motive

  motive⇒method : ∀ k → motive k → Method k
  motive⇒method k m {pvi} {x} IH = mmmE {C = lookup D k} x m id id IH

  convert : Els GoodMethods → Els Methods
  convert m k = motive⇒method k (m k)

  elim′ : Els GoodMethods → ∀ {pi} (x : A′ pi) → Pr′ x
  elim′ m = Elim.elim H Pr (convert m)

  elim″ : Arrows GoodMethods ({pi : ⟦ P , I ⟧xtel} (x : A′ pi) → Pr′ x)
  elim″ = curryₙ elim′
