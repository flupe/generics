{-# OPTIONS --safe #-}

module Generics.Constructions.Elim where

open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc
open import Generics.HasDesc
import Generics.Helpers as Helpers

import Generics.Constructions.Induction as Induction


module Elim {P} {I : ExTele P} {ℓ} {A : Indexed P I ℓ} (H : HasDesc {P} {I} {ℓ} A)
            {p} {c} (Pr : Pred′ I (λ i → uncurry′ I _ (uncurry′ P _ A p) i → Set c)) where
                    -- Pr : Pred P I (uncurry P I A)

  open HasDesc H


  Pr′ : {i : ⟦ I ⟧tel p} → uncurry′ I _ (uncurry′ P _ A p) i → Set c
  Pr′ {i} = unpred′ I _ Pr i

  -- induction hypothesis: every recursive occurence satisfies Pr
  IH : ∀ (C : ConDesc P ε I ℓ) {i} → Extend C ℓ A′ (p , i) → Set (ℓ ⊔ c)
  IH C x = AllExtend C A′ Pr′ x

  Methods : Fin n → Set (levelOfTel I ⊔ ℓ ⊔ c)
  Methods k = ∀ {i} {x : Extend (lookupCon D k) ℓ A′ (p , i)}
            → IH (lookupCon D k) x
            → Pr′ (constr (k , x))

  Pr″ : ∀ {i} → μ D (p , i) → Set c
  Pr″ = Pr′ ∘ from

  module Ind = Induction {p = p} Pr″

  module _ (methods : Els Methods) where

     to-hypothesis : ∀ {i} (X : μ D (p , i)) → All D Pr″ X → Pr″ X
     to-hypothesis ⟨ k , x ⟩ all
       rewrite sym (constr-coh (k , x)) = method (mapAllExtend C from Pr′ all)
       where
         C = lookupCon D k

         method : ∀ {i} {x : Extend C ℓ A′ (p , i)} → IH C x → Pr′ (constr (k , x))
         method = methods k

     elim : ∀ {i} (x : A′ (p , i)) → Pr′ x
     elim x rewrite sym (from∘to x) = Ind.ind to-hypothesis (to x)

module _ {P} {I : ExTele P} {ℓ} {A : Indexed P I ℓ} (H : HasDesc {P} {I} {ℓ} A) {p} where

  HasFunExt : ∀ {V} (C : ConDesc P V I ℓ) → Setω
  HasFunExt (var x) = Liftω ⊤
  HasFunExt (π p ai₁ S C) = ∀ {a b} → Extensionality a b
  HasFunExt (A ⊗ B) = HasFunExt A ×ω HasFunExt B 

  haveFunExt : (∀ {a b} → Extensionality a b)
             → ∀ {V} {C : ConDesc P V I ℓ} → HasFunExt C
  haveFunExt F {C = var x} = liftω tt
  haveFunExt F {C = π p ai₁ S C} = F
  haveFunExt F {C = A ⊗ B} = haveFunExt F ,ω haveFunExt F

  open Helpers P I ℓ (const ⊤) (const ⊤) HasFunExt
  open HasDesc H

  FunExtHelpers : Setω
  FunExtHelpers = Helpers p D

  module _ ⦃ FH : FunExtHelpers ⦄
           {c} (Pr : Pred′ I (λ i → uncurry′ I _ (uncurry′ P _ A p) i → Set c)) where

    open Elim H {p} Pr

    level⟦⟧ : ∀ {V} (C : ConDesc P V I ℓ) → Level → Level
    level⟦⟧ (var x) c = c
    level⟦⟧ (π {ℓ} p i S C) c = ℓ ⊔ level⟦⟧ C c
    level⟦⟧ (A ⊗ B) c = level⟦⟧ A c ⊔ level⟦⟧ B c

    levelE : ∀ {V} (C : ConDesc P V I ℓ) → Level
    levelE (var x) = c
    levelE (π {ℓ} p i S C) = ℓ ⊔ levelE C
    levelE (A ⊗ B) = level⟦⟧ A ℓ ⊔ level⟦⟧ A c ⊔ levelE B

    mutual

      Motive⟦⟧ : ∀ {V} (C : ConDesc P V I ℓ) → ⟦ V ⟧tel p → Set (level⟦⟧ C ℓ)
      Motive⟦⟧ (var x) v = A′ (p , x (p , v))
      Motive⟦⟧ (π e i S C) v = Motive⟦⟧ᵇ e i S C v
      Motive⟦⟧ (A ⊗ B) v = Motive⟦⟧ A v × Motive⟦⟧ B v

      Motive⟦⟧ᵇ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia
                  (S : ⟦ P , V ⟧xtel → Set ℓ₂) (C : ConDesc P (V ⊢< ia > S)  I ℓ)
                → ⟦ V ⟧tel p → Set (ℓ₂ ⊔ level⟦⟧ C ℓ)
      Motive⟦⟧ᵇ refl i S C v =
        Π< i > (S (p , v)) (λ x → Motive⟦⟧ C (v , x))

    mutual

      Motive⟦⟧⇒⟦⟧Con : ∀ {V} {C : ConDesc P V I ℓ} {v} → Motive⟦⟧ C v → ⟦ C ⟧Con ℓ A′ (p , v)
      Motive⟦⟧⇒⟦⟧Con {C = var x} = id
      Motive⟦⟧⇒⟦⟧Con {C = π e i S C} {pv} m = Motive⟦⟧⇒⟦⟧Conᵇ e i S C pv m
      Motive⟦⟧⇒⟦⟧Con {C = A ⊗ B} (mA , mB) = Motive⟦⟧⇒⟦⟧Con {C = A} mA , Motive⟦⟧⇒⟦⟧Con {C = B} mB

      Motive⟦⟧⇒⟦⟧Conᵇ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia (S : ⟦ P , V ⟧xtel → Set ℓ₂)
                          (C : ConDesc P (V ⊢< ia > S)  I ℓ)
                          (v : ⟦ V ⟧tel p)
                        → Motive⟦⟧ᵇ e ia S C v → ⟦⟧ᵇ ℓ e ia A′ S C (p , v)
      Motive⟦⟧⇒⟦⟧Conᵇ refl i S C v m x = Motive⟦⟧⇒⟦⟧Con {C = C} (app< i > m x)

      All⟦⟧⇒Motive⟦⟧ : ∀ {V} {C : ConDesc P V I ℓ} {v} (x : ⟦ C ⟧Con ℓ A′ (p , v))
            → All⟦⟧ C A′ Pr′ x → Motive⟦⟧ C v
      All⟦⟧⇒Motive⟦⟧ {C = var i} x H = x
      All⟦⟧⇒Motive⟦⟧ {C = π e i S C} x H = All⟦⟧ᵇ⇒Motive⟦⟧ᵇ e i S C _ x H
      All⟦⟧⇒Motive⟦⟧ {C = A ⊗ B} (xa , xb) (HA , HB) = All⟦⟧⇒Motive⟦⟧ {C = A} xa HA , All⟦⟧⇒Motive⟦⟧ {C = B} xb HB
      
      All⟦⟧ᵇ⇒Motive⟦⟧ᵇ :
             ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia (S : ⟦ P , V ⟧xtel → Set ℓ₂)
               (C : ConDesc P (V ⊢< ia > S)  I ℓ)
               (v : ⟦ V ⟧tel p) (x : ⟦⟧ᵇ ℓ e ia A′ S C (p , v))
             → All⟦⟧ᵇ e ia A′ S C Pr′ x → Motive⟦⟧ᵇ e ia S C v
      All⟦⟧ᵇ⇒Motive⟦⟧ᵇ refl i S C v x H = fun< i > λ s → All⟦⟧⇒Motive⟦⟧ {C = C} (x s) (H s)

    mutual

      Motive⟦⟧P : ∀ {V} (C : ConDesc P V I ℓ) (v : ⟦ V ⟧tel p) → Motive⟦⟧ C v → Set (level⟦⟧ C c)
      Motive⟦⟧P (var x    ) v X = Pr′ X
      Motive⟦⟧P (π e i S C) v X = Motive⟦⟧Pᵇ e i S C v X
      Motive⟦⟧P (A ⊗ B) v (mA , mB) = Motive⟦⟧P A v mA × Motive⟦⟧P B v mB

      Motive⟦⟧Pᵇ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia
                   (S : ⟦ P , V ⟧xtel → Set ℓ₂)
                   (C : ConDesc P (V ⊢< ia > S)  I ℓ)
                   (v : ⟦ V ⟧tel p)
                 → Motive⟦⟧ᵇ e ia S C v → Set (ℓ₂ ⊔ level⟦⟧ C c)
      Motive⟦⟧Pᵇ refl i S C v m = Π< i > (S (p , v)) λ x → Motive⟦⟧P C (v , x) (app< i > m x)

    mutual

      All⟦⟧⇒Motive⟦⟧P : ∀ {V} {C : ConDesc P V I ℓ} {v} {m : Motive⟦⟧ C v}
                      → All⟦⟧ C A′ Pr′ (Motive⟦⟧⇒⟦⟧Con {C = C} m) → Motive⟦⟧P C v m
      All⟦⟧⇒Motive⟦⟧P {C = var i    } (lift H) = H
      All⟦⟧⇒Motive⟦⟧P {C = π e i S C} H = All⟦⟧ᵇ⇒Motive⟦⟧Pᵇ e i S C _ H
      All⟦⟧⇒Motive⟦⟧P {C = A ⊗ B    } (HA , HB)
        = All⟦⟧⇒Motive⟦⟧P {C = A} HA , All⟦⟧⇒Motive⟦⟧P {C = B} HB

      All⟦⟧ᵇ⇒Motive⟦⟧Pᵇ :
              ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia
                (S : ⟦ P , V ⟧xtel → Set ℓ₂) (C : ConDesc P (V ⊢< ia > S)  I ℓ)
                (v : ⟦ V ⟧tel p) {m : Motive⟦⟧ᵇ e ia S C v}
              → All⟦⟧ᵇ e ia A′ S C Pr′ (Motive⟦⟧⇒⟦⟧Conᵇ e ia S C v m) → Motive⟦⟧Pᵇ e ia S C v m
      All⟦⟧ᵇ⇒Motive⟦⟧Pᵇ refl i S C pv H = fun< i > λ s → All⟦⟧⇒Motive⟦⟧P {C = C} (H s)

    mutual

      MotiveE : ∀ {V} (C : ConDesc P V I ℓ)
                (v : ⟦ V ⟧tel p)
              → (∀ {i} (x : Extend C ℓ A′ (p , v , i)) → Set c)
              → Set (levelE C)
      MotiveE (var x) v f = f (lift refl)
      MotiveE (π e i S C) v f = MotiveEᵇ e i S C v f
      MotiveE (A ⊗ B) v f =
        (g : Motive⟦⟧ A v) (Pg : Motive⟦⟧P A v g) → MotiveE B v (f ∘ (Motive⟦⟧⇒⟦⟧Con {C = A} g ,_))

      MotiveEᵇ : ∀ {V} {ℓ₁ ℓ₂}
              → (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ)
              → (ia : ArgInfo)
              → (S : ⟦ P , V ⟧xtel → Set ℓ₂)
              → (C : ConDesc P (V ⊢< ia > S)  I ℓ)
              → (v : ⟦ V ⟧tel p)
              → (∀ {i′} (x : Extendᵇ ℓ e ia A′ S C (p , v , i′)) → Set c)
              → Set (ℓ₂ ⊔ levelE C)
      MotiveEᵇ refl i S C v f = Π< i > (S (p , v)) λ x → MotiveE C (v , x) (f ∘ (x ,_))

    Motives : ∀ k → Set (levelE (lookupCon D k))
    Motives k = MotiveE (lookupCon D k) tt λ x → Pr′ (constr (k , x))

    mutual
      All⟦⟧⇒Motive⟦⟧⇒⟦⟧Con : ∀ {V} {C : ConDesc P V I ℓ} {v : ⟦ V ⟧tel p}
            (F : HasFunExt C)
            (x : ⟦ C ⟧Con ℓ A′ (p , v))
            (H : All⟦⟧ C A′ Pr′ x)
          → Motive⟦⟧⇒⟦⟧Con {C = C} (All⟦⟧⇒Motive⟦⟧ {C = C} x H) ≡ x
      All⟦⟧⇒Motive⟦⟧⇒⟦⟧Con {C = var i    } F x H = refl
      All⟦⟧⇒Motive⟦⟧⇒⟦⟧Con {C = π p i S C} F x H = All⟦⟧⇒Motive⟦⟧⇒⟦⟧Conᵇ F x H
      All⟦⟧⇒Motive⟦⟧⇒⟦⟧Con {C = A ⊗ B} (FA ,ω FB) (a , b) (HA , HB)
        rewrite All⟦⟧⇒Motive⟦⟧⇒⟦⟧Con {C = A} FA a HA
              | All⟦⟧⇒Motive⟦⟧⇒⟦⟧Con {C = B} FB b HB = refl

      All⟦⟧⇒Motive⟦⟧⇒⟦⟧Conᵇ : ∀ {V} {ℓ₁ ℓ₂} {e : ℓ₁ ≡ ℓ₂ ⊔ ℓ} {i} {S : ⟦ P , V ⟧xtel → Set ℓ₂}
             {C : ConDesc P (V ⊢< i > S)  I ℓ}
             {v : ⟦ V ⟧tel p}
             (F : ∀ {a b} → Extensionality a b)
             (x : ⟦⟧ᵇ ℓ e i A′ S C (p , v))
             (H : All⟦⟧ᵇ e i A′ S C Pr′ x)
           → Motive⟦⟧⇒⟦⟧Conᵇ e i S C v (All⟦⟧ᵇ⇒Motive⟦⟧ᵇ e i S C v x H) ≡ x
      All⟦⟧⇒Motive⟦⟧⇒⟦⟧Conᵇ {e = refl} {arg-info visible (modality relevant _)} {C = C} F x H =
        F (λ y → All⟦⟧⇒Motive⟦⟧⇒⟦⟧Con {C = C} (haveFunExt F) (x y) (H y))
      All⟦⟧⇒Motive⟦⟧⇒⟦⟧Conᵇ {e = refl} {arg-info visible (modality irrelevant _)} {C = C} F x H =
        F (λ y → All⟦⟧⇒Motive⟦⟧⇒⟦⟧Con {C = C} (haveFunExt F) (x y) (H y))
      All⟦⟧⇒Motive⟦⟧⇒⟦⟧Conᵇ {e = refl} {arg-info hidden (modality relevant _)} {C = C} F x H =
        F (λ y → All⟦⟧⇒Motive⟦⟧⇒⟦⟧Con {C = C} (haveFunExt F) (x y) (H y))
      All⟦⟧⇒Motive⟦⟧⇒⟦⟧Conᵇ {e = refl} {arg-info hidden (modality irrelevant _)} {C = C} F x H =
        F (λ y → All⟦⟧⇒Motive⟦⟧⇒⟦⟧Con {C = C} (haveFunExt F) (x y) (H y))
      All⟦⟧⇒Motive⟦⟧⇒⟦⟧Conᵇ {e = refl} {arg-info instance′ (modality relevant _)} {C = C} F x H =
        F (λ y → All⟦⟧⇒Motive⟦⟧⇒⟦⟧Con {C = C} (haveFunExt F) (x y) (H y))
      All⟦⟧⇒Motive⟦⟧⇒⟦⟧Conᵇ {e = refl} {arg-info instance′ (modality irrelevant _)} {C = C} F x H =
        F (λ y → All⟦⟧⇒Motive⟦⟧⇒⟦⟧Con {C = C} (haveFunExt F) (x y) (H y))

    module _ {k} where

      mutual
        mmmE : ∀ {V} {C : ConDesc P V I ℓ} {v i}
            → (F : ConHelper p C)
            → (x : Extend C ℓ A′ (p , v , i))
            → {f : ∀ {i} (x : Extend C ℓ A′ (p , v , i)) → Set c}
            → MotiveE C v f
            → (g : Extend C ℓ A′ (p , v , i) → Extend (lookupCon D k) ℓ A′ (p , tt , i))
            → (f x → Pr′ (constr (k , g x)))
            → AllExtend C A′ Pr′ x
            → Pr′ (constr (k , g x))
        mmmE (var) (lift refl) m f tie _ = tie m
        mmmE (pi-rel ⦃ _ ⦄ ⦃ F ⦄) x m mk tie H = mmmE′ _ _ _ _ F x m mk tie H
        mmmE (pi-irr ⦃ _ ⦄ ⦃ F ⦄) x m mk tie H = mmmE′ _ _ _ _ F x m mk tie H
        mmmE (prod {A = A} {B} ⦃ FA ⦄ ⦃ FB ⦄) (xa , xb) {g} m f tie (HA , HB)  =
          mmmE {C = B} FB xb (m (All⟦⟧⇒Motive⟦⟧ {C = A} xa HA)
                             (All⟦⟧⇒Motive⟦⟧P {C = A} (subst (All⟦⟧ A A′ Pr′) (sym e) HA)))
                          (f ∘ (xa ,_))
                          (subst (λ X → g (X , xb) → Pr′ (constr (k , f (xa , xb)))) (sym e) tie)
                          HB
          where e = All⟦⟧⇒Motive⟦⟧⇒⟦⟧Con {C = A} FA xa HA

        mmmE′ : ∀ {V}{ℓ₁ ℓ₂}
              → (e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ)
              → (ia : ArgInfo)
              → (S  : ⟦ P , V ⟧xtel → Set ℓ₂)
              → (C  : ConDesc P (V ⊢< ia > S)  I ℓ)
              → (F  : ConHelper p C)
              → ∀ {v i′}
              → (x  : Extendᵇ ℓ e ia A′ S C (p , v , i′))
              → {f  : ∀ {i′} → Extendᵇ ℓ e ia A′ S C (p , v , i′) → Set c}
              → MotiveEᵇ e ia S C v f
              → (g  : Extendᵇ ℓ e ia A′ S C (p , v , i′) → Extend (lookupCon D k) ℓ A′ (p , tt , i′))
              → (f x → Pr′ (constr (k , g x)))
              → AllExtendᵇ e ia A′ S C Pr′ x
              → Pr′ (constr (k , g x))
        mmmE′ refl i S C F (s , d) {f} m mk tie H = mmmE {C = C} F d (app< i > m s) (mk ∘ (s ,_)) tie H

    motive⇒method : ∀ k → Motives k → Methods k
    motive⇒method k m {x = x} IH = mmmE {C = lookupCon D k} (lookupHelper FH k) x m id id IH

    convert : Els Motives → Els Methods
    convert m k = motive⇒method k (m k)

   -- elim′ : Els Motives → ∀ {i} (x : A′ (p , i)) → Pr′ x
    -- elim′ m = Elim.elim H Pr (convert m)
    elim′ : Els Motives → Pred′ I λ i → (x : A′ (p , i)) → Pr′ x
    elim′ m = pred′ I _ (λ i → Elim.elim H Pr (convert m) {i})

    deriveElim : Arrows Motives (Pred′ I λ i → (x : A′ (p , i)) → Pr′ x)
    deriveElim = curryₙ elim′
