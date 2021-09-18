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

  open HasDesc H

  Pr′ : {i : ⟦ I ⟧tel p} → uncurry′ I _ (uncurry′ P _ A p) i → Set c
  Pr′ {i} = unpred′ I _ Pr i

  -- Induction hypothesis: every recursive occurence satisfies Pr
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

  open HasDesc H

  module _ {c} (Pr : Pred′ I (λ i → uncurry′ I _ (uncurry′ P _ A p) i → Set c)) where

    open Elim H {p} Pr

    level⟦⟧ : ∀ {V} (C : ConDesc P V I ℓ) → Level
    level⟦⟧ (var x) = c
    level⟦⟧ (π {ℓ} p i S C) = ℓ ⊔ level⟦⟧ C
    level⟦⟧ (A ⊗ B) = level⟦⟧ A ⊔ level⟦⟧ B

    levelE : ∀ {V} (C : ConDesc P V I ℓ) → Level
    levelE (var x) = c
    levelE (π {ℓ} p i S C) = ℓ ⊔ levelE C
    levelE (A ⊗ B) = ℓ ⊔ level⟦⟧ A ⊔ levelE B

    mutual

      Motive⟦⟧P : ∀ {V} (C : ConDesc P V I ℓ) (v : ⟦ V ⟧tel p)
                → ⟦ C ⟧Con ℓ A′ (p , v)
                → Set (level⟦⟧ C)
      Motive⟦⟧P (var x    ) v X = Pr′ X
      Motive⟦⟧P (π e i S C) v X = Motive⟦⟧Pᵇ e i S C v X
      Motive⟦⟧P (A ⊗ B) v (mA , mB) = Motive⟦⟧P A v mA × Motive⟦⟧P B v mB

      Motive⟦⟧Pᵇ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia
                   (S : ⟦ P , V ⟧xtel → Set ℓ₂)
                   (C : ConDesc P (V ⊢< ia > S)  I ℓ)
                   (v : ⟦ V ⟧tel p)
                 → ⟦⟧ᵇ ℓ e ia A′ S C (p , v)
                 → Set (ℓ₂ ⊔ level⟦⟧ C)
      Motive⟦⟧Pᵇ refl i S C v m = Π< i > (S (p , v)) (λ s → Motive⟦⟧P C (v , s) (m s))

    mutual

      All⟦⟧⇒Motive⟦⟧P : ∀ {V} {C : ConDesc P V I ℓ} {v}
                      → {x : ⟦ C ⟧Con ℓ A′ (p , v)}
                      → All⟦⟧ C A′ Pr′ x  → Motive⟦⟧P C v x
      All⟦⟧⇒Motive⟦⟧P {C = var i    } (lift H) = H
      All⟦⟧⇒Motive⟦⟧P {C = π e i S C} H = All⟦⟧ᵇ⇒Motive⟦⟧Pᵇ e i S C _ H
      All⟦⟧⇒Motive⟦⟧P {C = A ⊗ B    } (HA , HB)
        = All⟦⟧⇒Motive⟦⟧P {C = A} HA , All⟦⟧⇒Motive⟦⟧P {C = B} HB

      All⟦⟧ᵇ⇒Motive⟦⟧Pᵇ :
              ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia
                (S : ⟦ P , V ⟧xtel → Set ℓ₂) (C : ConDesc P (V ⊢< ia > S)  I ℓ)
                (v : ⟦ V ⟧tel p)
                {x : ⟦⟧ᵇ ℓ e ia A′ S C (p , v)}
              → All⟦⟧ᵇ e ia A′ S C Pr′ x → Motive⟦⟧Pᵇ e ia S C v x
      All⟦⟧ᵇ⇒Motive⟦⟧Pᵇ refl i S C pv H = fun< i > λ s → All⟦⟧⇒Motive⟦⟧P {C = C} (H s)

    mutual

      MotiveE : ∀ {V} (C : ConDesc P V I ℓ)
                (v : ⟦ V ⟧tel p)
              → (∀ {i} (x : Extend C ℓ A′ (p , v , i)) → Set c)
              → Set (levelE C)
      MotiveE (var x) v f = f (lift refl)
      MotiveE (π e i S C) v f = MotiveEᵇ e i S C v f
      MotiveE (A ⊗ B) v f =
        (g : ⟦ A ⟧Con ℓ A′ (p , v)) (Pg : Motive⟦⟧P A v g) → MotiveE B v (f ∘ (g ,_))

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

    module _ {k} where

      bury : ∀ {V} (C : ConDesc P V I ℓ) {v i}
           → (f : ∀ {i} → Extend C ℓ A′ (p , v , i) → Extend (lookupCon D k) ℓ A′ (p , tt , i))
           → (M : MotiveE C v λ x → Pr′ (constr (k , f x)))
           → (x : Extend C ℓ A′ (p , v , i))
           → AllExtend C A′ Pr′ x
           → Pr′ (constr (k , f x))

      buryᵇ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia
              (S : ⟦ P , V ⟧xtel → Set ℓ₂)
              (C : ConDesc P (V ⊢< ia > S) I ℓ)
              {v i}
              (f : ∀ {i} → Extendᵇ ℓ e ia A′ S C (p , v , i)
                         → Extend (lookupCon D k) ℓ A′ (p , tt , i))
              (M : MotiveEᵇ e ia S C v λ x → Pr′ (constr (k , f x)))
            → (x : Extendᵇ ℓ e ia A′ S C (p , v , i))
            → AllExtendᵇ e ia A′ S C Pr′ x
            → Pr′ (constr (k , f x))

      bury (var _) _ M (lift refl) _ = M
      bury (π e i S C) f M x H = buryᵇ e i S C f M x H
      bury (A ⊗ B) f M (a , b) (HA , HB) =
        bury B (f ∘ (a ,_)) (M a (All⟦⟧⇒Motive⟦⟧P {C = A} HA)) b HB

      buryᵇ refl i S C f M (s , x) H = bury C (f ∘ (s ,_)) (app< i > M s) x H

    motive⇒method : ∀ k → Motives k → Methods k
    motive⇒method k m {x = x} IH = bury (lookupCon D k) id m x IH

    convert : Els Motives → Els Methods
    convert m k = motive⇒method k (m k)

    elim′ : Els Motives → Pred′ I λ i → (x : A′ (p , i)) → Pr′ x
    elim′ m = pred′ I _ (λ i → Elim.elim H Pr (convert m) {i})

    deriveElim : Arrows Motives (Pred′ I λ i → (x : A′ (p , i)) → Pr′ x)
    deriveElim = curryₙ elim′
