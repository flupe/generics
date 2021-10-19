{-# OPTIONS --safe #-}


open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc
open import Generics.HasDesc
import Generics.Helpers as Helpers

import Generics.Constructions.Induction as Induction


module Generics.Constructions.Elim
  {P} {I : ExTele P} {ℓ} {A : Indexed P I ℓ} (H : HasDesc {P} {I} {ℓ} A) where

  open HasDesc H

  module _ {p} {c} (Pr : Pred′ I (λ i → uncurry′ I _ (uncurry′ P _ A p) i → Set c)) where

    Pr′ : {i : ⟦ I ⟧tel p} → uncurry′ I _ (uncurry′ P _ A p) i → Set c
    Pr′ {i} = unpred′ I _ Pr i

    -- Induction hypothesis: every recursive occurence satisfies Pr
    IH : ∀ (C : ConDesc P ε I ℓ) {i} → ⟦_⟧Con C ℓ A′ (p , i) → Set (ℓ ⊔ c)
    IH C x = AllCon C A′ Pr′ x

    Methods : Fin n → Set (levelOfTel I ⊔ ℓ ⊔ c)
    Methods k = ∀ {i} {x : ⟦_⟧Con (lookupCon D k) ℓ A′ (p , i)}
              → IH (lookupCon D k) x
              → Pr′ (constr (k , x))

    Pr″ : ∀ {i} → μ D (p , i) → Set c
    Pr″ = Pr′ ∘ from

    module Ind = Induction {p = p} Pr″

    module _ (methods : Els Methods) where

       to-hypothesis : ∀ {i} (X : μ D (p , i)) → All D Pr″ X → Pr″ X
       to-hypothesis ⟨ k , x ⟩ all
         rewrite sym (constr-coh (k , x)) = method (mapAllCon C from Pr′ all)
         where
           C = lookupCon D k

           method : ∀ {i} {x : ⟦_⟧Con C ℓ A′ (p , i)} → IH C x → Pr′ (constr (k , x))
           method = methods k

       elim : ∀ {i} (x : A′ (p , i)) → Pr′ x
       elim x rewrite sym (from∘to x) = Ind.ind to-hypothesis (to x)

    levelIndArg : ∀ {V} (C : ConDesc P V I ℓ) → Level
    levelIndArg (var x) = c
    levelIndArg (π {ℓ} p i S C) = ℓ ⊔ levelIndArg C
    levelIndArg (A ⊗ B) = levelIndArg A ⊔ levelIndArg B

    levelCon : ∀ {V} (C : ConDesc P V I ℓ) → Level
    levelCon (var x) = c
    levelCon (π {ℓ} p i S C) = ℓ ⊔ levelCon C
    levelCon (A ⊗ B) = ℓ ⊔ levelIndArg A ⊔ levelCon B



    MotiveIndArg : ∀ {V} (C : ConDesc P V I ℓ) (v : ⟦ V ⟧tel p)
                 → ⟦ C ⟧IndArg ℓ A′ (p , v)
                 → Set (levelIndArg C)

    MotiveIndArgᵇ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia
                    (S : ⟦ P , V ⟧xtel → Set ℓ₂)
                    (C : ConDesc P (V ⊢< ia > S)  I ℓ)
                    (v : ⟦ V ⟧tel p)
                  → IndArgᵇ ℓ e ia A′ S C (p , v)
                  → Set (ℓ₂ ⊔ levelIndArg C)

    MotiveIndArg (var x    ) v X = Pr′ X
    MotiveIndArg (π e i S C) v X = MotiveIndArgᵇ e i S C v X
    MotiveIndArg (A ⊗ B) v (mA , mB) = MotiveIndArg A v mA × MotiveIndArg B v mB

    MotiveIndArgᵇ refl i S C v m = Π< i > (S (p , v)) (λ s → MotiveIndArg C (v , s) (m s))



    AllIndArg⇒MotiveIndArg : ∀ {V} {C : ConDesc P V I ℓ} {v}
                    → {x : ⟦ C ⟧IndArg ℓ A′ (p , v)}
                    → AllIndArg C A′ Pr′ x  → MotiveIndArg C v x

    AllIndArgᵇ⇒MotiveIndArgᵇ :
            ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia
              (S : ⟦ P , V ⟧xtel → Set ℓ₂) (C : ConDesc P (V ⊢< ia > S)  I ℓ)
              (v : ⟦ V ⟧tel p)
              {x : IndArgᵇ ℓ e ia A′ S C (p , v)}
            → AllIndArgᵇ e ia A′ S C Pr′ x → MotiveIndArgᵇ e ia S C v x

    AllIndArg⇒MotiveIndArg {C = var i    } (lift H) = H
    AllIndArg⇒MotiveIndArg {C = π e i S C} H = AllIndArgᵇ⇒MotiveIndArgᵇ e i S C _ H
    AllIndArg⇒MotiveIndArg {C = A ⊗ B    } (HA , HB)
      = AllIndArg⇒MotiveIndArg {C = A} HA , AllIndArg⇒MotiveIndArg {C = B} HB

    AllIndArgᵇ⇒MotiveIndArgᵇ refl i S C pv H = fun< i > λ s → AllIndArg⇒MotiveIndArg {C = C} (H s)



    MotiveCon : ∀ {V} (C : ConDesc P V I ℓ) v
              → (∀ {i} (x : ⟦ C ⟧Con ℓ A′ (p , v , i)) → Set c)
              → Set (levelCon C)

    MotiveConᵇ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) (ia : ArgInfo)
                 (S : ⟦ P , V ⟧xtel → Set ℓ₂)
                 (C : ConDesc P (V ⊢< ia > S)  I ℓ)
                 (v : ⟦ V ⟧tel p)
               → (∀ {i′} (x : Conᵇ ℓ e ia A′ S C (p , v , i′)) → Set c)
               → Set (ℓ₂ ⊔ levelCon C)

    MotiveCon (var x) v f = f (lift refl)
    MotiveCon (π e i S C) v f = MotiveConᵇ e i S C v f
    MotiveCon (A ⊗ B) v f =
      (g : ⟦ A ⟧IndArg ℓ A′ (p , v)) (Pg : MotiveIndArg A v g) → MotiveCon B v (f ∘ (g ,_))

    MotiveConᵇ refl i S C v f = Π< i > (S (p , v)) λ x → MotiveCon C (v , x) (f ∘ (x ,_))



    Motives : ∀ k → Set (levelCon (lookupCon D k))
    Motives k = MotiveCon (lookupCon D k) tt λ x → Pr′ (constr (k , x))

    module _ {k} where

      bury : ∀ {V} (C : ConDesc P V I ℓ) {v i}
           → (f : ∀ {i} → ⟦ C ⟧Con ℓ A′ (p , v , i) → ⟦ lookupCon D k ⟧Con ℓ A′ (p , tt , i))
           → (M : MotiveCon C v λ x → Pr′ (constr (k , f x)))
           → (x : ⟦ C ⟧Con ℓ A′ (p , v , i))
           → AllCon C A′ Pr′ x
           → Pr′ (constr (k , f x))

      buryᵇ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia
              (S : ⟦ P , V ⟧xtel → Set ℓ₂)
              (C : ConDesc P (V ⊢< ia > S) I ℓ)
              {v i}
              (f : ∀ {i} → Conᵇ ℓ e ia A′ S C (p , v , i)
                         → ⟦_⟧Con (lookupCon D k) ℓ A′ (p , tt , i))
              (M : MotiveConᵇ e ia S C v λ x → Pr′ (constr (k , f x)))
            → (x : Conᵇ ℓ e ia A′ S C (p , v , i))
            → AllConᵇ e ia A′ S C Pr′ x
            → Pr′ (constr (k , f x))

      bury (var _) _ M (lift refl) _ = M
      bury (π e i S C) f M x H = buryᵇ e i S C f M x H
      bury (A ⊗ B) f M (a , b) (HA , HB) =
        bury B (f ∘ (a ,_)) (M a (AllIndArg⇒MotiveIndArg {C = A} HA)) b HB

      buryᵇ refl i S C f M (s , x) H = bury C (f ∘ (s ,_)) (app< i > M s) x H


    motive⇒method : ∀ k → Motives k → Methods k
    motive⇒method k m {x = x} IH = bury (lookupCon D k) id m x IH

    convert : Els Motives → Els Methods
    convert m k = motive⇒method k (m k)

    elim′ : Els Motives → Pred′ I λ i → (x : A′ (p , i)) → Pr′ x
    elim′ m = pred′ I _ (λ i → elim (convert m) {i})

    deriveElim : Arrows Motives (Pred′ I λ i → (x : A′ (p , i)) → Pr′ x)
    deriveElim = curryₙ elim′
