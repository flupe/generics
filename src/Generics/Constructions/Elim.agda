{-# OPTIONS --safe #-}

open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc
open import Generics.All
open import Generics.HasDesc
import Generics.Helpers as Helpers


module Generics.Constructions.Elim
  {P I ℓ} {A : Indexed P I ℓ} (H : HasDesc A)
  (open HasDesc H)
  {p c} (Pr : Pred′ I (λ i → uncurry′ I _ (uncurry′ P _ A p) i → Set c))
  where

private
  variable
    V : ExTele P
    i : ⟦ I ⟧tel p
    v : ⟦ V ⟧tel p

Pr′ : uncurry′ I _ (uncurry′ P _ A p) i → Set c
Pr′ {i} = unpred′ I _ Pr i

--------------------------
-- Types of motives

levelIndArg levelCon : ConDesc P V I ℓ → Level
levelIndArg (var x) = c
levelIndArg (π {ℓ} p i S C) = ℓ ⊔ levelIndArg C
levelIndArg (A ⊗ B) = levelIndArg A ⊔ levelIndArg B
levelCon (var x) = c
levelCon (π {ℓ} p i S C) = ℓ ⊔ levelCon C
levelCon (A ⊗ B) = ℓ ⊔ levelIndArg A ⊔ levelCon B

MotiveIndArg : (C : ConDesc P V I ℓ)
             → ⟦ C ⟧IndArg ℓ A′ (p , v)
             → Set (levelIndArg C)
MotiveIndArgᵇ : ∀ {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia
                (S : ⟦ P , V ⟧xtel → Set ℓ₂)
                (C : ConDesc P (V ⊢< ia > S)  I ℓ)
              → IndArgᵇ ℓ e ia A′ S C (p , v)
              → Set (ℓ₂ ⊔ levelIndArg C)
MotiveIndArg (var x    ) X = Pr′ X
MotiveIndArg (π e i S C) X = MotiveIndArgᵇ e i S C X
MotiveIndArg (A ⊗ B) (mA , mB) = MotiveIndArg A mA × MotiveIndArg B mB
MotiveIndArgᵇ refl i S C m = Π< i > (S (p , _)) (λ s → MotiveIndArg C (m s))

MotiveCon : (C : ConDesc P V I ℓ)
          → (∀ {i} → ⟦ C ⟧Con ℓ A′ (p , v , i) → Set c)
          → Set (levelCon C)
MotiveConᵇ : ∀ {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia
             (S : ⟦ P , V ⟧xtel → Set ℓ₂)
             (C : ConDesc P (V ⊢< ia > S) I ℓ)
           → (∀ {i} → Conᵇ ℓ e ia A′ S C (p , v , i) → Set c)
           → Set (ℓ₂ ⊔ levelCon C)
MotiveCon (var x) f = f (lift refl)
MotiveCon (π e i S C) f = MotiveConᵇ e i S C f
MotiveCon (A ⊗ B) f = (g  : ⟦ A ⟧IndArg ℓ A′ (p , _))
                      (Pg : MotiveIndArg A g)
                    → MotiveCon B (f ∘ (g ,_))
MotiveConᵇ refl i S C f = Π< i > (S (p , _)) λ x → MotiveCon C (f ∘ (x ,_))

Motives : ∀ k → Set (levelCon (lookupCon D k))
Motives k = MotiveCon (lookupCon D k) λ x → Pr′ (constr (k , x))


--------------------------
-- Eliminator

module _ (motives : Els Motives) where

  elimData-wf
    : (x : ⟦ D ⟧Data _ A′ (p , i))
    → AllData D A′ Acc x
    → Pr′ (constr x)

  elim-wf : (x : A′ (p , i)) → Acc x → Pr′ x
  elim-wf x (acc a) = subst Pr′ (constr∘split x) (elimData-wf (split x) a)

  elimData-wf (k , x) a
    = indCon (lookupCon D k) (motives k) x a
    where
      indIndArg
        : (C : ConDesc P V I ℓ)
        → (x : ⟦ C ⟧IndArg ℓ A′ (p , v))
        → AllIndArg C A′ Acc x
        → MotiveIndArg C x
      indIndArgᵇ
        : ∀ {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) {ia}
          {S : ⟦ P , V ⟧xtel → Set ℓ₂}
          (C : ConDesc P (V ⊢< ia > S) I ℓ)
        → (x : IndArgᵇ ℓ e ia A′ S C (p , v))
        → AllIndArgᵇ e ia A′ S C Acc x
        → MotiveIndArgᵇ e ia S C x
      indIndArg (var _) x (lift a) = elim-wf x a
      indIndArg (π e _ S C) x a = indIndArgᵇ e C x a
      indIndArg (A ⊗ B) (xa , xb) (aa , ab)
        = indIndArg A xa aa
        , indIndArg B xb ab
      indIndArgᵇ refl C x a = fun< _ > λ s → indIndArg C (x s) (a s)

      indCon
        : (C   : ConDesc P V I ℓ)
          {mk  : ∀ {i} → ⟦ C ⟧Con ℓ A′ (p , v , i) → ⟦ D ⟧Data ℓ A′ (p , i)}
          (mot : MotiveCon C (Pr′ ∘ constr ∘ mk))
          (x   : ⟦ C ⟧Con ℓ A′ (p , v , i))
        → AllCon C A′ Acc x
        → Pr′ (constr (mk x))
      indConᵇ
        : ∀ {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) {ia}
          {S   : ⟦ P , V ⟧xtel → Set ℓ₂}
          (C   : ConDesc P (V ⊢< ia > S) I ℓ)
          {mk  : ∀ {i} → Conᵇ ℓ e ia A′ S C (p , v , i) → ⟦ D ⟧Data ℓ A′ (p , i)}
          (mot : MotiveConᵇ e ia S C (Pr′ ∘ constr ∘ mk))
          (x   : Conᵇ ℓ e ia A′ S C (p , v , i))
        → AllConᵇ e ia A′ S C Acc x
        → Pr′ (constr (mk x))
      indCon (var _) mot (lift refl) a = mot
      indCon (π e _ _ C) mot x a = indConᵇ e C mot x a
      indCon (A ⊗ B) mot (xa , xb) (aa , ab)
        = indCon B (mot xa (indIndArg A xa aa)) xb ab
      indConᵇ refl C mot (s , x) a = indCon C (app< _ > mot s) x a

  elim : (x : A′ (p , i)) → Pr′ x
  elim x = elim-wf x (wf x)

deriveElim : Arrows Motives (Pred′ I λ i → (x : A′ (p , i)) → Pr′ x)
deriveElim = curryₙ (λ m → pred′ I _ λ i → elim m)
