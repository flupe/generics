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
-- Defining motives' types

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


Pr″ : ⟦ D ⟧Data _ A′ (p , i) → Set c
Pr″ = Pr′ ∘ constr

--------------------------
-- Eliminator

module _ (motives : Els Motives) where

  ind  : (x : ⟦ D ⟧Data _ A′ (p , i)) → AllData D A′ Acc x → Pr″ x

  elim : (x : A′ (p , i)) → Acc x → Pr″ (split x)
  elim x (acc a) = ind (split x) a

  ind (k , x) a = indCon (lookupCon D k) (k ,_) (motives k) x id a
    where
      indIndArg
        : (C      : ConDesc P V I ℓ)
        → (x      : ⟦ C ⟧IndArg ℓ A′ (p , v))
        → AllIndArg C A′ Acc x
        → MotiveIndArg C x
      indIndArgᵇ
        : ∀ {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia
          (S : ⟦ P , V ⟧xtel → Set ℓ₂)
          (C : ConDesc P (V ⊢< ia > S) I ℓ)
        → (x : IndArgᵇ ℓ e ia A′ S C (p , v))
        → AllIndArgᵇ e ia A′ S C Acc x
        → MotiveIndArgᵇ e ia S C x
      indIndArg (var _) x (lift a) = subst Pr′ (constr∘split x) (elim x a)
      indIndArg (π e _ S C) x a = indIndArgᵇ e _ S C x a
      indIndArg (A ⊗ B) (xa , xb) (aa , ab)
        = indIndArg A xa aa
        , indIndArg B xb ab
      indIndArgᵇ refl ia S C x a = fun< ia > λ s → indIndArg C (x s) (a s)
      indCon : (C      : ConDesc P V I ℓ)
             → (mk     : ⟦ C ⟧Con ℓ A′ (p , v , i) → ⟦ D ⟧Data ℓ A′ (p , i))
             → {tie    : ∀ {i} → ⟦ C ⟧Con ℓ A′ (p , v , i) → Set c}
             → (motive : MotiveCon C tie)
             → (x      : ⟦ C ⟧Con ℓ A′ (p , v , i))
             → (final  : tie x → Pr″ (mk x) )
             → AllCon C A′ Acc x
             → Pr″ (mk x)
      indConᵇ : ∀ {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ia
                (S : ⟦ P , V ⟧xtel → Set ℓ₂)
                (C : ConDesc P (V ⊢< ia > S) I ℓ)
              → (mk     : Conᵇ ℓ e ia A′ S C (p , v , i) → ⟦ D ⟧Data ℓ A′ (p , i))
              → {tie    : ∀ {i} → Conᵇ ℓ e ia A′ S C (p , v , i) → Set c}
              → (motive : MotiveConᵇ e ia S C tie)
              → (x      : Conᵇ ℓ e ia A′ S C (p , v , i))
              → (final  : tie x → Pr″ (mk x) )
              → AllConᵇ e ia A′ S C Acc x
              → Pr″ (mk x)
      indCon (var _) mk motive (lift refl) final a = final motive
      indCon (π e _ S C) mk motive x final a = indConᵇ e _ S C mk motive x final a
      indCon (A ⊗ B) mk motive (xa , xb) final (aa , ab)
        = indCon B (mk ∘ (xa ,_)) (motive xa (indIndArg A xa aa)) xb final ab
      indConᵇ refl ia S C mk motive (s , x) final a
        = indCon C (mk ∘ (s ,_)) (app< ia > motive s) x final a

  elim′ : (x : A′ (p , i)) → Pr′ x
  elim′ x = subst Pr′ (constr∘split x) (elim x (wf x))

deriveElim : Arrows Motives (Pred′ I λ i → (x : A′ (p , i)) → Pr′ x)
deriveElim = curryₙ (λ m → pred′ I _ λ i → elim′ m)
