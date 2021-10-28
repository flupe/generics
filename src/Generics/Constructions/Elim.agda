{-# OPTIONS --sized-types --without-K #-}

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

Pr′ : A′ (p , i) → Set c
Pr′ {i} = unpred′ I _ Pr i

--------------------------
-- Types of motives

levelElimIndArg levelElimCon : ConDesc P V I → Level

levelElimIndArg (var x) = c
levelElimIndArg (π {ℓ} i S C) = ℓ ⊔ levelElimIndArg C
levelElimIndArg (A ⊗ B) = levelElimIndArg A ⊔ levelElimIndArg B

levelElimCon (var x) = c
levelElimCon (π {ℓ′} i S C) = ℓ′ ⊔ levelElimCon C
levelElimCon (A ⊗ B) = levelIndArg A ℓ ⊔ levelElimIndArg A ⊔ levelElimCon B

MotiveIndArg : (C : ConDesc P V I)
             → ⟦ C ⟧IndArg A′ (p , v)
             → Set (levelElimIndArg C)
MotiveIndArg (var x    ) X = Pr′ X
MotiveIndArg (π ia S C) X = Π< ia > (S _) (MotiveIndArg C ∘ app< ia > X)
MotiveIndArg (A ⊗ B) (mA , mB) = MotiveIndArg A mA × MotiveIndArg B mB

MotiveCon : (C : ConDesc P V I)
          → (∀ {i} → ⟦ C ⟧Con A′ (p , v , i) → Set c)
          → Set (levelElimCon C)
MotiveCon (var x) f = f refl
MotiveCon (π ia S C) f = Π< ia > (S _) (λ s → MotiveCon C (f ∘ (s ,_)))
MotiveCon (A ⊗ B) f = (g  : ⟦ A ⟧IndArg A′ (p , _))
                      (Pg : MotiveIndArg A g)
                    → MotiveCon B (f ∘ (g ,_))

Motives : ∀ k → Set (levelElimCon (lookupCon D k))
Motives k = MotiveCon (lookupCon D k) λ x → Pr′ (constr (k , x))


--------------------------
-- Eliminator

module _ (motives : Els Motives) where

  elimData-wf
    : (x : ⟦ D ⟧Data A′ (p , i))
    → ∀ {j}
    → AllDataω Acc D x j
    → Pr′ (constr x)

  elim-wf : (x : A′ (p , i)) → ∀ {j} → Acc x j → Pr′ x
  elim-wf x (acc a) = subst Pr′ (constr∘split x) (elimData-wf (split x) a)

  elimData-wf (k , x) a
    = indCon (lookupCon D k) (motives k) x a
    where
      indIndArg
        : (C : ConDesc P V I)
        → (x : ⟦ C ⟧IndArg A′ (p , v))
        → ∀ {j} → AllIndArgω Acc C x j
        → MotiveIndArg C x
      indIndArg (var _) x a = elim-wf x a
      indIndArg (π ia S C) x a = fun< ia > (λ s → indIndArg C (app< ia > x s) (a s))
      indIndArg (A ⊗ B) (xa , xb) (aa , ab)
        = indIndArg A xa aa
        , indIndArg B xb ab

      indCon
        : (C   : ConDesc P V I)
          {mk  : ∀ {i} → ⟦ C ⟧Con A′ (p , v , i) → ⟦ D ⟧Data A′ (p , i)}
          (mot : MotiveCon C (λ x → Pr′ (constr (mk x))))
          (x   : ⟦ C ⟧Con A′ (p , v , i))
        → ∀ {j} → AllConω Acc C x j
        → Pr′ (constr (mk x))
      indCon (var _) mot refl a = mot
      indCon (π ia _ C) mot (s , x) a = indCon C (app< ia > mot s) x a
      indCon (A ⊗ B) mot (xa , xb) (aa , ab)
        = indCon B (mot xa (indIndArg A xa aa)) xb ab

  elim : (x : A′ (p , i)) → Pr′ x
  elim x = elim-wf x (wf x)

deriveElim : Arrows Motives (Pred′ I λ i → (x : A′ (p , i)) → Pr′ x)
deriveElim = curryₙ (λ m → pred′ I _ λ i → elim m)
