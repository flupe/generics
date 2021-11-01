{-# OPTIONS --safe #-}

open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc
open import Generics.All
open import Generics.HasDesc
import Generics.Helpers as Helpers


module Generics.Constructions.Elim {P I ℓ} {A : Indexed P I ℓ} where

module _ (H : HasDesc A) (open HasDesc H)
         {p c} (Pr : Pred′ I (λ i → A′ (p , i) → Set c))
         where

  private
    variable
      V : ExTele P
      i : ⟦ I ⟧tel p
      v : ⟦ V ⟧tel p
  
  Pr′ : A′ (p , i) → Set c
  Pr′ {i} = unpred′ I _ Pr i
  
  
  --------------------------
  -- Types of methods
  
  levelElimIndArg levelElimCon : ConDesc P V I → Level
  
  levelElimIndArg (var x) = c
  levelElimIndArg (π {ℓ} i S C) = ℓ ⊔ levelElimIndArg C
  levelElimIndArg (A ⊗ B) = levelElimIndArg A ⊔ levelElimIndArg B
  
  levelElimCon (var x) = c
  levelElimCon (π {ℓ′} i S C) = ℓ′ ⊔ levelElimCon C
  levelElimCon (A ⊗ B) = levelIndArg A ℓ ⊔ levelElimIndArg A ⊔ levelElimCon B
  
  MethodIndArg : (C : ConDesc P V I)
               → ⟦ C ⟧IndArg A′ (p , v)
               → Set (levelElimIndArg C)
  MethodIndArg (var x    ) X = Pr′ X
  MethodIndArg (π ia S C) X = Π< ia > (S _) (MethodIndArg C ∘ app< ia > X)
  MethodIndArg (A ⊗ B) (mA , mB) = MethodIndArg A mA × MethodIndArg B mB
  
  MethodCon : (C : ConDesc P V I)
            → (∀ {i} → ⟦ C ⟧Con A′ (p , v , i) → Set c)
            → Set (levelElimCon C)
  MethodCon (var x) f = f refl
  MethodCon (π ia S C) f = Π< ia > (S _) (λ s → MethodCon C (f ∘ (s ,_)))
  MethodCon (A ⊗ B) f = {g  : ⟦ A ⟧IndArg A′ (p , _)}
                        (Pg : MethodIndArg A g)
                      → MethodCon B (f ∘ (g ,_))
  
  Methods : ∀ k → Set (levelElimCon (lookupCon D k))
  Methods k = MethodCon (lookupCon D k) λ x → Pr′ (constr (k , x))
  
  
  --------------------------
  -- Eliminator
  
  module _ (methods : Els Methods) where
  
    elimData-wf
      : (x : ⟦ D ⟧Data A′ (p , i))
      → AllDataω Acc D x
      → Pr′ (constr x)
  
    elim-wf : (x : A′ (p , i)) → Acc x → Pr′ x
    elim-wf x (acc a) = subst Pr′ (constr∘split x) (elimData-wf (split x) a)
  
    elimData-wf (k , x) a
      = elimCon (lookupCon D k) (methods k) x a
      where
        elimIndArg
          : (C : ConDesc P V I)
          → (x : ⟦ C ⟧IndArg A′ (p , v))
          → AllIndArgω Acc C x
          → MethodIndArg C x
        elimIndArg (var _) x a = elim-wf x a
        elimIndArg (π ia S C) x a = fun< ia > (λ s → elimIndArg C (app< ia > x s) (a s))
        elimIndArg (A ⊗ B) (xa , xb) (aa , ab)
          = elimIndArg A xa aa
          , elimIndArg B xb ab
  
        elimCon
          : (C   : ConDesc P V I)
            {mk  : ∀ {i} → ⟦ C ⟧Con A′ (p , v , i) → ⟦ D ⟧Data A′ (p , i)}
            (mot : MethodCon C (λ x → Pr′ (constr (mk x))))
            (x   : ⟦ C ⟧Con A′ (p , v , i))
          → AllConω Acc C x
          → Pr′ (constr (mk x))
        elimCon (var _) mot refl a = mot
        elimCon (π ia _ C) mot (s , x) a = elimCon C (app< ia > mot s) x a
        elimCon (A ⊗ B) mot (xa , xb) (aa , ab)
          = elimCon B (mot (elimIndArg A xa aa)) xb ab
  
    elim′ : (x : A′ (p , i)) → Pr′ x
    elim′ x = elim-wf x (wf x)
  
  deriveElim : Arrows Methods (Pred′ I λ i → (x : A′ (p , i)) → Pr′ x)
  deriveElim = curryₙ (λ m → pred′ I _ λ i → elim′ m)

elim : ∀ ⦃ H : HasDesc A ⦄ (open HasDesc H) {p c} (Pr : Pred′ I (λ i → A′ (p , i) → Set c))
     → Arrows (Methods H Pr) (Pred′ I λ i → (x : A′ (p , i)) → Pr′ H Pr x)
elim ⦃ H ⦄ Pr = deriveElim H Pr
