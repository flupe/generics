{-# OPTIONS --safe #-}

module Generics.Constructions.Injective where

open import Generics.Prelude hiding (lookup; pi; curry; icong)
open import Generics.Telescope
open import Generics.Desc
open import Generics.All
open import Generics.HasDesc
open import Relation.Binary.PropositionalEquality.Properties

PathOver : ∀ {i j} {A : Set i} (B : A → Set j) {x y : A}
            (p : x ≡ y)
            (u : B x) (v : B y)
         → Set j
PathOver B refl u v = u ≡ v

module _
  {P I ℓ} {A : Indexed P I ℓ} (H : HasDesc {P} {I} {ℓ} A)
  {p}
  where

  open HasDesc H
  
  private
    variable
      V       : ExTele P
      i i₁ i₂ : ⟦ I ⟧tel p
      v v₁ v₂ : ⟦ V ⟧tel p
      c ℓ′    : Level


  countArgs : ConDesc P V I → ℕ
  countArgs (var _) = zero
  countArgs (π _ _ C) = suc (countArgs C)
  countArgs (_ ⊗ B) = suc (countArgs B)

  -- | Compute level of projection
  levelProj : (C : ConDesc P V I) (m : Fin (countArgs C)) → Level
  levelProj (π {ℓ′} ai S C) zero = ℓ′
  levelProj (π ai S C) (suc m) = levelProj C m
  levelProj (A ⊗ B) zero = levelIndArg A ℓ
  levelProj (A ⊗ B) (suc m) = levelProj B m

  -- TODO (for Lucas of tomorrow):
  -- ⟦ v₁ ≡ v₂ ⟧

  -- private
  --   proj₂-id : ∀ {a} {A : Set a} {ℓB : A → Level} {B : ∀ x → Set (ℓB x)}
  --              {k : A} {x y : B k}
  --            → _≡ω_ {A = Σℓω A B} (k , x) (k , y)
  --            → x ≡ y
  --   proj₂-id refl = refl

  --   unconstrr : ∀ {k i} {x : ⟦ _ ⟧Con A′ (p , tt , i)}
  --                       {y : ⟦ _ ⟧Con A′ (p , tt , i)}
  --             → constr (k , x) ≡ constr (k , y)
  --             → x ≡ y
  --   unconstrr p = proj₂-id (constr-injective p)

  -- unconstr : ∀ {i₁ i₂} (ieq : i₁ ≡ i₂) {k}
  --            {x₁ : ⟦ lookupCon D k ⟧Con A′ (p , tt , i₁)}
  --            {x₂ : ⟦ lookupCon D k ⟧Con A′ (p , tt , i₂)}
  --          → subst (A′ ∘ (p ,_)) ieq (constr (k , x₁)) ≡ constr (k , x₂)
  --          → subst (λ i → ⟦ lookupCon D k ⟧Con A′ (p , tt , i)) ieq x₁ ≡ x₂
  -- unconstr refl p = proj₂-id (constr-injective p)

           

  -------------------------------
  -- Types of injectivity proofs

  levelInjective : (C : ConDesc P V I) → Level → Level
  levelInjective (var x) c = levelOfTel I ⊔ ℓ ⊔ c
  levelInjective (π {ℓ′} ai S C) c = ℓ′ ⊔ levelInjective C c
  levelInjective (A ⊗ B) c = levelIndArg A ℓ ⊔ levelInjective B c


  mutual
    InjectiveCon
      : (C : ConDesc P V I) (m : Fin (countArgs C))
        (mk₁ : ∀ {i₁} → ⟦ C ⟧Con A′ (p , v₁ , i₁) → A′ (p , i₁))
        (mk₂ : ∀ {i₂} → ⟦ C ⟧Con A′ (p , v₂ , i₂) → A′ (p , i₂))
      → Set (levelInjective C (levelProj C m))
    InjectiveCon {V} {v₁} {v₂} (π {ℓ′} (n , ai) S C) (suc m) mk₁ mk₂
      = {s₁ : < relevance ai > S (_ , v₁)} 
        {s₂ : < relevance ai > S (_ , v₂)}
      → InjectiveCon C m (λ x → mk₁ (s₁ , x)) (λ x → mk₂ (s₂ , x))
    InjectiveCon {V} {v₁} {v₂} (A ⊗ B) (suc m) mk₁ mk₂
      = {f₁ : ⟦ A ⟧IndArg A′ (_ , v₁)}
        {f₂ : ⟦ A ⟧IndArg A′ (_ , v₂)}
      → InjectiveCon B m (λ x → mk₁ (f₁ , x)) (λ x → mk₂ (f₂ , x))
    InjectiveCon (A ⊗ B) zero mk₁ mk₂ = {!!}
    InjectiveCon (π ai S C) zero mk₁ mk₂ = {!!}

    InjectiveConLift
      : ∀ {V V′ : ExTele P} (C : ConDesc P V′ I) {c}
        {v₁  v₂  : ⟦ V  ⟧tel p}
        {v′₁ v′₂ : ⟦ V′ ⟧tel p}
        {X : ⟦ P , V ⟧xtel → Set c}
        (mk₁ : ∀ {i₁} → ⟦ C ⟧Con A′ (p , v′₁ , i₁) → A′ (p , i₁))
        (mk₂ : ∀ {i₂} → ⟦ C ⟧Con A′ (p , v′₂ , i₂) → A′ (p , i₂))
        (x₁ : X (p , v₁))
        (x₂ : X (p , v₂))
        (v≡v : v₁ ≡ v₂)
      → Set (levelInjective C c)
    InjectiveConLift (var f) {v′₁ = v′₁} {v′₂} {X} mk₁ mk₂ x₁ x₂ v≡v
      = (ieq : f (p , v′₁) ≡ f (p , v′₂))
        (ceq : subst (A′ ∘ (p ,_)) ieq (mk₁ refl) ≡ mk₂ refl)
      → subst (X ∘ (p ,_)) v≡v x₁ ≡ x₂
    InjectiveConLift (π (n , ai) S C) {X = X} mk₁ mk₂ x₁ x₂ v≡v
      = {s₁ : < relevance ai > S (p , _)} 
        {s₂ : < relevance ai > S (p , _)}
      → InjectiveConLift C {X = X} (λ x → mk₁ (s₁ , x)) (λ x → mk₂ (s₂ , x)) x₁ x₂ v≡v
    InjectiveConLift (A ⊗ B) {v′₁ = v′₁} {v′₂} {X} mk₁ mk₂ x₁ x₂ v≡v
      = {f₁ : ⟦ A ⟧IndArg A′ (_ , v′₁)}
        {f₂ : ⟦ A ⟧IndArg A′ (_ , v′₂)}
      → InjectiveConLift B {X = X} (λ x → mk₁ (f₁ , x)) (λ x → mk₂ (f₂ , x)) x₁ x₂ v≡v

    -- first, we gather all arguments for left and right A′ values

    -- InjectiveCon C′ m mk (π (n , ai) S C) mk₁ mk₂
    --   = {s₁ : < relevance ai > S _}
    --     {s₂ : < relevance ai > S _}
    --   → InjectiveCon C′ m mk C (λ x → mk₁ (s₁ , x)) λ x → mk₂ (s₂ , x)
    -- InjectiveCon C′ m mk (A ⊗ B) mk₁ mk₂
    --   = {f₁ : ⟦ A ⟧IndArg A′ _}
    --     {f₂ : ⟦ A ⟧IndArg A′ _}
    --   → InjectiveCon C′ m mk B (λ x → mk₁ (f₁ , x)) λ x → mk₂ (f₂ , x)

    -- -- we now have all arguments to prouce two values of A′
    -- -- for the same kth constructor
    -- -- it's time to find the type of the proof

    -- -- base case: projecting on first arg, no lifting necessary
    -- InjectiveCon {V} {v₁} {v₂} (π ai S C) zero mk (var f) mk₁ mk₂
    --   = (ieq : f (p , v₁) ≡ f (p , v₂))
    --   → subst (A′ ∘ (p ,_)) ieq (mk (mk₁ refl)) ≡ mk (mk₂ refl)
    --   → proj₁ (mk₁ refl) ≡ proj₁ (mk₂ refl)
    -- InjectiveCon {V} {v₁} {v₂} (A ⊗ B) zero mk (var f) mk₁ mk₂
    --   = (ieq : f (p , v₁) ≡ f (p , v₂))
    --   → subst (A′ ∘ (p ,_)) ieq (mk (mk₁ refl)) ≡ mk (mk₂ refl)
    --   → proj₁ (mk₁ refl) ≡ proj₁ (mk₂ refl)

    
    
    -- otherwise, we have to lift a few things
    -- InjectiveCon {V} {v₁} {v₂} (π ai S C) (suc m) mk (var f) mk₁ mk₂
    --   = (ieq : f (p , v₁) ≡ f (p , v₂))
    --   → subst (A′ ∘ (p ,_)) ieq (mk (mk₁ refl)) ≡ mk (mk₂ refl)
    --   → InjectiveConLift C m {!!} {!!} {!!} {!!}
    -- InjectiveCon {V} {v₁} {v₂} (A ⊗ B) (suc m) mk (var f) mk₁ mk₂
    --   = (ieq : f (p , v₁) ≡ f (p , v₂))
    --   → subst (A′ ∘ (p ,_)) ieq (mk (mk₁ refl)) ≡ mk (mk₂ refl)
    --   → {!!}




  -- Injective : ∀ k (let C = lookupCon D k) (m : Fin (countArgs C))
  --           → Set (levelInjective C (levelProj C m))
  -- Injective k m = InjectiveCon _ m (λ x → constr (k , x)) _ id id

{-

  deriveInjective : ∀ k m → Injective k m
  deriveInjective k m = injCon (lookupCon D k) m (lookupCon D k)
    where
      injCon
        : (C′  : ConDesc P ε I) (m : Fin (countArgs C′))
          {mk  : ∀ {i} → ⟦ C′ ⟧Con A′ (p , tt , i) → A′ (p , i)}
          (C   : ConDesc P V I)
          {mk₁ : ∀ {i₁} → ⟦ C ⟧Con A′ (p , v₁ , i₁) → ⟦ C′ ⟧Con A′ (p , tt , i₁)}
          {mk₂ : ∀ {i₂} → ⟦ C ⟧Con A′ (p , v₂ , i₂) → ⟦ C′ ⟧Con A′ (p , tt , i₂)}
        → InjectiveCon C′ m mk C mk₁ mk₂

      -- we proceed until the end of the constructor
      injCon C′ m (π ai S C) = injCon C′ m C
      injCon C′ m (A ⊗ B)    = injCon C′ m B

      -- at the end, base case when projecting on fist arg
      injCon (π ai S C) zero (var x) ieq xeq = {!!}
      injCon (A ⊗ B)    zero (var x) ieq xeq = {!!}

      -- else, LIFT
      injCon (π ai S C′) (suc m) (var x) = {!!}
      injCon (C′ ⊗ C′₁) (suc m) (var x) = {!!}
{-



  deriveInjective′ : ∀ k m
                    (ieq : i₁ ≡ i₂)
                    {x₁ : ⟦ _ ⟧Con A′ (p , tt , i₁)}
                    {x₂ : ⟦ _ ⟧Con A′ (p , tt , i₂)}
                   → subst (λ i → ⟦ _ ⟧Con A′ (p , tt , i)) ieq x₁ ≡ x₂
                   → {!!}
  deriveInjective′ = {!!}
  
-}

-}
