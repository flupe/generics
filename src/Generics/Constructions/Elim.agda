{-# OPTIONS --safe #-}

module Generics.Constructions.Elim where

open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc
open import Generics.HasDesc
import Generics.Constructions.Induction as Induction


module Elim {P} {I : ExTele P} {ℓ} (A : Curried′ P I ℓ) (H : HasDesc {P} {I} {ℓ} A)
            {c} (Pr : ∀ {pi} → uncurry′ P I A pi → Set c) where

      open HasDesc H
      
      -- induction hypothesis: every recursive occurence satisfies Pr
      IH : ∀ (C : CDesc P ε I ℓ) {pi} → Extend C ℓ A′ pi → Set (ℓ ⊔ c)
      IH C x = AllExtend C A′ Pr x

      con-method : Fin n → Set (levelTel P ⊔ levelTel I ⊔ ℓ ⊔ c)
      con-method k = ∀ {pi} {x : Extend (lookup D k)  ℓ A′ pi} → IH (lookup D k) x → Pr (constr (k , x))

      elim-methods : Vec (Set (levelTel P ⊔ levelTel I ⊔ ℓ ⊔ c)) n
      elim-methods = tabulate con-method

      Pr′ : ∀ {pi} → μ D pi → Set c
      Pr′ = Pr ∘ from

      module Ind = Induction Pr′

      module _ (methods : Members elim-methods) where

         to-hypothesis : ∀ {pi} (X : μ D pi) → All D Pr′ X → Pr′ X
         to-hypothesis {pi} ⟨ k , x ⟩ all
           rewrite sym (constr-coh (k , x)) = method (mapAllExtend C from Pr all)
           where
             C = lookup D k

             method : ∀ {pi} {x : Extend C ℓ A′ pi} → IH C x → Pr (constr (k , x))
             method = subst id (lookupTabulate con-method k) (lookupMember methods k)

         elim : ∀ {pi} (x : A′ pi) → Pr x
         elim x rewrite sym (from∘to x) = Ind.ind to-hypothesis (to x)


module _ {P} {I : ExTele P} {ℓ} (A : Curried′ P I ℓ) (H : HasDesc {P} {I} {ℓ} A)
         {c} (Pr : ∀ {pi} → uncurry′ P I A pi → Set c) where

  open HasDesc H
  open Elim A H Pr

  --  con-method : Fin n → Set (levelTel P ⊔ levelTel I ⊔ ℓ ⊔ c)
  --  con-method k = ∀ {pi} {x : Extend (lookup D k) ℓ A′ pi} → IH (lookup D k) x → Pr (constr (k , x))

  mutual

    level⟦⟧ : ∀ {V} (C : CDesc P V I ℓ) → Level → Level
    level⟦⟧ (var x) c = c
    level⟦⟧ (π {ℓ} p i S C) c = ℓ ⊔ level⟦⟧ C c
    level⟦⟧ (A ⊗ B) c = level⟦⟧ A c ⊔ level⟦⟧ B c

    level : ∀ {V} (C : CDesc P V I ℓ) → Level
    level (var x) = c
    level (π {ℓ} p i S C) = ℓ ⊔ level C
    level (A ⊗ B) = level⟦⟧ A ℓ ⊔ level⟦⟧ A c ⊔ level B
   
    motive⟦⟧ : ∀ {V} (C : CDesc P V I ℓ) → Σ[ P ⇒ V ] → Set (level⟦⟧ C ℓ)
    motive⟦⟧ (var x) pv@(p , v) = A′ (p , x pv)
    motive⟦⟧ (π e i S C) pv = motive⟦⟧′ e i S C pv
    motive⟦⟧ (A ⊗ B) pv = motive⟦⟧ A pv × motive⟦⟧ B pv

    motive⟦⟧′ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) i (S : Σ[ P ⇒ V ] → Set ℓ₂) (C : CDesc P (V ⊢< relevance i > S)  I ℓ)
             → Σ[ P ⇒ V ] → Set (ℓ₂ ⊔ level⟦⟧ C ℓ)
    motive⟦⟧′ refl (arg-info visible   relevant  ) S C pv@(p , v) =  ( x : S pv ) → motive⟦⟧ C (p , v , relv x)
    motive⟦⟧′ refl (arg-info visible   irrelevant) S C pv@(p , v) = .( x : S pv ) → motive⟦⟧ C (p , v , irrv x)
    motive⟦⟧′ refl (arg-info hidden    relevant  ) S C pv@(p , v) =  { x : S pv } → motive⟦⟧ C (p , v , relv x)
    motive⟦⟧′ refl (arg-info hidden    irrelevant) S C pv@(p , v) = .{ x : S pv } → motive⟦⟧ C (p , v , irrv x)
    motive⟦⟧′ refl (arg-info instance′ relevant  ) S C pv@(p , v) =  ⦃ x : S pv ⦄ → motive⟦⟧ C (p , v , relv x)
    motive⟦⟧′ refl (arg-info instance′ irrelevant) S C pv@(p , v) = .⦃ x : S pv ⦄ → motive⟦⟧ C (p , v , irrv x)

    mott : ∀ {V} {C : CDesc P V I ℓ} {pv} → motive⟦⟧ C pv → C⟦ C ⟧ ℓ A′ pv
    mott {C = var x} = id
    mott {C = π e i S C} {pv} m = mott′ e i S C pv m
    mott {C = A ⊗ B} (mA , mB) = mott {C = A} mA , mott {C = B} mB

    mott′ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) i (S : Σ[ P ⇒ V ] → Set ℓ₂) (C : CDesc P (V ⊢< relevance i > S)  I ℓ)
            (pv : Σ[ P ⇒ V ]) → motive⟦⟧′ e i S C pv → C⟦⟧b ℓ e i A′ S C pv
    mott′ refl (arg-info visible   relevant  ) S C pv@(p , v) m (relv x) = mott {C = C} (m x)
    mott′ refl (arg-info visible   irrelevant) S C pv@(p , v) m (irrv x) = mott {C = C} (m x)
    mott′ refl (arg-info hidden    relevant  ) S C pv@(p , v) m (relv x) = mott {C = C} (m {x})
    mott′ refl (arg-info hidden    irrelevant) S C pv@(p , v) m (irrv x) = mott {C = C} (m {x})
    mott′ refl (arg-info instance′ relevant  ) S C pv@(p , v) m (relv x) = mott {C = C} (m ⦃ x ⦄)
    mott′ refl (arg-info instance′ irrelevant) S C pv@(p , v) m (irrv x) = mott {C = C} (m ⦃ x ⦄)

    motive⟦⟧P : ∀ {V} (C : CDesc P V I ℓ) (pv : Σ[ P ⇒ V ]) → motive⟦⟧ C pv → Set (level⟦⟧ C c)
    motive⟦⟧P (var x    ) pv X = Pr X
    motive⟦⟧P (π e i S C) pv X = motive⟦⟧P′ e i S C pv X
    motive⟦⟧P (A ⊗ B) pv (mA , mB) = motive⟦⟧P A pv mA × motive⟦⟧P B pv mB

    motive⟦⟧P′ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) i (S : Σ[ P ⇒ V ] → Set ℓ₂) (C : CDesc P (V ⊢< relevance i > S)  I ℓ)
                (pv : Σ[ P ⇒ V ]) → motive⟦⟧′ e i S C pv → Set (ℓ₂ ⊔ level⟦⟧ C c)
    motive⟦⟧P′ refl (arg-info visible   relevant  ) S C pv@(p , v) m =  ( x : S pv ) → motive⟦⟧P C (p , v , relv x) (m x)
    motive⟦⟧P′ refl (arg-info visible   irrelevant) S C pv@(p , v) m = .( x : S pv ) → motive⟦⟧P C (p , v , irrv x) (m x)
    motive⟦⟧P′ refl (arg-info hidden    relevant  ) S C pv@(p , v) m =  { x : S pv } → motive⟦⟧P C (p , v , relv x) (m {x})
    motive⟦⟧P′ refl (arg-info hidden    irrelevant) S C pv@(p , v) m = .{ x : S pv } → motive⟦⟧P C (p , v , irrv x) (m {x})
    motive⟦⟧P′ refl (arg-info instance′ relevant  ) S C pv@(p , v) m =  ⦃ x : S pv ⦄ → motive⟦⟧P C (p , v , relv x) (m ⦃ x ⦄)
    motive⟦⟧P′ refl (arg-info instance′ irrelevant) S C pv@(p , v) m = .⦃ x : S pv ⦄ → motive⟦⟧P C (p , v , irrv x) (m ⦃ x ⦄)

    motiveE : ∀ {V} (C : CDesc P V I ℓ)
              ((p , v) : Σ[ P ⇒ V ])
            → (∀ {i} (x : Extend C ℓ A′ (p , v , i)) → Set c)
            → Set (level C)
    motiveE (var x) pv f = f (lift refl)
    motiveE (π e i S C) pv f = motiveE′ e i S C pv f
    motiveE (A ⊗ B) pv f =
      (g : motive⟦⟧ A pv) (Pg : motive⟦⟧P A pv g) → motiveE B pv (f ∘ (mott {C = A} g ,_))

    motiveE′ : ∀ {V} {ℓ₁ ℓ₂}
            → (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ)
            → (i : ArgInfo)
            → (S : Σ[ P ⇒ V ] → Set ℓ₂)
            → (C : CDesc P (V ⊢< relevance i > S)  I ℓ)
            → ((p , v) : Σ[ P ⇒ V ])
            → (∀ {i′} (x : Extendb ℓ e i A′ S C (p , v , i′)) → Set c)
            → Set (ℓ₂ ⊔ level C)
    motiveE′ refl (arg-info visible   relevant  ) S C pv@(p , v) f =  ( x : S pv ) → motiveE C (p , v , relv x) (f ∘ (relv x ,_)) 
    motiveE′ refl (arg-info visible   irrelevant) S C pv@(p , v) f = .( x : S pv ) → motiveE C (p , v , irrv x) (f ∘ (irrv x ,_)) 
    motiveE′ refl (arg-info hidden    relevant  ) S C pv@(p , v) f =  { x : S pv } → motiveE C (p , v , relv x) (f ∘ (relv x ,_)) 
    motiveE′ refl (arg-info hidden    irrelevant) S C pv@(p , v) f = .{ x : S pv } → motiveE C (p , v , irrv x) (f ∘ (irrv x ,_)) 
    motiveE′ refl (arg-info instance′ relevant  ) S C pv@(p , v) f =  ⦃ x : S pv ⦄ → motiveE C (p , v , relv x) (f ∘ (relv x ,_)) 
    motiveE′ refl (arg-info instance′ irrelevant) S C pv@(p , v) f = .⦃ x : S pv ⦄ → motiveE C (p , v , irrv x) (f ∘ (irrv x ,_)) 

    motive : ∀ k → Set (levelTel P ⊔ level (lookup D k))
    motive k = ∀ {p : tel P tt} → motiveE (lookup D k) (p , tt) λ x → Pr (constr (k , x))

    -- motive⇒method : ∀ {k} → motive k → con-method k
    -- motive⇒method m {x} IH = {!!}
