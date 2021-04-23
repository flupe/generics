{-# OPTIONS --rewriting #-}

module Generics.Constructions.Elim where

open import Agda.Builtin.Equality.Rewrite

open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc
open import Generics.HasDesc

import Generics.Constructions.Induction as Induction


module Elim {P} {I : ExTele P} {ℓ} {A : Indexed P I ℓ} (H : HasDesc {P} {I} {ℓ} A)
            {c} (Pr : Pred P I (uncurry P I A) c) where

      open HasDesc H

      Pr′ : {pi : Σ[ P ⇒ I ]} → uncurry P I A pi → Set c
      Pr′ {pi} = uncurry P I Pr pi

      -- induction hypothesis: every recursive occurence satisfies Pr
      IH : ∀ (C : Desc P ε I ℓ) {pi} → Extend C ℓ A′ pi → Set (ℓ ⊔ c)
      IH C x = AllExtend C A′ Pr′ x

      Method : Fin n → Set (levelTel P ⊔ levelTel I ⊔ ℓ ⊔ c)
      Method k = ∀ {pi} {x : Extend (lookup D k)  ℓ A′ pi}
               → IH (lookup D k) x
               → Pr′ (constr (k , x))

      Methods : SetList n
      Methods = tabulate (const (levelTel P ⊔ levelTel I ⊔ ℓ ⊔ c)) Method

      Pr″ : ∀ {pi} → μ D pi → Set c
      Pr″ = Pr′ ∘ from

      module Ind = Induction Pr″

      module _ (methods : Members Methods) where

         to-hypothesis : ∀ {pi} (X : μ D pi) → All D Pr″ X → Pr″ X
         to-hypothesis {pi} ⟨ k , x ⟩ all
           rewrite sym (constr-coh (k , x)) = method (mapAllExtend C from Pr′ all)
           where
             C = lookup D k

             method : ∀ {pi} {x : Extend C ℓ A′ pi} → IH C x → Pr′ (constr (k , x))
             method = lookupTabulate _ _ methods k

         elim : ∀ {pi} (x : A′ pi) → Pr′ x
         elim x rewrite sym (from∘to x) = Ind.ind to-hypothesis (to x)

module _ {P} {I : ExTele P} {ℓ} {A : Indexed P I ℓ} (H : HasDesc {P} {I} {ℓ} A)
         {c} (Pr : Pred P I (uncurry P I A) c) where

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

    motive⟦⟧ : ∀ {V} (C : Desc P V I ℓ) → Σ[ P ⇒ V ] → Set (level⟦⟧ C ℓ)
    motive⟦⟧ (var x) pv@(p , v) = A′ (p , x pv)
    motive⟦⟧ (π e i S C) pv = motive⟦⟧ᵇ e i S C pv
    motive⟦⟧ (A ⊗ B) pv = motive⟦⟧ A pv × motive⟦⟧ B pv

    motive⟦⟧ᵇ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) i (S : Σ[ P ⇒ V ] → Set ℓ₂) (C : Desc P (V ⊢< relevance i > S)  I ℓ)
             → Σ[ P ⇒ V ] → Set (ℓ₂ ⊔ level⟦⟧ C ℓ)
    motive⟦⟧ᵇ refl (arg-info visible   relevant  ) S C pv@(p , v) =  ( x : S pv ) → motive⟦⟧ C (p , v , x)
    motive⟦⟧ᵇ refl (arg-info visible   irrelevant) S C pv@(p , v) = .( x : S pv ) → motive⟦⟧ C (p , v , irrv x)
    motive⟦⟧ᵇ refl (arg-info hidden    relevant  ) S C pv@(p , v) =  { x : S pv } → motive⟦⟧ C (p , v , x)
    motive⟦⟧ᵇ refl (arg-info hidden    irrelevant) S C pv@(p , v) = .{ x : S pv } → motive⟦⟧ C (p , v , irrv x)
    motive⟦⟧ᵇ refl (arg-info instance′ relevant  ) S C pv@(p , v) =  ⦃ x : S pv ⦄ → motive⟦⟧ C (p , v , x)
    motive⟦⟧ᵇ refl (arg-info instance′ irrelevant) S C pv@(p , v) = .⦃ x : S pv ⦄ → motive⟦⟧ C (p , v , irrv x)

  mutual

    mott : ∀ {V} {C : Desc P V I ℓ} {pv} → motive⟦⟧ C pv → ⟦ C ⟧ ℓ A′ pv
    mott {C = var x} = id
    mott {C = π e i S C} {pv} m = mott′ e i S C pv m
    mott {C = A ⊗ B} (mA , mB) = mott {C = A} mA , mott {C = B} mB

    mott′ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) i (S : Σ[ P ⇒ V ] → Set ℓ₂) (C : Desc P (V ⊢< relevance i > S)  I ℓ)
            (pv : Σ[ P ⇒ V ]) → motive⟦⟧ᵇ e i S C pv → ⟦⟧ᵇ ℓ e i A′ S C pv
    mott′ refl (arg-info visible   relevant  ) S C pv@(p , v) m x = mott {C = C} (m x)
    mott′ refl (arg-info visible   irrelevant) S C pv@(p , v) m (irrv x) = mott {C = C} (m x)
    mott′ refl (arg-info hidden    relevant  ) S C pv@(p , v) m x = mott {C = C} (m {x})
    mott′ refl (arg-info hidden    irrelevant) S C pv@(p , v) m (irrv x) = mott {C = C} (m {x})
    mott′ refl (arg-info instance′ relevant  ) S C pv@(p , v) m x = mott {C = C} (m ⦃ x ⦄)
    mott′ refl (arg-info instance′ irrelevant) S C pv@(p , v) m (irrv x) = mott {C = C} (m ⦃ x ⦄)

    mmott : ∀ {V} {C : Desc P V I ℓ} {pv} (x : ⟦ C ⟧ ℓ A′ pv) → All⟦⟧ C A′ Pr′ x → motive⟦⟧ C pv
    mmott {C = var i} x H = x
    mmott {C = π e i S C} x H = mmott′ e i S C _ x H
    mmott {C = A ⊗ B} (xa , xb) (HA , HB) = mmott {C = A} xa HA , mmott {C = B} xb HB


    mmott′ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) i (S : Σ[ P ⇒ V ] → Set ℓ₂) (C : Desc P (V ⊢< relevance i > S)  I ℓ)
            (pv : Σ[ P ⇒ V ]) (x : ⟦⟧ᵇ ℓ e i A′ S C pv) → All⟦⟧ᵇ e i A′ S C Pr′ x → motive⟦⟧ᵇ e i S C pv
    mmott′ refl (arg-info visible   relevant  ) S C pv x H s     = mmott {C = C} (x s) (H s)
    mmott′ refl (arg-info visible   irrelevant) S C pv x H s     = mmott {C = C} (x (irrv s)) (H (irrv s))
    mmott′ refl (arg-info hidden    relevant  ) S C pv x H {s}   = mmott {C = C} (x s) (H s)
    mmott′ refl (arg-info hidden    irrelevant) S C pv x H {s}   = mmott {C = C} (x (irrv s)) (H (irrv s))
    mmott′ refl (arg-info instance′ relevant  ) S C pv x H ⦃ s ⦄ = mmott {C = C} (x s) (H s)
    mmott′ refl (arg-info instance′ irrelevant) S C pv x H ⦃ s ⦄ = mmott {C = C} (x (irrv s)) (H (irrv s))

  mutual

    motive⟦⟧P : ∀ {V} (C : Desc P V I ℓ) (pv : Σ[ P ⇒ V ]) → motive⟦⟧ C pv → Set (level⟦⟧ C c)
    motive⟦⟧P (var x    ) pv X = Pr′ X
    motive⟦⟧P (π e i S C) pv X = motive⟦⟧P′ e i S C pv X
    motive⟦⟧P (A ⊗ B) pv (mA , mB) = motive⟦⟧P A pv mA × motive⟦⟧P B pv mB

    motive⟦⟧P′ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) i (S : Σ[ P ⇒ V ] → Set ℓ₂) (C : Desc P (V ⊢< relevance i > S)  I ℓ)
                (pv : Σ[ P ⇒ V ]) → motive⟦⟧ᵇ e i S C pv → Set (ℓ₂ ⊔ level⟦⟧ C c)
    motive⟦⟧P′ refl (arg-info visible   relevant  ) S C pv@(p , v) m =  ( x : S pv ) → motive⟦⟧P C (p , v , x) (m x)
    motive⟦⟧P′ refl (arg-info visible   irrelevant) S C pv@(p , v) m = .( x : S pv ) → motive⟦⟧P C (p , v , irrv x) (m x)
    motive⟦⟧P′ refl (arg-info hidden    relevant  ) S C pv@(p , v) m =  { x : S pv } → motive⟦⟧P C (p , v , x) (m {x})
    motive⟦⟧P′ refl (arg-info hidden    irrelevant) S C pv@(p , v) m = .{ x : S pv } → motive⟦⟧P C (p , v , irrv x) (m {x})
    motive⟦⟧P′ refl (arg-info instance′ relevant  ) S C pv@(p , v) m =  ⦃ x : S pv ⦄ → motive⟦⟧P C (p , v , x) (m ⦃ x ⦄)
    motive⟦⟧P′ refl (arg-info instance′ irrelevant) S C pv@(p , v) m = .⦃ x : S pv ⦄ → motive⟦⟧P C (p , v , irrv x) (m ⦃ x ⦄)

  mutual

    mottt : ∀ {V} {C : Desc P V I ℓ} {pv} {m : motive⟦⟧ C pv} → All⟦⟧ C A′ Pr′ (mott {C = C} m) → motive⟦⟧P C pv m
    mottt {C = var i    } (lift H) = H
    mottt {C = π e i S C} H = mmottt′ e i S C _ H
    mottt {C = A ⊗ B    } (HA , HB) = mottt {C = A} HA , mottt {C = B} HB

    mmottt′ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) i (S : Σ[ P ⇒ V ] → Set ℓ₂) (C : Desc P (V ⊢< relevance i > S)  I ℓ)
            (pv : Σ[ P ⇒ V ]) {m : motive⟦⟧ᵇ e i S C pv} → All⟦⟧ᵇ e i A′ S C Pr′ (mott′ e i S C pv m) → motive⟦⟧P′ e i S C pv m
    mmottt′ refl (arg-info visible   relevant  ) S C pv H s     = mottt {C = C} (H s)
    mmottt′ refl (arg-info visible   irrelevant) S C pv H s     = mottt {C = C} (H (irrv s))
    mmottt′ refl (arg-info hidden    relevant  ) S C pv H {s}   = mottt {C = C} (H s)
    mmottt′ refl (arg-info hidden    irrelevant) S C pv H {s}   = mottt {C = C} (H (irrv s))
    mmottt′ refl (arg-info instance′ relevant  ) S C pv H ⦃ s ⦄ = mottt {C = C} (H s)
    mmottt′ refl (arg-info instance′ irrelevant) S C pv H ⦃ s ⦄ = mottt {C = C} (H (irrv s))

  mutual

    motiveE : ∀ {V} (C : Desc P V I ℓ)
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
            → (C : Desc P (V ⊢< relevance i > S)  I ℓ)
            → ((p , v) : Σ[ P ⇒ V ])
            → (∀ {i′} (x : Extendᵇ ℓ e i A′ S C (p , v , i′)) → Set c)
            → Set (ℓ₂ ⊔ level C)
    motiveE′ refl (arg-info visible   relevant  ) S C pv@(p , v) f =  ( x : S pv ) → motiveE C (p , v , x) (f ∘ (x ,_))
    motiveE′ refl (arg-info visible   irrelevant) S C pv@(p , v) f = .( x : S pv ) → motiveE C (p , v , irrv x) (f ∘ (irrv x ,_))
    motiveE′ refl (arg-info hidden    relevant  ) S C pv@(p , v) f =  { x : S pv } → motiveE C (p , v , x) (f ∘ (x ,_))
    motiveE′ refl (arg-info hidden    irrelevant) S C pv@(p , v) f = .{ x : S pv } → motiveE C (p , v , irrv x) (f ∘ (irrv x ,_))
    motiveE′ refl (arg-info instance′ relevant  ) S C pv@(p , v) f =  ⦃ x : S pv ⦄ → motiveE C (p , v , x) (f ∘ (x ,_))
    motiveE′ refl (arg-info instance′ irrelevant) S C pv@(p , v) f = .⦃ x : S pv ⦄ → motiveE C (p , v , irrv x) (f ∘ (irrv x ,_))

  motive : ∀ k → Set (levelTel P ⊔ level (lookup D k))
  motive k = ∀ {p : tel P tt} → motiveE (lookup D k) (p , tt) λ x → Pr′ (constr (k , x))

  postulate rew : ∀ {V} {C : Desc P V I ℓ} {pv : Σ[ P ⇒ V ]}
                  (x : ⟦ C ⟧ ℓ A′ pv)
                  (H : All⟦⟧ C A′ Pr′ x)
                → mott {C = C} (mmott {C = C} x H) ≡ x

  -- TODO: remove this rewrite rule, actually prove it
  {-# REWRITE rew #-}

  module _ {k} where

    mutual
      mmmE : ∀ {V} {C : Desc P V I ℓ} {(p , v , i) : Σ[ P ⇒ V & I ]}
          → (x : Extend C ℓ A′ (p , v , i))
          → {f : ∀ {i} (x : Extend C ℓ A′ (p , v , i)) → Set c}
          → motiveE C (p , v) f
          → (g : Extend C ℓ A′ (p , v , i) → Extend (lookup D k) ℓ A′ (p , tt , i))
          → (f x → Pr′ (constr (k , g x)))
          → AllExtend C A′ Pr′ x
          → Pr′ (constr (k , g x))
      mmmE {C = var x} (lift refl) m f tie _ = tie m
      mmmE {C = π e i S C} x m mk tie H = mmmE′ e i S C x m mk tie H
      mmmE {C = A ⊗ B} (xa , xb) m f tie (HA , HB) =
        mmmE {C = B} xb (m (mmott {C = A} xa HA) (mottt {C = A} HA)) (f ∘ (xa ,_)) tie HB

      mmmE′ : ∀ {V}{ℓ₁ ℓ₂}
            → (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ)
            → (i : ArgInfo)
            → (S : Σ[ P ⇒ V ] → Set ℓ₂)
            → (C : Desc P (V ⊢< relevance i > S)  I ℓ)
            → {(p , v , i′) : Σ[ P ⇒ V & I ]}
            → (x : Extendᵇ ℓ e i A′ S C (p , v , i′))
            → {f : ∀ {i′} → Extendᵇ ℓ e i A′ S C (p , v , i′) → Set c}
            → motiveE′ e i S C (p , v) f
            → (g : Extendᵇ ℓ e i A′ S C (p , v , i′) → Extend (lookup D k) ℓ A′ (p , tt , i′))
            → (f x → Pr′ (constr (k , g x)))
            → AllExtendᵇ e i A′ S C Pr′ x
            → Pr′ (constr (k , g x))
      mmmE′ refl (arg-info visible   relevant  ) S C (s      , d) {f} m mk tie H = mmmE {C = C} d (m s) (mk ∘ (s ,_)) tie H
      mmmE′ refl (arg-info visible   irrelevant) S C (irrv s , d) {f} m mk tie H = mmmE {C = C} d (m s) (mk ∘ (irrv s ,_)) tie H
      mmmE′ refl (arg-info hidden    relevant  ) S C (s      , d) {f} m mk tie H = mmmE {C = C} d (m {s}) (mk ∘ (s ,_)) tie H
      mmmE′ refl (arg-info hidden    irrelevant) S C (irrv s , d) {f} m mk tie H = mmmE {C = C} d (m {s}) (mk ∘ (irrv s ,_)) tie H
      mmmE′ refl (arg-info instance′ relevant  ) S C (s      , d) {f} m mk tie H = mmmE {C = C} d (m ⦃ s ⦄) (mk ∘ (s ,_)) tie H
      mmmE′ refl (arg-info instance′ irrelevant) S C (irrv s , d) {f} m mk tie H = mmmE {C = C} d (m ⦃ s ⦄) (mk ∘ (irrv s ,_)) tie H

{-

  GoodMethods : SetList n
  GoodMethods = tabulate _ motive

  motive⇒method : ∀ k → motive k → Method k
  motive⇒method k m {pvi} {x} IH = mmmE {C = lookup D k} x m id id IH

  convert : Members GoodMethods → Members Methods
  convert m = mapTabulate motive⇒method m

  elim′ : Members GoodMethods → ∀ {pi} (x : A′ pi) → Pr′ x
  elim′ m = Elim.elim H Pr (convert m)

  elim″ : CurryMembers {AS = GoodMethods} elim′
  elim″ = curryMembers elim′

-}
