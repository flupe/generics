{-# OPTIONS --safe --without-K #-}
module Generics.Desc where

open import Generics.Prelude hiding (lookup)
open import Generics.Telescope

_≤ℓ_ : (a b : Level) → Set
a ≤ℓ b = b ≡ a ⊔ b

data CDesc (P : Telescope ⊤) (V I : ExTele P) ℓ : Setω where
  var : (((p , v) : Σ[ P ⇒ V ]) → tel I p) → CDesc P V I ℓ
  π   : ∀ {ℓ′} (p : ℓ′ ≤ℓ ℓ) (i : ArgInfo) (S : Σ[ P ⇒ V ] → Set ℓ′) → CDesc P (V ⊢< relevance i > S) I ℓ → CDesc P V I ℓ
  _⊗_ : (A B : CDesc P V I ℓ) → CDesc P V I ℓ

levelC′ levelC : ∀ {P} {V I : ExTele P} {ℓ} → CDesc P V I ℓ → Level → Level
levelC′ (var i        ) c = c
levelC′ (π {ℓ} p i S C) c = ℓ ⊔ levelC C c
levelC′ (A ⊗ B        ) c = levelC A c ⊔ levelC B c

levelC (var i        ) c = lzero
levelC (π {ℓ} p i S C) c = ℓ ⊔ levelC C c
levelC (A ⊗ B        ) c = levelC′ A c ⊔ levelC B c


mutual
  C⟦_⟧ : ∀ {P} {V I : ExTele P} {ℓ₁} (C : CDesc P V I ℓ₁) ℓ₂
       → (Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂))
       → (Σ[ P ⇒ V ] → Set (ℓ₁ ⊔ ℓ₂))
  C⟦ var i     ⟧ ℓ₂ X pv@(p , _) = X (p , i pv)
  C⟦ A ⊗ B     ⟧ ℓ₂ X pv = C⟦ A ⟧ ℓ₂ X pv × C⟦ B ⟧ ℓ₂ X pv
  C⟦ π e i S C ⟧ ℓ₂ X pv = C⟦⟧b ℓ₂ e i X S C pv

  C⟦⟧b : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂ ℓ₃} ℓ₄
       → ℓ₁ ≡ ℓ₂ ⊔ ℓ₃
       → (i : ArgInfo)
       → (Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄))
       → (S : Σ[ P ⇒ V ] → Set ℓ₂)
       → CDesc P (V ⊢< relevance i > S) I ℓ₃
       → Σ[ P ⇒ V ] → Set (ℓ₁ ⊔ ℓ₄)
  C⟦⟧b ℓ₄ refl i X S C pv@(p , v) = (s : < relevance i > S pv) → C⟦ C ⟧ ℓ₄ X (p , v , s)


mutual
  Extend : ∀ {P} {V I : ExTele P} {ℓ₁} (C : CDesc P V I ℓ₁) ℓ₂
         → (Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂))
         → Σ[ P ⇒ V & I ] → Set (ℓ₁ ⊔ ℓ₂ ⊔ levelTel I)
  Extend {I = I} {ℓ₁} (var x) ℓ₂ X pvi@(p , v , i) = Lift (ℓ₁ ⊔ ℓ₂ ⊔ levelTel I) (i ≡ x (p , v))
  Extend (A ⊗ B    ) ℓ₂ X pvi@(p , v , _) = C⟦ A ⟧ ℓ₂ X (p , v) × Extend B ℓ₂ X pvi
  Extend (π e i S C) ℓ₂ X pvi = Extendb ℓ₂ e i X S C pvi

  Extendb : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂ ℓ₃} ℓ₄
          → ℓ₁ ≡ ℓ₂ ⊔ ℓ₃
          → (i : ArgInfo)
          → (Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄))
          → (S : Σ[ P ⇒ V ] → Set ℓ₂)
          → CDesc P (V ⊢< relevance i > S)  I ℓ₃
          → Σ[ P ⇒ V & I ] → Set (ℓ₁ ⊔ ℓ₄ ⊔ levelTel I)
  Extendb ℓ₄ refl r X S C pvi@(p , v , i) = Σ[ s ∈ < relevance r > S (p , v) ] Extend C ℓ₄ X (p , (v , s) , i)


data Desc P (I : ExTele P) ℓ : ℕ → Setω where
  []  : Desc P I ℓ 0
  _∷_ : ∀ {n} (C : CDesc P ε I ℓ) (D : Desc P I ℓ n) → Desc P I ℓ (suc n)


lookup : ∀ {P} {I : ExTele P} {ℓ n} → Desc P I ℓ n → Fin n → CDesc P ε I ℓ
lookup (C ∷ D) (zero ) = C
lookup (C ∷ D) (suc k) = lookup D k

⟦_⟧ : ∀ {P} {I : ExTele P} {ℓ₁ n} (D : Desc P I ℓ₁ n) ℓ₂
    → (Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂             ))
    → (Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂ ⊔ levelTel I))
⟦_⟧ {P} {I} {ℓ₁} {n} D ℓ₂ X (p , i) = Σ[ k ∈ Fin n ] Extend (lookup D k) ℓ₂ X (p , tt , i)

data μ {P} {I : ExTele P} {ℓ n} (D : Desc P I ℓ n) (pi : Σ[ P ⇒ I ]) : Set (ℓ ⊔ levelTel I) where
  ⟨_⟩ : ⟦ D ⟧ (levelTel I) (μ D) pi → μ D pi

⟨_⟩⁻¹ : ∀ {P} {I : ExTele P} {ℓ n} {D : Desc P I ℓ n} {pi} → μ D pi → ⟦ D ⟧ (levelTel I) (μ D) pi
⟨ ⟨ x ⟩ ⟩⁻¹ = x

mutual
  All⟦⟧ : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂} (C : CDesc P V I ℓ₁)
          (X  : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂)) {c}
          (Pr : ∀ {pi} → X pi → Set c)
        → ∀ {pv} → C⟦ C ⟧ ℓ₂ X pv → Set (c ⊔ ℓ₁)
  All⟦⟧ {ℓ₁ = ℓ} (var i) X {c} Pr x   = Lift (ℓ ⊔ c) (Pr x)
  All⟦⟧ (A ⊗ B    ) X Pr (⟦A⟧ , ⟦B⟧) = All⟦⟧ A X Pr ⟦A⟧ × All⟦⟧ B X Pr ⟦B⟧
  All⟦⟧ (π e i S C) X Pr x = All⟦⟧b e i X S C Pr x

  All⟦⟧b : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
        (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
        (i : ArgInfo)
        (X : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄)) {c}
        (S : Σ[ P ⇒ V ] → Set ℓ₂)
        (C : CDesc P (V ⊢< relevance i > S) I ℓ₃)
        (Pr : ∀ {pi} → X pi → Set c)
       → ∀ {pv} → C⟦⟧b ℓ₄ e i X S C pv → Set (c ⊔ ℓ₁)
  All⟦⟧b refl i X S C Pr {pv} x = (s : < relevance i > S pv) → All⟦⟧ C X Pr (x s)

mutual
  AllExtend : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂} (C : CDesc P V I ℓ₁)
              (X  : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂)) {c}
              (Pr : ∀ {pi} → X pi → Set c)
            → ∀ {pvi} → Extend C ℓ₂ X pvi → Set (c ⊔ ℓ₁)
  AllExtend (var i) X Pr x   = Lift _ ⊤
  AllExtend (A ⊗ B) X Pr (⟦A⟧ , EB) = All⟦⟧ A X Pr ⟦A⟧ × AllExtend B X Pr EB
  AllExtend (π e i S C) X Pr x = AllExtendb e i X S C Pr x

  AllExtendb : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
               (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
               (i : ArgInfo)
               (X : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄)) {c}
               (S : Σ[ P ⇒ V ] → Set ℓ₂)
               (C : CDesc P (V ⊢< relevance i > S) I ℓ₃)
               (Pr : ∀ {pi} → X pi → Set c)
             → ∀ {pvi} → Extendb ℓ₄ e i X S C pvi → Set (c ⊔ ℓ₃)
  AllExtendb refl _ X _ C Pr (_ , d) = AllExtend C X Pr d


All : ∀ {P} {I : ExTele P} {ℓ n} (D : Desc P I ℓ n) {c}
      (Pr : ∀ {pi} → μ D pi → Set c)
    → ∀ {pi} → μ D pi → Set (c ⊔ ℓ)
All D Pr ⟨ k , x ⟩ = AllExtend (lookup D k) (μ D) Pr x


module _ {P} {I : ExTele P} where

  mutual
    map⟦⟧ : ∀ {ℓ₁} ℓ₂ {A : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂)}
                   ℓ₃ {B : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₃)}
            (f : ∀ {pi} → A pi → B pi)
            {V} (C : CDesc P V I ℓ₁)
          → ∀ {pv} → C⟦ C ⟧ ℓ₂ A pv → C⟦ C ⟧ ℓ₃ B pv
    map⟦⟧ ℓ₂ ℓ₃ f (var i) = f
    map⟦⟧ ℓ₂ ℓ₃ f (A ⊗ B) (⟦A⟧ , ⟦B⟧) = map⟦⟧ ℓ₂ ℓ₃ f A ⟦A⟧ , map⟦⟧ ℓ₂ ℓ₃ f B ⟦B⟧
    map⟦⟧ ℓ₂ ℓ₃ f (π p i S C) = map⟦⟧′ ℓ₂ ℓ₃ f p i S C

    map⟦⟧′ : ∀ {V} {ℓ₁ ℓ₂ ℓ₃} ℓ₄ ℓ₅
             {A : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄)}
             {B : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₅)}
             (f : ∀ {pi} → A pi → B pi)
             (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
             (i : ArgInfo)
             (S : Σ[ P ⇒ V ] → Set ℓ₂)
             (C : CDesc P (V ⊢< relevance i > S) I ℓ₃)
           → ∀ {pv} → C⟦⟧b ℓ₄ e i A S C pv → C⟦⟧b ℓ₅ e i B S C pv
    map⟦⟧′ ℓ₄ ℓ₅ f refl i S C = map⟦⟧ ℓ₄ ℓ₅ f C ∘_

  mutual
    mapExtend : ∀ {ℓ₁} ℓ₂ {A : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂)}
                       ℓ₃ {B : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₃)}
                (f : ∀ {pi} → A pi → B pi)
                {V} (C : CDesc P V I ℓ₁)
              → ∀ {pvi} → Extend C ℓ₂ A pvi → Extend C ℓ₃ B pvi
    mapExtend ℓ₂ ℓ₃ f (var _) (lift p) = lift p
    mapExtend ℓ₂ ℓ₃ f (A ⊗ B) (⟦A⟧ , EB) = map⟦⟧ ℓ₂ ℓ₃ f A ⟦A⟧ , mapExtend ℓ₂ ℓ₃ f B EB
    mapExtend ℓ₂ ℓ₃ f (π p i S C) x = mapExtend′ ℓ₂ ℓ₃ f p i S C x

    mapExtend′ : ∀ {V} {ℓ₁ ℓ₂ ℓ₃} ℓ₄ ℓ₅
                 {A : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄)}
                 {B : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₅)}
                 (f : ∀ {pi} → A pi → B pi)
                 (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
                 (i : ArgInfo)
                 (S : Σ[ P ⇒ V ] → Set ℓ₂)
                 (C : CDesc P (V ⊢< relevance i > S) I ℓ₃)
               → ∀ {pvi} → Extendb ℓ₄ e i A S C pvi → Extendb ℓ₅ e i B S C pvi
    mapExtend′ ℓ₄ ℓ₅ f refl i S C (s , x) = s , mapExtend ℓ₄ ℓ₅ f C x


  mapD : ∀ {ℓ₁} ℓ₂ {A : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂)}
                ℓ₃ {B : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₃)}
           (f : ∀ {pi} → A pi → B pi)
           {n} (D : Desc P I ℓ₁ n)
       → ∀ {pi} → ⟦ D ⟧ ℓ₂ A pi → ⟦ D ⟧ ℓ₃ B pi
  mapD ℓ₂ ℓ₃ f D (k , x) = k , mapExtend ℓ₂ ℓ₃ f (lookup D k) x



  module _ (funext : ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x}
                   → (∀ x → f x ≡ g x) → f ≡ g) where

    mutual
      map⟦⟧-compose : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {X : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂)}
                                      {Y : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₃)}
                                      {Z : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₄)}
                      {f : ∀ {pi} → X pi → Y pi}
                      {g : ∀ {pi} → Y pi → Z pi}
                      {V} {C : CDesc P V I ℓ₁}
                    → ∀ {pvi} (x : C⟦ C ⟧ ℓ₂ X pvi)
                    → map⟦⟧ ℓ₂ ℓ₄ (g ∘ f) C x ≡ map⟦⟧ ℓ₃ ℓ₄ g C (map⟦⟧ ℓ₂ ℓ₃ f C x)
      map⟦⟧-compose {C = var i} x = refl
      map⟦⟧-compose {C = A ⊗ B} (⟦A⟧ , ⟦B⟧) =
        cong₂ _,_ (map⟦⟧-compose {C = A} ⟦A⟧) (map⟦⟧-compose {C = B} ⟦B⟧)
      map⟦⟧-compose {C = π p i S C} x = map⟦⟧′-compose x

      map⟦⟧-id : ∀ {V} {ℓ₁ ℓ₂} {X : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂)}
                 {f : ∀ {pi} → X pi → X pi}
                 (f≗id : ∀ {pi} (x : X pi) → f x ≡ x)
                 (C : CDesc P V I ℓ₁)
               → ∀ {pvi} (x : C⟦ C ⟧ ℓ₂ X pvi) → map⟦⟧ ℓ₂ ℓ₂ f C x ≡ x
      map⟦⟧-id f≗id (var i) x = f≗id x
      map⟦⟧-id f≗id (A ⊗ B) (a , b) = cong₂ _,_ (map⟦⟧-id f≗id A a) (map⟦⟧-id f≗id B b)
      map⟦⟧-id f≗id (π p i S C) x = map⟦⟧′-id f≗id p i C x

      map⟦⟧′-compose : ∀ {V} {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆}
                       {X : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄)}
                       {Y : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₅)}
                       {Z : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₆)}
                       {f : ∀ {pi} → X pi → Y pi}
                       {g : ∀ {pi} → Y pi → Z pi}
                       {e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃}
                       {i : ArgInfo}
                       {S : Σ[ P ⇒ V ] → Set ℓ₂}
                       {C : CDesc P (V ⊢< relevance i > S) I ℓ₃}
                     → ∀ {pvi} (x : C⟦⟧b ℓ₄ e i X S C pvi)
                     → map⟦⟧′ ℓ₄ ℓ₆ (g ∘ f) e i S C x
                       ≡ map⟦⟧′ ℓ₅ ℓ₆ g e i S C (map⟦⟧′ ℓ₄ ℓ₅ f e i S C x)
      map⟦⟧′-compose {e = refl} {C = C} x = funext (λ s → map⟦⟧-compose {C = C} (x s))

      map⟦⟧′-id : ∀ {V} {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {X : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄)}
                  {f : ∀ {pi} → X pi → X pi}
                  (f≗id : ∀ {pi} (x : X pi) → f x ≡ x)
                  (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
                  (i : ArgInfo)
                  {S : Σ[ P ⇒ V ] → Set ℓ₂}
                  (C : CDesc P (V ⊢< relevance i > S) I ℓ₃)
                → ∀ {pvi} (x : C⟦⟧b ℓ₄ e i X S C pvi)
                → map⟦⟧′ ℓ₄ ℓ₄ f e i S C x ≡ x
      map⟦⟧′-id f≗id refl i C x = funext (λ s → map⟦⟧-id f≗id C (x s))

    mutual
      mapExtend-compose : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {X : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂)}
                                          {Y : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₃)}
                                          {Z : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₄)}
                          {f : ∀ {pi} → X pi → Y pi}
                          {g : ∀ {pi} → Y pi → Z pi}
                          {V} {C : CDesc P V I ℓ₁}
                        → ∀ {pvi} (x : Extend C ℓ₂ X pvi)
                        → mapExtend ℓ₂ ℓ₄ (g ∘ f) C x ≡ mapExtend ℓ₃ ℓ₄ g C (mapExtend ℓ₂ ℓ₃ f C x)
      mapExtend-compose {C = var i} x = refl
      mapExtend-compose {C = A ⊗ B} (⟦A⟧ , EB) =
        cong₂ _,_ (map⟦⟧-compose {C = A} ⟦A⟧) (mapExtend-compose {C = B} EB)
      mapExtend-compose {C = π p i S C} x = mapExtend′-compose x


      mapExtend-id : ∀ {ℓ₁ ℓ₂} {X : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂)}
                     {f    : ∀ {pi} → X pi → X pi}
                     (f≗id : ∀ {pi} (x : X pi) → f x ≡ x)
                     {V} (C : CDesc P V I ℓ₁)
                   → ∀ {pvi} (x : Extend C ℓ₂ X pvi)
                   → mapExtend ℓ₂ ℓ₂ f C x ≡ x
      mapExtend-id f≗id (var i) x = refl
      mapExtend-id f≗id (A ⊗ B) (a , b) = cong₂ _,_ (map⟦⟧-id f≗id A a) (mapExtend-id f≗id B b)
      mapExtend-id f≗id (π p i S C) x = mapExtend′-id f≗id p i C x


      mapExtend′-compose : ∀ {V} {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆}
                           {X : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄)}
                           {Y : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₅)}
                           {Z : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₆)}
                           {f : ∀ {pi} → X pi → Y pi}
                           {g : ∀ {pi} → Y pi → Z pi}
                           {e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃}
                           {i : ArgInfo}
                           {S : Σ[ P ⇒ V ] → Set ℓ₂}
                           {C : CDesc P (V ⊢< relevance i > S) I ℓ₃}
                        → ∀ {pvi} (x : Extendb ℓ₄ e i X S C pvi)
                        → mapExtend′ ℓ₄ ℓ₆ (g ∘ f) e i S C x
                          ≡ mapExtend′ ℓ₅ ℓ₆ g e i S C (mapExtend′ ℓ₄ ℓ₅ f e i S C x)
      mapExtend′-compose {f = f} {g} {e = refl} {C = C} (s , x) =
        cong (s ,_) (mapExtend-compose {f = f} {g} {C = C} x)


      mapExtend′-id : ∀ {V} {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {X : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄)}
                     {f    : ∀ {pi} → X pi → X pi}
                     (f≗id : ∀ {pi} (x : X pi) → f x ≡ x)
                     (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
                     (i : ArgInfo)
                     {S : Σ[ P ⇒ V ] → Set ℓ₂}
                     (C : CDesc P (V ⊢< relevance i > S) I ℓ₃)
                   → ∀ {pvi} (x : Extendb ℓ₄ e i X S C pvi)
                   → mapExtend′ ℓ₄ ℓ₄ f e i S C x ≡ x
      mapExtend′-id f≗id refl i C (s , x) = cong (s ,_) (mapExtend-id f≗id C x)

    mapD-compose : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
                     {A : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂)}
                     {B : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₃)}
                     {C : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₄)}
                     {f : ∀ {pi} → A pi → B pi}
                     {g : ∀ {pi} → B pi → C pi}
                     {n} {D : Desc P I ℓ₁ n}
                 → ∀ {pi} (x : ⟦ D ⟧ ℓ₂ A pi)
                 → mapD ℓ₂ ℓ₄ (g ∘ f) D x ≡ mapD ℓ₃ ℓ₄ g D (mapD ℓ₂ ℓ₃ f D x)
    mapD-compose {f = f} {g} {D = D} (k , x) =
      cong (k ,_) (mapExtend-compose {f = f} {g} {C = lookup D k} x)


    mapD-id : ∀ {ℓ₁ ℓ₂} {X : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂)}
                {f    : ∀ {pi} → X pi → X pi}
                (f≗id : ∀ {pi} (x : X pi) → f x ≡ x)
                {n} {D : Desc P I ℓ₁ n}
            → ∀ {pi} (x : ⟦ D ⟧ ℓ₂ X pi) → mapD ℓ₂ ℓ₂ f D x ≡ x
    mapD-id f≗id {D = D} (k , x) = cong (k ,_) (mapExtend-id f≗id (lookup D k) x)

mutual
  mapAll⟦⟧ : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂ ℓ₃} (C : CDesc P V I ℓ₁)
             {X : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂)}
             {Y : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₃)}
             (f : ∀ {pi} → X pi → Y pi)
             {c} (Pr : ∀ {pi} → Y pi → Set c)
             {pv} {x : C⟦ C ⟧ ℓ₂ X pv}
           → All⟦⟧ C X (Pr ∘ f) x
           → All⟦⟧ C Y Pr (map⟦⟧ ℓ₂ ℓ₃ f C x)
  mapAll⟦⟧ (var i) f Pr H = H
  mapAll⟦⟧ (A ⊗ B) f Pr (HA , HB) = mapAll⟦⟧ A f Pr HA , mapAll⟦⟧ B f Pr HB
  mapAll⟦⟧ (π p i S C) f Pr H = mapAll⟦⟧′ f Pr p i C H

  mapAll⟦⟧′ : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅}
              {X : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄)}
              {Y : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₅)}
              (f : ∀ {pi} → X pi → Y pi)
              {c} (Pr : ∀ {pi} → Y pi → Set c)
              (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
              (i : ArgInfo)
              {S : Σ[ P ⇒ V ] → Set ℓ₂}
              (C : CDesc P (V ⊢< relevance i > S) I ℓ₃)
            → ∀ {pvi} {x : C⟦⟧b ℓ₄ e i X S C pvi}
            → All⟦⟧b e i X S C (Pr ∘ f) x
            → All⟦⟧b e i Y S C Pr (map⟦⟧′ ℓ₄ ℓ₅ f e i S C x)
  mapAll⟦⟧′ f Pr refl i C H s = mapAll⟦⟧ C f Pr (H s)

mutual
  mapAllExtend : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂ ℓ₃} (C : CDesc P V I ℓ₁)
                 {X : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂)}
                 {Y : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₃)}
                 (f : ∀ {pi} → X pi → Y pi)
                 {c} (Pr : ∀ {pi} → Y pi → Set c)
                 {pvi} {x : Extend C ℓ₂ X pvi}
               → AllExtend C X (Pr ∘ f) x
               → AllExtend C Y Pr (mapExtend ℓ₂ ℓ₃ f C x)
  mapAllExtend (var i) f Pr H = H
  mapAllExtend (A ⊗ B) f Pr (HA , HB) = mapAll⟦⟧ A f Pr HA , mapAllExtend B f Pr HB
  mapAllExtend (π p i S C) f Pr H = mapAllExtend′ f Pr p i C H

  mapAllExtend′ : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅}
                  {X : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄)}
                  {Y : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₅)}
                  (f : ∀ {pi} → X pi → Y pi)
                  {c} (Pr : ∀ {pi} → Y pi → Set c)
                  (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
                  (i : ArgInfo)
                  {S : Σ[ P ⇒ V ] → Set ℓ₂}
                  (C : CDesc P (V ⊢< relevance i > S) I ℓ₃)
                → ∀ {pvi} {x : Extendb ℓ₄ e i X S C pvi}
                → AllExtendb e i X S C (Pr ∘ f) x
                → AllExtendb e i Y S C Pr (mapExtend′ ℓ₄ ℓ₅ f e i S C x)
  mapAllExtend′ f Pr refl _ C H = mapAllExtend C f Pr H
