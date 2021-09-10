{-# OPTIONS --safe --without-K #-}

module Generics.Desc where

open import Generics.Prelude hiding (lookup)
open import Generics.Telescope


_≤ℓ_ : (a b : Level) → Set
a ≤ℓ b = b ≡ a ⊔ b


data Desc (P : Telescope ⊤) (V I : ExTele P) ℓ : Setω where
  var : (((p , v) : Σ[ P ⇒ V ]) → ⟦ I ⟧tel p) → Desc P V I ℓ
  π   : ∀ {ℓ′} (p : ℓ′ ≤ℓ ℓ) (ai : ArgInfo)
        (S : Σ[ P ⇒ V ] → Set ℓ′)
        (C : Desc P (V ⊢< ai > S) I ℓ)
      → Desc P V I ℓ
  _⊗_ : (A B : Desc P V I ℓ) → Desc P V I ℓ


mutual

  ⟦_⟧ : ∀ {P} {V I : ExTele P} {ℓ₁} (C : Desc P V I ℓ₁) ℓ₂
      → (Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂))
      → (Σ[ P ⇒ V ] → Set (ℓ₁ ⊔ ℓ₂))
  ⟦ var i     ⟧ ℓ₂ X pv@(p , _) = X (p , i pv)
  ⟦ A ⊗ B     ⟧ ℓ₂ X pv = ⟦ A ⟧ ℓ₂ X pv × ⟦ B ⟧ ℓ₂ X pv
  ⟦ π e i S C ⟧ ℓ₂ X pv = ⟦⟧ᵇ ℓ₂ e i X S C pv

  ⟦⟧ᵇ : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂ ℓ₃} ℓ₄
       → ℓ₁ ≡ ℓ₂ ⊔ ℓ₃
       → (ai : ArgInfo)
       → (Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄))
       → (S : Σ[ P ⇒ V ] → Set ℓ₂)
       → Desc P (V ⊢< ai > S) I ℓ₃
       → Σ[ P ⇒ V ] → Set (ℓ₁ ⊔ ℓ₄)
  ⟦⟧ᵇ ℓ₄ refl i X S C pv@(p , v) = (s : < relevance i > S pv) → ⟦ C ⟧ ℓ₄ X (p , v , s)

mutual
  Extend : ∀ {P} {V I : ExTele P} {ℓ₁} (C : Desc P V I ℓ₁) ℓ₂
         → (Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂))
         → Σ[ P ⇒ V & I ] → Set (ℓ₁ ⊔ ℓ₂ ⊔ levelOfTel I)
  Extend {I = I} {ℓ₁} (var x) ℓ₂ X pvi@(p , v , i) = Lift (ℓ₁ ⊔ ℓ₂ ⊔ levelOfTel I) (i ≡ x (p , v))
  Extend (A ⊗ B    ) ℓ₂ X pvi@(p , v , _) = ⟦ A ⟧ ℓ₂ X (p , v) × Extend B ℓ₂ X pvi
  Extend (π e i S C) ℓ₂ X pvi = Extendᵇ ℓ₂ e i X S C pvi

  Extendᵇ : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂ ℓ₃} ℓ₄
          → ℓ₁ ≡ ℓ₂ ⊔ ℓ₃
          → (ai : ArgInfo)
          → (Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄))
          → (S : Σ[ P ⇒ V ] → Set ℓ₂)
          → Desc P (V ⊢< ai > S)  I ℓ₃
          → Σ[ P ⇒ V & I ] → Set (ℓ₁ ⊔ ℓ₄ ⊔ levelOfTel I)
  Extendᵇ ℓ₄ refl ia X S C pvi@(p , v , i) = Σ[ s ∈ < relevance ia > S (p , v) ] Extend C ℓ₄ X (p , (v , s) , i)

data DataDesc P (I : ExTele P) ℓ : ℕ → Setω where
  []  : DataDesc P I ℓ 0
  _∷_ : ∀ {n} (C : Desc P ε I ℓ) (D : DataDesc P I ℓ n) → DataDesc P I ℓ (suc n)


lookup : ∀ {P} {I : ExTele P} {ℓ n} → DataDesc P I ℓ n → Fin n → Desc P ε I ℓ
lookup (C ∷ D) (zero ) = C
lookup (C ∷ D) (suc k) = lookup D k

⟦_⟧Data : ∀ {P} {I : ExTele P} {ℓ₁ n} (D : DataDesc P I ℓ₁ n) ℓ₂
    → (Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂             ))
    → (Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂ ⊔ levelOfTel I))
⟦_⟧Data {P} {I} {ℓ₁} {n} D ℓ₂ X (p , i) = Σ[ k ∈ Fin n ] Extend (lookup D k) ℓ₂ X (p , tt , i)

data μ {P} {I : ExTele P} {ℓ n} (D : DataDesc P I ℓ n) (pi : Σ[ P ⇒ I ])
     : Set (ℓ ⊔ levelOfTel I) where
  ⟨_⟩ : ⟦ D ⟧Data (levelOfTel I) (μ D) pi → μ D pi

⟨_⟩⁻¹ : ∀ {P} {I : ExTele P} {ℓ n} {D : DataDesc P I ℓ n} {pi}
      → μ D pi → ⟦ D ⟧Data (levelOfTel I) (μ D) pi
⟨ ⟨ x ⟩ ⟩⁻¹ = x

mutual
  All⟦⟧ : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂} (C : Desc P V I ℓ₁)
          (X  : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂)) {c}
          (Pr : ∀ {pi} → X pi → Set c)
        → ∀ {pv} → ⟦ C ⟧ ℓ₂ X pv → Set (c ⊔ ℓ₁)
  All⟦⟧ {ℓ₁ = ℓ} (var i) X {c} Pr x   = Lift (ℓ ⊔ c) (Pr x)
  All⟦⟧ (A ⊗ B    ) X Pr (⟦A⟧ , ⟦B⟧) = All⟦⟧ A X Pr ⟦A⟧ × All⟦⟧ B X Pr ⟦B⟧
  All⟦⟧ (π e i S C) X Pr x = All⟦⟧ᵇ e i X S C Pr x

  All⟦⟧ᵇ : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
        (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
        (ia : ArgInfo)
        (X : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄)) {c}
        (S : Σ[ P ⇒ V ] → Set ℓ₂)
        (C : Desc P (V ⊢< ia > S) I ℓ₃)
        (Pr : ∀ {pi} → X pi → Set c)
       → ∀ {pv} → ⟦⟧ᵇ ℓ₄ e ia X S C pv → Set (c ⊔ ℓ₁)
  All⟦⟧ᵇ refl ia X S C Pr {pv} x = (s : < relevance ia > S pv) → All⟦⟧ C X Pr (x s)

mutual
  AllExtend : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂} (C : Desc P V I ℓ₁)
              (X  : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂)) {c}
              (Pr : ∀ {pi} → X pi → Set c)
            → ∀ {pvi} → Extend C ℓ₂ X pvi → Set (c ⊔ ℓ₁)
  AllExtend (var i) X Pr x   = Lift _ ⊤
  AllExtend (A ⊗ B) X Pr (⟦A⟧ , EB) = All⟦⟧ A X Pr ⟦A⟧ × AllExtend B X Pr EB
  AllExtend (π e i S C) X Pr x = AllExtendᵇ e i X S C Pr x

  AllExtendᵇ : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
               (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
               (ia : ArgInfo)
               (X : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄)) {c}
               (S : Σ[ P ⇒ V ] → Set ℓ₂)
               (C : Desc P (V ⊢< ia > S) I ℓ₃)
               (Pr : ∀ {pi} → X pi → Set c)
             → ∀ {pvi} → Extendᵇ ℓ₄ e ia X S C pvi → Set (c ⊔ ℓ₃)
  AllExtendᵇ refl _ X _ C Pr (_ , d) = AllExtend C X Pr d


All : ∀ {P} {I : ExTele P} {ℓ n} (D : DataDesc P I ℓ n) {c}
      (Pr : ∀ {pi} → μ D pi → Set c)
    → ∀ {pi} → μ D pi → Set (c ⊔ ℓ)
All D Pr ⟨ k , x ⟩ = AllExtend (lookup D k) (μ D) Pr x


module _ {P} {I : ExTele P} where

  mutual
    map⟦⟧ : ∀ {ℓ₁} ℓ₂ {A : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂)}
                   ℓ₃ {B : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₃)}
            (f : ∀ {pi} → A pi → B pi)
            {V} (C : Desc P V I ℓ₁)
          → ∀ {pv} → ⟦ C ⟧ ℓ₂ A pv → ⟦ C ⟧ ℓ₃ B pv
    map⟦⟧ ℓ₂ ℓ₃ f (var i) = f
    map⟦⟧ ℓ₂ ℓ₃ f (A ⊗ B) (⟦A⟧ , ⟦B⟧) = map⟦⟧ ℓ₂ ℓ₃ f A ⟦A⟧ , map⟦⟧ ℓ₂ ℓ₃ f B ⟦B⟧
    map⟦⟧ ℓ₂ ℓ₃ f (π p i S C) = map⟦⟧ᵇ ℓ₂ ℓ₃ f p i S C

    map⟦⟧ᵇ : ∀ {V} {ℓ₁ ℓ₂ ℓ₃} ℓ₄ ℓ₅
             {A  : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄)}
             {B  : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₅)}
             (f  : ∀ {pi} → A pi → B pi)
             (e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
             (ia : ArgInfo)
             (S  : Σ[ P ⇒ V ] → Set ℓ₂)
             (C  : Desc P (V ⊢< ia > S) I ℓ₃)
           → ∀ {pv} → ⟦⟧ᵇ ℓ₄ e ia A S C pv → ⟦⟧ᵇ ℓ₅ e ia B S C pv
    map⟦⟧ᵇ ℓ₄ ℓ₅ f refl i S C = map⟦⟧ ℓ₄ ℓ₅ f C ∘_

  mutual
    mapExtend : ∀ {ℓ₁} ℓ₂ {A : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂)}
                       ℓ₃ {B : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₃)}
                (f : ∀ {pi} → A pi → B pi)
                {V} (C : Desc P V I ℓ₁)
              → ∀ {pvi} → Extend C ℓ₂ A pvi → Extend C ℓ₃ B pvi
    mapExtend ℓ₂ ℓ₃ f (var _) (lift p) = lift p
    mapExtend ℓ₂ ℓ₃ f (A ⊗ B) (⟦A⟧ , EB) = map⟦⟧ ℓ₂ ℓ₃ f A ⟦A⟧ , mapExtend ℓ₂ ℓ₃ f B EB
    mapExtend ℓ₂ ℓ₃ f (π p i S C) x = mapExtendᵇ ℓ₂ ℓ₃ f p i S C x

    mapExtendᵇ : ∀ {V} {ℓ₁ ℓ₂ ℓ₃} ℓ₄ ℓ₅
                 {A  : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄)}
                 {B  : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₅)}
                 (f  : ∀ {pi} → A pi → B pi)
                 (e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
                 (ia : ArgInfo)
                 (S  : Σ[ P ⇒ V ] → Set ℓ₂)
                 (C  : Desc P (V ⊢< ia > S) I ℓ₃)
               → ∀ {pvi} → Extendᵇ ℓ₄ e ia A S C pvi → Extendᵇ ℓ₅ e ia B S C pvi
    mapExtendᵇ ℓ₄ ℓ₅ f refl i S C (s , x) = s , mapExtend ℓ₄ ℓ₅ f C x


  mapData : ∀ {ℓ₁} ℓ₂ {A : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂)}
                   ℓ₃ {B : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₃)}
           (f : ∀ {pi} → A pi → B pi)
           {n} (D : DataDesc P I ℓ₁ n)
       → ∀ {pi} → ⟦ D ⟧Data ℓ₂ A pi → ⟦ D ⟧Data ℓ₃ B pi
  mapData ℓ₂ ℓ₃ f D (k , x) = k , mapExtend ℓ₂ ℓ₃ f (lookup D k) x



  module _ (funext : ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x}
                   → (∀ x → f x ≡ g x) → f ≡ g) where

    mutual
      map⟦⟧-compose : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {X : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂)}
                                      {Y : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₃)}
                                      {Z : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₄)}
                      {f : ∀ {pi} → X pi → Y pi}
                      {g : ∀ {pi} → Y pi → Z pi}
                      {V} {C : Desc P V I ℓ₁}
                    → ∀ {pvi} (x : ⟦ C ⟧ ℓ₂ X pvi)
                    → map⟦⟧ ℓ₂ ℓ₄ (g ∘ f) C x ≡ map⟦⟧ ℓ₃ ℓ₄ g C (map⟦⟧ ℓ₂ ℓ₃ f C x)
      map⟦⟧-compose {C = var i} x = refl
      map⟦⟧-compose {C = A ⊗ B} (⟦A⟧ , ⟦B⟧) =
        cong₂ _,_ (map⟦⟧-compose {C = A} ⟦A⟧) (map⟦⟧-compose {C = B} ⟦B⟧)
      map⟦⟧-compose {C = π p i S C} x = map⟦⟧ᵇ-compose x

      map⟦⟧-id : ∀ {V} {ℓ₁ ℓ₂} {X : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂)}
                 {f : ∀ {pi} → X pi → X pi}
                 (f≗id : ∀ {pi} (x : X pi) → f x ≡ x)
                 (C : Desc P V I ℓ₁)
               → ∀ {pvi} (x : ⟦ C ⟧ ℓ₂ X pvi) → map⟦⟧ ℓ₂ ℓ₂ f C x ≡ x
      map⟦⟧-id f≗id (var i) x = f≗id x
      map⟦⟧-id f≗id (A ⊗ B) (a , b) = cong₂ _,_ (map⟦⟧-id f≗id A a) (map⟦⟧-id f≗id B b)
      map⟦⟧-id f≗id (π p i S C) x = map⟦⟧ᵇ-id f≗id p i C x

      map⟦⟧ᵇ-compose : ∀ {V} {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆}
                       {X  : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄)}
                       {Y  : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₅)}
                       {Z  : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₆)}
                       {f  : ∀ {pi} → X pi → Y pi}
                       {g  : ∀ {pi} → Y pi → Z pi}
                       {e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃}
                       {ia : ArgInfo}
                       {S  : Σ[ P ⇒ V ] → Set ℓ₂}
                       {C  : Desc P (V ⊢< ia > S) I ℓ₃}
                     → ∀ {pvi} (x : ⟦⟧ᵇ ℓ₄ e ia X S C pvi)
                     → map⟦⟧ᵇ ℓ₄ ℓ₆ (g ∘ f) e ia S C x
                       ≡ map⟦⟧ᵇ ℓ₅ ℓ₆ g e ia S C (map⟦⟧ᵇ ℓ₄ ℓ₅ f e ia S C x)
      map⟦⟧ᵇ-compose {e = refl} {C = C} x = funext (λ s → map⟦⟧-compose {C = C} (x s))

      map⟦⟧ᵇ-id : ∀ {V} {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {X : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄)}
                  {f : ∀ {pi} → X pi → X pi}
                  (f≗id : ∀ {pi} (x : X pi) → f x ≡ x)
                  (e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
                  (ia : ArgInfo)
                  {S  : Σ[ P ⇒ V ] → Set ℓ₂}
                  (C  : Desc P (V ⊢< ia > S) I ℓ₃)
                → ∀ {pvi} (x : ⟦⟧ᵇ ℓ₄ e ia X S C pvi)
                → map⟦⟧ᵇ ℓ₄ ℓ₄ f e ia S C x ≡ x
      map⟦⟧ᵇ-id f≗id refl i C x = funext (λ s → map⟦⟧-id f≗id C (x s))

    mutual
      mapExtend-compose : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {X : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂)}
                                          {Y : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₃)}
                                          {Z : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₄)}
                          {f : ∀ {pi} → X pi → Y pi}
                          {g : ∀ {pi} → Y pi → Z pi}
                          {V} {C : Desc P V I ℓ₁}
                        → ∀ {pvi} (x : Extend C ℓ₂ X pvi)
                        → mapExtend ℓ₂ ℓ₄ (g ∘ f) C x ≡ mapExtend ℓ₃ ℓ₄ g C (mapExtend ℓ₂ ℓ₃ f C x)
      mapExtend-compose {C = var i} x = refl
      mapExtend-compose {C = A ⊗ B} (⟦A⟧ , EB) =
        cong₂ _,_ (map⟦⟧-compose {C = A} ⟦A⟧) (mapExtend-compose {C = B} EB)
      mapExtend-compose {C = π p i S C} x = mapExtendᵇ-compose x


      mapExtend-id : ∀ {ℓ₁ ℓ₂} {X : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂)}
                     {f    : ∀ {pi} → X pi → X pi}
                     (f≗id : ∀ {pi} (x : X pi) → f x ≡ x)
                     {V} (C : Desc P V I ℓ₁)
                   → ∀ {pvi} (x : Extend C ℓ₂ X pvi)
                   → mapExtend ℓ₂ ℓ₂ f C x ≡ x
      mapExtend-id f≗id (var i) x = refl
      mapExtend-id f≗id (A ⊗ B) (a , b) = cong₂ _,_ (map⟦⟧-id f≗id A a) (mapExtend-id f≗id B b)
      mapExtend-id f≗id (π p i S C) x = mapExtendᵇ-id f≗id p i C x


      mapExtendᵇ-compose : ∀ {V} {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆}
                           {X  : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄)}
                           {Y  : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₅)}
                           {Z  : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₆)}
                           {f  : ∀ {pi} → X pi → Y pi}
                           {g  : ∀ {pi} → Y pi → Z pi}
                           {e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃}
                           {ia : ArgInfo}
                           {S  : Σ[ P ⇒ V ] → Set ℓ₂}
                           {C  : Desc P (V ⊢< ia > S) I ℓ₃}
                        → ∀ {pvi} (x : Extendᵇ ℓ₄ e ia X S C pvi)
                        → mapExtendᵇ ℓ₄ ℓ₆ (g ∘ f) e ia S C x
                          ≡ mapExtendᵇ ℓ₅ ℓ₆ g e ia S C (mapExtendᵇ ℓ₄ ℓ₅ f e ia S C x)
      mapExtendᵇ-compose {f = f} {g} {e = refl} {C = C} (s , x) =
        cong (s ,_) (mapExtend-compose {f = f} {g} {C = C} x)


      mapExtendᵇ-id : ∀ {V} {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {X : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄)}
                     {f    : ∀ {pi} → X pi → X pi}
                     (f≗id : ∀ {pi} (x : X pi) → f x ≡ x)
                     (e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
                     (ia : ArgInfo)
                     {S  : Σ[ P ⇒ V ] → Set ℓ₂}
                     (C  : Desc P (V ⊢< ia > S) I ℓ₃)
                   → ∀ {pvi} (x : Extendᵇ ℓ₄ e ia X S C pvi)
                   → mapExtendᵇ ℓ₄ ℓ₄ f e ia S C x ≡ x
      mapExtendᵇ-id f≗id refl i C (s , x) = cong (s ,_) (mapExtend-id f≗id C x)

    mapData-compose : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
                     {A : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂)}
                     {B : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₃)}
                     {C : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₄)}
                     {f : ∀ {pi} → A pi → B pi}
                     {g : ∀ {pi} → B pi → C pi}
                     {n} {D : DataDesc P I ℓ₁ n}
                 → ∀ {pi} (x : ⟦ D ⟧Data ℓ₂ A pi)
                 → mapData ℓ₂ ℓ₄ (g ∘ f) D x ≡ mapData ℓ₃ ℓ₄ g D (mapData ℓ₂ ℓ₃ f D x)
    mapData-compose {f = f} {g} {D = D} (k , x) =
      cong (k ,_) (mapExtend-compose {f = f} {g} {C = lookup D k} x)


    mapData-id : ∀ {ℓ₁ ℓ₂} {X : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂)}
                {f    : ∀ {pi} → X pi → X pi}
                (f≗id : ∀ {pi} (x : X pi) → f x ≡ x)
                {n} {D : DataDesc P I ℓ₁ n}
            → ∀ {pi} (x : ⟦ D ⟧Data ℓ₂ X pi) → mapData ℓ₂ ℓ₂ f D x ≡ x
    mapData-id f≗id {D = D} (k , x) = cong (k ,_) (mapExtend-id f≗id (lookup D k) x)

mutual
  mapAll⟦⟧ : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂ ℓ₃} (C : Desc P V I ℓ₁)
             {X : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂)}
             {Y : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₃)}
             (f : ∀ {pi} → X pi → Y pi)
             {c} (Pr : ∀ {pi} → Y pi → Set c)
             {pv} {x : ⟦ C ⟧ ℓ₂ X pv}
           → All⟦⟧ C X (Pr ∘ f) x
           → All⟦⟧ C Y Pr (map⟦⟧ ℓ₂ ℓ₃ f C x)
  mapAll⟦⟧ (var i) f Pr H = H
  mapAll⟦⟧ (A ⊗ B) f Pr (HA , HB) = mapAll⟦⟧ A f Pr HA , mapAll⟦⟧ B f Pr HB
  mapAll⟦⟧ (π p i S C) f Pr H = mapAll⟦⟧ᵇ f Pr p i C H

  mapAll⟦⟧ᵇ : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅}
              {X  : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄)}
              {Y  : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₅)}
              (f  : ∀ {pi} → X pi → Y pi)
              {c} (Pr : ∀ {pi} → Y pi → Set c)
              (e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
              (ia : ArgInfo)
              {S  : Σ[ P ⇒ V ] → Set ℓ₂}
              (C  : Desc P (V ⊢< ia > S) I ℓ₃)
            → ∀ {pvi} {x : ⟦⟧ᵇ ℓ₄ e ia X S C pvi}
            → All⟦⟧ᵇ e ia X S C (Pr ∘ f) x
            → All⟦⟧ᵇ e ia Y S C Pr (map⟦⟧ᵇ ℓ₄ ℓ₅ f e ia S C x)
  mapAll⟦⟧ᵇ f Pr refl i C H s = mapAll⟦⟧ C f Pr (H s)

mutual
  mapAllExtend : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂ ℓ₃} (C : Desc P V I ℓ₁)
                 {X : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₂)}
                 {Y : Σ[ P ⇒ I ] → Set (ℓ₁ ⊔ ℓ₃)}
                 (f : ∀ {pi} → X pi → Y pi)
                 {c} (Pr : ∀ {pi} → Y pi → Set c)
                 {pvi} {x : Extend C ℓ₂ X pvi}
               → AllExtend C X (Pr ∘ f) x
               → AllExtend C Y Pr (mapExtend ℓ₂ ℓ₃ f C x)
  mapAllExtend (var i) f Pr H = H
  mapAllExtend (A ⊗ B) f Pr (HA , HB) = mapAll⟦⟧ A f Pr HA , mapAllExtend B f Pr HB
  mapAllExtend (π p i S C) f Pr H = mapAllExtendᵇ f Pr p i C H

  mapAllExtendᵇ : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅}
                  {X  : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₄)}
                  {Y  : Σ[ P ⇒ I ] → Set (ℓ₃ ⊔ ℓ₅)}
                  (f  : ∀ {pi} → X pi → Y pi)
                  {c} (Pr : ∀ {pi} → Y pi → Set c)
                  (e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
                  (ia : ArgInfo)
                  {S  : Σ[ P ⇒ V ] → Set ℓ₂}
                  (C  : Desc P (V ⊢< ia > S) I ℓ₃)
                → ∀ {pvi} {x : Extendᵇ ℓ₄ e ia X S C pvi}
                → AllExtendᵇ e ia X S C (Pr ∘ f) x
                → AllExtendᵇ e ia Y S C Pr (mapExtendᵇ ℓ₄ ℓ₅ f e ia S C x)
  mapAllExtendᵇ f Pr refl _ C H = mapAllExtend C f Pr H
