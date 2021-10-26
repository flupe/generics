{-# OPTIONS --safe --without-K #-}

module Generics.Desc where

open import Generics.Prelude hiding (lookup)
open import Generics.Telescope


_≤ℓ_ : (a b : Level) → Set
a ≤ℓ b = b ≡ a ⊔ b


data ConDesc (P : Telescope ⊤) (V I : ExTele P) ℓ : Setω where
  var : (((p , v) : ⟦ P , V ⟧xtel) → ⟦ I ⟧tel p) → ConDesc P V I ℓ
  π   : ∀ {ℓ′} (p : ℓ′ ≤ℓ ℓ) (ai : ArgInfo)
        (S : ⟦ P , V ⟧xtel → Set ℓ′)
        (C : ConDesc P (V ⊢< ai > S) I ℓ)
      → ConDesc P V I ℓ
  _⊗_ : (A B : ConDesc P V I ℓ) → ConDesc P V I ℓ


⟦_⟧IndArg : ∀ {P} {V I : ExTele P} {ℓ₁} (C : ConDesc P V I ℓ₁) ℓ₂
    → (⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₂))
    → (⟦ P , V ⟧xtel → Set (ℓ₁ ⊔ ℓ₂))

IndArgᵇ : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂ ℓ₃} ℓ₄
     → ℓ₁ ≡ ℓ₂ ⊔ ℓ₃
     → (ai : ArgInfo)
     → (⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₄))
     → (S : ⟦ P , V ⟧xtel → Set ℓ₂)
     → ConDesc P (V ⊢< ai > S) I ℓ₃
     → ⟦ P , V ⟧xtel → Set (ℓ₁ ⊔ ℓ₄)

⟦ var i     ⟧IndArg ℓ₂ X pv@(p , _) = X (p , i pv)
⟦ A ⊗ B     ⟧IndArg ℓ₂ X pv = ⟦ A ⟧IndArg ℓ₂ X pv × ⟦ B ⟧IndArg ℓ₂ X pv
⟦ π e i S C ⟧IndArg ℓ₂ X pv = IndArgᵇ ℓ₂ e i X S C pv

IndArgᵇ ℓ₄ refl i X S C pv@(p , v) = (s : < relevance i > S pv) → ⟦ C ⟧IndArg ℓ₄ X (p , v , s)


⟦_⟧Con : ∀ {P} {V I : ExTele P} {ℓ₁} (C : ConDesc P V I ℓ₁) ℓ₂
       → (⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₂))
       → ⟦ P , V & I ⟧xtel → Set (ℓ₁ ⊔ ℓ₂ ⊔ levelOfTel I)

Conᵇ : ∀ {P} {V I : ExTele P} {ℓ₁ ℓ₂ ℓ₃} ℓ₄
        → ℓ₁ ≡ ℓ₂ ⊔ ℓ₃
        → (ai : ArgInfo)
        → (⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₄))
        → (S : ⟦ P , V ⟧xtel → Set ℓ₂)
        → ConDesc P (V ⊢< ai > S)  I ℓ₃
        → ⟦ P , V & I ⟧xtel → Set (ℓ₁ ⊔ ℓ₄ ⊔ levelOfTel I)

⟦_⟧Con {I = I} {ℓ₁} (var x) ℓ₂ X pvi@(p , v , i) = Lift (ℓ₁ ⊔ ℓ₂ ⊔ levelOfTel I) (i ≡ x (p , v))
⟦ A ⊗ B ⟧Con ℓ₂ X pvi@(p , v , _) = ⟦ A ⟧IndArg ℓ₂ X (p , v) × ⟦ B ⟧Con ℓ₂ X pvi
⟦ π e i S C ⟧Con ℓ₂ X pvi = Conᵇ ℓ₂ e i X S C pvi

Conᵇ ℓ₄ refl ia X S C pvi@(p , v , i) =
  Σ[ s ∈ < relevance ia > S (p , v) ] ⟦ C ⟧Con ℓ₄ X (p , (v , s) , i)


data DataDesc P (I : ExTele P) ℓ : ℕ → Setω where
  []  : DataDesc P I ℓ 0
  _∷_ : ∀ {n} (C : ConDesc P ε I ℓ) (D : DataDesc P I ℓ n) → DataDesc P I ℓ (suc n)


lookupCon : ∀ {P} {I : ExTele P} {ℓ n} → DataDesc P I ℓ n → Fin n → ConDesc P ε I ℓ
lookupCon (C ∷ D) (zero ) = C
lookupCon (C ∷ D) (suc k) = lookupCon D k


⟦_⟧Data : ∀ {P} {I : ExTele P} {ℓ₁ n} (D : DataDesc P I ℓ₁ n) ℓ₂
    → (⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₂             ))
    → (⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₂ ⊔ levelOfTel I))
⟦ D ⟧Data ℓ₂ X (p , i) =
  Σ[ k ∈ Fin _ ] ⟦ lookupCon D k ⟧Con ℓ₂ X (p , tt , i)


data μ {P} {I : ExTele P} {ℓ n} (D : DataDesc P I ℓ n) (pi : ⟦ P , I ⟧xtel)
     : Set (ℓ ⊔ levelOfTel I) where
  ⟨_⟩ : ⟦ D ⟧Data (levelOfTel I) (μ D) pi → μ D pi

⟨_⟩⁻¹ : ∀ {P} {I : ExTele P} {ℓ n} {D : DataDesc P I ℓ n} {pi}
      → μ D pi → ⟦ D ⟧Data (levelOfTel I) (μ D) pi
⟨ ⟨ x ⟩ ⟩⁻¹ = x

module _ {P} {I : ExTele P} {p} where
  
  AllIndArg : ∀ {V} {ℓ₁ ℓ₂} (C : ConDesc P V I ℓ₁)
          (X  : ⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₂)) {c}
          (Pr : ∀ {i} → X (p , i) → Set c)
        → ∀ {v} → ⟦ C ⟧IndArg ℓ₂ X (p , v) → Set (c ⊔ ℓ₁)

  AllIndArgᵇ : ∀ {V} {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
        (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
        (ia : ArgInfo)
        (X : ⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₄)) {c}
        (S : ⟦ P , V ⟧xtel → Set ℓ₂)
        (C : ConDesc P (V ⊢< ia > S) I ℓ₃)
        (Pr : ∀ {i} → X (p , i) → Set c)
       → ∀ {v} → IndArgᵇ ℓ₄ e ia X S C (p , v) → Set (c ⊔ ℓ₁)

  AllIndArg {ℓ₁ = ℓ} (var i) X {c = c} Pr x = Lift (ℓ ⊔ c) (Pr x)
  AllIndArg (A ⊗ B    ) X Pr (⟦A⟧ , ⟦B⟧) = AllIndArg A X Pr ⟦A⟧ × AllIndArg B X Pr ⟦B⟧
  AllIndArg (π e i S C) X Pr x = AllIndArgᵇ e i X S C Pr x
  
  AllIndArgᵇ refl ia X S C Pr {v} x = (s : < relevance ia > S (_ , v)) → AllIndArg C X Pr (x s)
  


  AllCon : ∀ {V} {ℓ₁ ℓ₂} (C : ConDesc P V I ℓ₁)
              (X  : ⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₂)) {c}
              (Pr : ∀ {i} → X (p , i) → Set c)
            → ∀ {v i} → ⟦ C ⟧Con ℓ₂ X (p , v , i) → Set (c ⊔ ℓ₁)

  AllConᵇ : ∀ {V} {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
               (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
               (ia : ArgInfo)
               (X : ⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₄)) {c}
               (S : ⟦ P , V ⟧xtel → Set ℓ₂)
               (C : ConDesc P (V ⊢< ia > S) I ℓ₃)
               (Pr : ∀ {i} → X (p , i) → Set c)
             → ∀ {v i} → Conᵇ ℓ₄ e ia X S C (p , v , i) → Set (c ⊔ ℓ₃)

  AllCon (var i) X Pr x   = Lift _ ⊤
  AllCon (A ⊗ B) X Pr (⟦A⟧ , EB) = AllIndArg A X Pr ⟦A⟧ × AllCon B X Pr EB
  AllCon (π e i S C) X Pr x = AllConᵇ e i X S C Pr x
  
  AllConᵇ refl _ X _ C Pr (_ , d) = AllCon C X Pr d
  

  
  All : ∀ {ℓ n} (D : DataDesc P I ℓ n) {c}
        (Pr : ∀ {i} → μ D (p , i) → Set c)
      → ∀ {i} → μ D (p , i) → Set (c ⊔ ℓ)
  All D Pr ⟨ k , x ⟩ = AllCon (lookupCon D k) (μ D) Pr x


  mapIndArg : ∀ {ℓ₁} ℓ₂ {A : ⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₂)}
                 ℓ₃ {B : ⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₃)}
          (f : ∀ {i} → A (p , i) → B (p , i))
          {V} (C : ConDesc P V I ℓ₁)
        → ∀ {v} → ⟦ C ⟧IndArg ℓ₂ A (p , v) → ⟦ C ⟧IndArg ℓ₃ B (p , v)
  mapIndArgᵇ : ∀ {V} {ℓ₁ ℓ₂ ℓ₃} ℓ₄ ℓ₅
           {A  : ⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₄)}
           {B  : ⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₅)}
           (f  : ∀ {i} → A (p , i) → B (p , i))
           (e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
           (ia : ArgInfo)
           (S  : ⟦ P , V ⟧xtel → Set ℓ₂)
           (C  : ConDesc P (V ⊢< ia > S) I ℓ₃)
         → ∀ {v} → IndArgᵇ ℓ₄ e ia A S C (p , v) → IndArgᵇ ℓ₅ e ia B S C (p , v)

  mapIndArg ℓ₂ ℓ₃ f (var i) = f
  mapIndArg ℓ₂ ℓ₃ f (A ⊗ B) (⟦A⟧ , ⟦B⟧) = mapIndArg ℓ₂ ℓ₃ f A ⟦A⟧ , mapIndArg ℓ₂ ℓ₃ f B ⟦B⟧
  mapIndArg ℓ₂ ℓ₃ f (π p i S C) = mapIndArgᵇ ℓ₂ ℓ₃ f p i S C
  mapIndArgᵇ ℓ₄ ℓ₅ f refl i S C = mapIndArg ℓ₄ ℓ₅ f C ∘_



  mapCon : ∀ {ℓ₁} ℓ₂ {A : ⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₂)}
                     ℓ₃ {B : ⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₃)}
              (f : ∀ {i} → A (p , i) → B (p , i))
              {V} (C : ConDesc P V I ℓ₁)
            → ∀ {v i} → ⟦ C ⟧Con ℓ₂ A (p , v , i) → ⟦ C ⟧Con ℓ₃ B (p , v , i)

  mapConᵇ : ∀ {V} {ℓ₁ ℓ₂ ℓ₃} ℓ₄ ℓ₅
               {A  : ⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₄)}
               {B  : ⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₅)}
               (f  : ∀ {i} → A (p , i) → B (p , i))
               (e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
               (ia : ArgInfo)
               (S  : ⟦ P , V ⟧xtel → Set ℓ₂)
               (C  : ConDesc P (V ⊢< ia > S) I ℓ₃)
             → ∀ {v i} → Conᵇ ℓ₄ e ia A S C (p , v , i) → Conᵇ ℓ₅ e ia B S C (p , v , i)

  mapCon ℓ₂ ℓ₃ f (var _) (lift p) = lift p
  mapCon ℓ₂ ℓ₃ f (A ⊗ B) (⟦A⟧ , EB) = mapIndArg ℓ₂ ℓ₃ f A ⟦A⟧ , mapCon ℓ₂ ℓ₃ f B EB
  mapCon ℓ₂ ℓ₃ f (π p i S C) x = mapConᵇ ℓ₂ ℓ₃ f p i S C x

  mapConᵇ ℓ₄ ℓ₅ f refl i S C (s , x) = s , mapCon ℓ₄ ℓ₅ f C x



  mapData : ∀ {ℓ₁} ℓ₂ {A : ⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₂)}
                   ℓ₃ {B : ⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₃)}
           (f : ∀ {i} → A (p , i) → B (p , i))
           {n} (D : DataDesc P I ℓ₁ n)
       → ∀ {i} → ⟦ D ⟧Data ℓ₂ A (p , i) → ⟦ D ⟧Data ℓ₃ B (p , i)
  mapData ℓ₂ ℓ₃ f D (k , x) = k , mapCon ℓ₂ ℓ₃ f (lookupCon D k) x


  module _ (funext : ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x}
                   → (∀ x → f x ≡ g x) → f ≡ g) where

    mutual
      mapIndArg-compose : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {X : ⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₂)}
                                      {Y : ⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₃)}
                                      {Z : ⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₄)}
                      {f : ∀ {i} → X (p , i) → Y (p , i)}
                      {g : ∀ {i} → Y (p , i) → Z (p , i)}
                      {V} {C : ConDesc P V I ℓ₁}
                    → ∀ {v} (x : ⟦ C ⟧IndArg ℓ₂ X (p , v))
                    → mapIndArg ℓ₂ {X} ℓ₄ {Z} (g ∘ f) C x ≡ mapIndArg ℓ₃ ℓ₄ g C (mapIndArg ℓ₂ {X} ℓ₃ {Y} f C x)
      mapIndArg-compose {C = var i} x = refl
      mapIndArg-compose {C = A ⊗ B} (⟦A⟧ , ⟦B⟧) =
        cong₂ _,_ (mapIndArg-compose {C = A} ⟦A⟧) (mapIndArg-compose {C = B} ⟦B⟧)
      mapIndArg-compose {X = X} {Y} {Z} {C = π p i S C} x
        = mapIndArgᵇ-compose {X = X} {Y} {Z} x

      mapIndArg-id : ∀ {V} {ℓ₁ ℓ₂} {X : ⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₂)}
                 {f : ∀ {i} → X (p , i) → X (p , i)}
                 (f≗id : ∀ {i} (x : X (p , i)) → f x ≡ x)
                 (C : ConDesc P V I ℓ₁)
               → ∀ {v} (x : ⟦ C ⟧IndArg ℓ₂ X (p , v)) → mapIndArg ℓ₂ ℓ₂ f C x ≡ x
      mapIndArg-id f≗id (var i) x = f≗id x
      mapIndArg-id f≗id (A ⊗ B) (a , b) = cong₂ _,_ (mapIndArg-id f≗id A a) (mapIndArg-id f≗id B b)
      mapIndArg-id f≗id (π p i S C) x = mapIndArgᵇ-id f≗id p i C x

      mapIndArgᵇ-compose : ∀ {V} {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆}
                       {X  : ⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₄)}
                       {Y  : ⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₅)}
                       {Z  : ⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₆)}
                       {f  : ∀ {i} → X (p , i) → Y (p , i)}
                       {g  : ∀ {i} → Y (p , i) → Z (p , i)}
                       {e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃}
                       {ia : ArgInfo}
                       {S  : ⟦ P , V ⟧xtel → Set ℓ₂}
                       {C  : ConDesc P (V ⊢< ia > S) I ℓ₃}
                     → ∀ {v} (x : IndArgᵇ ℓ₄ e ia X S C (p , v))
                     → mapIndArgᵇ ℓ₄ ℓ₆ (g ∘ f) e ia S C x
                       ≡ mapIndArgᵇ ℓ₅ ℓ₆ g e ia S C (mapIndArgᵇ ℓ₄ ℓ₅ f e ia S C x)
      mapIndArgᵇ-compose {e = refl} {C = C} x = funext (λ s → mapIndArg-compose {C = C} (x s))

      mapIndArgᵇ-id : ∀ {V} {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {X : ⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₄)}
                  {f : ∀ {i} → X (p , i) → X (p , i)}
                  (f≗id : ∀ {i} (x : X (p , i)) → f x ≡ x)
                  (e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
                  (ia : ArgInfo)
                  {S  : ⟦ P , V ⟧xtel → Set ℓ₂}
                  (C  : ConDesc P (V ⊢< ia > S) I ℓ₃)
                → ∀ {v} (x : IndArgᵇ ℓ₄ e ia X S C (p , v))
                → mapIndArgᵇ ℓ₄ ℓ₄ f e ia S C x ≡ x
      mapIndArgᵇ-id f≗id refl i C x = funext (λ s → mapIndArg-id f≗id C (x s))

    mutual
      mapCon-compose : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {X : ⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₂)}
                                          {Y : ⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₃)}
                                          {Z : ⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₄)}
                          {f : ∀ {i} → X (p , i) → Y (p , i)}
                          {g : ∀ {i} → Y (p , i) → Z (p , i)}
                          {V} {C : ConDesc P V I ℓ₁}
                        → ∀ {v i} (x : ⟦ C ⟧Con ℓ₂ X (p , v , i))
                        → mapCon ℓ₂ {X} ℓ₄ {Z} (g ∘ f) C x
                        ≡ mapCon ℓ₃ ℓ₄ g C (mapCon ℓ₂ {X} ℓ₃ {Y} f C x)
      mapCon-compose {C = var i} x = refl
      mapCon-compose {C = A ⊗ B} (⟦A⟧ , EB) =
        cong₂ _,_ (mapIndArg-compose {C = A} ⟦A⟧) (mapCon-compose {C = B} EB)
      mapCon-compose {X = X} {Y} {Z} {C = π p i S C} x
        = mapConᵇ-compose {X = X} {Y} {Z} x

      mapCon-id : ∀ {ℓ₁ ℓ₂} {X : ⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₂)}
                     {f    : ∀ {i} → X (p , i) → X (p , i)}
                     (f≗id : ∀ {i} (x : X (p , i)) → f x ≡ x)
                     {V} (C : ConDesc P V I ℓ₁)
                   → ∀ {v i} (x : ⟦ C ⟧Con ℓ₂ X (p , v , i))
                   → mapCon ℓ₂ ℓ₂ f C x ≡ x
      mapCon-id f≗id (var i) x = refl
      mapCon-id f≗id (A ⊗ B) (a , b) = cong₂ _,_ (mapIndArg-id f≗id A a) (mapCon-id f≗id B b)
      mapCon-id f≗id (π p i S C) x = mapConᵇ-id f≗id p i C x

      mapConᵇ-compose : ∀ {V} {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆}
                           {X  : ⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₄)}
                           {Y  : ⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₅)}
                           {Z  : ⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₆)}
                           {f  : ∀ {i} → X (p , i) → Y (p , i)}
                           {g  : ∀ {i} → Y (p , i) → Z (p , i)}
                           {e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃}
                           {ia : ArgInfo}
                           {S  : ⟦ P , V ⟧xtel → Set ℓ₂}
                           {C  : ConDesc P (V ⊢< ia > S) I ℓ₃}
                        → ∀ {v i} (x : Conᵇ ℓ₄ e ia X S C (p , v , i))
                        → mapConᵇ ℓ₄ ℓ₆ (g ∘ f) e ia S C x
                          ≡ mapConᵇ ℓ₅ ℓ₆ g e ia S C (mapConᵇ ℓ₄ ℓ₅ f e ia S C x)
      mapConᵇ-compose {f = f} {g} {e = refl} {C = C} (s , x) =
        cong (s ,_) (mapCon-compose {f = f} {g} {C = C} x)


      mapConᵇ-id : ∀ {V} {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {X : ⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₄)}
                     {f    : ∀ {i} → X (p , i) → X (p , i)}
                     (f≗id : ∀ {i} (x : X (p , i)) → f x ≡ x)
                     (e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
                     (ia : ArgInfo)
                     {S  : ⟦ P , V ⟧xtel → Set ℓ₂}
                     (C  : ConDesc P (V ⊢< ia > S) I ℓ₃)
                   → ∀ {v i} (x : Conᵇ ℓ₄ e ia X S C (p , v , i))
                   → mapConᵇ ℓ₄ ℓ₄ f e ia S C x ≡ x
      mapConᵇ-id f≗id refl i C (s , x) = cong (s ,_) (mapCon-id f≗id C x)

    mapData-compose : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
                     {A : ⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₂)}
                     {B : ⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₃)}
                     {C : ⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₄)}
                     {f : ∀ {i} → A (p , i) → B (p , i)}
                     {g : ∀ {i} → B (p , i) → C (p , i)}
                     {n} {D : DataDesc P I ℓ₁ n}
                 → ∀ {i} (x : ⟦ D ⟧Data ℓ₂ A (p , i))
                 → mapData ℓ₂ {A} ℓ₄ {C} (g ∘ f) D x
                 ≡ mapData ℓ₃ ℓ₄ g D (mapData ℓ₂ {A} ℓ₃ {B} f D x)
    mapData-compose {f = f} {g} {D = D} (k , x) =
      cong (k ,_) (mapCon-compose {f = f} {g} {C = lookupCon D k} x)


    mapData-id : ∀ {ℓ₁ ℓ₂} {X : ⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₂)}
                {f    : ∀ {i} → X (p , i) → X (p , i)}
                (f≗id : ∀ {i} (x : X (p , i)) → f x ≡ x)
                {n} {D : DataDesc P I ℓ₁ n}
            → ∀ {i} (x : ⟦ D ⟧Data ℓ₂ X (p , i)) → mapData ℓ₂ ℓ₂ f D x ≡ x
    mapData-id f≗id {D = D} (k , x) = cong (k ,_) (mapCon-id f≗id (lookupCon D k) x)

  mutual
    mapAllIndArg : ∀ {V} {ℓ₁ ℓ₂ ℓ₃} (C : ConDesc P V I ℓ₁)
               {X : ⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₂)}
               {Y : ⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₃)}
               (f : ∀ {i} → X (p , i) → Y (p , i))
               {c} (Pr : ∀ {i} → Y (p , i) → Set c)
               {v} {x : ⟦ C ⟧IndArg ℓ₂ X (p , v)}
             → AllIndArg C X (Pr ∘ f) x
             → AllIndArg C Y Pr (mapIndArg ℓ₂ ℓ₃ f C x)
    mapAllIndArg (var i) f Pr H = H
    mapAllIndArg (A ⊗ B) f Pr (HA , HB) = mapAllIndArg A f Pr HA , mapAllIndArg B f Pr HB
    mapAllIndArg (π p i S C) f Pr H = mapAllIndArgᵇ f Pr p i C H
  
    mapAllIndArgᵇ : ∀ {V} {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅}
                {X  : ⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₄)}
                {Y  : ⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₅)}
                (f  : ∀ {i} → X (p , i) → Y (p , i))
                {c} (Pr : ∀ {i} → Y (p , i) → Set c)
                (e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
                (ia : ArgInfo)
                {S  : ⟦ P , V ⟧xtel → Set ℓ₂}
                (C  : ConDesc P (V ⊢< ia > S) I ℓ₃)
              → ∀ {v} {x : IndArgᵇ ℓ₄ e ia X S C (p , v)}
              → AllIndArgᵇ e ia X S C (Pr ∘ f) x
              → AllIndArgᵇ e ia Y S C Pr (mapIndArgᵇ ℓ₄ ℓ₅ f e ia S C x)
    mapAllIndArgᵇ f Pr refl i C H s = mapAllIndArg C f Pr (H s)

  mutual
    mapAllCon : ∀ {V} {ℓ₁ ℓ₂ ℓ₃} (C : ConDesc P V I ℓ₁)
                   {X : ⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₂)}
                   {Y : ⟦ P , I ⟧xtel → Set (ℓ₁ ⊔ ℓ₃)}
                   (f : ∀ {i} → X (p , i) → Y (p , i))
                   {c} (Pr : ∀ {i} → Y (p , i) → Set c)
                   {v i} {x : ⟦ C ⟧Con ℓ₂ X (p , v , i)}
                 → AllCon C X (Pr ∘ f) x
                 → AllCon C Y Pr (mapCon ℓ₂ ℓ₃ f C x)
    mapAllCon (var i) f Pr H = H
    mapAllCon (A ⊗ B) f Pr (HA , HB) = mapAllIndArg A f Pr HA , mapAllCon B f Pr HB
    mapAllCon (π p i S C) f Pr H = mapAllConᵇ f Pr p i C H
  
    mapAllConᵇ : ∀ {V} {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅}
                    {X  : ⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₄)}
                    {Y  : ⟦ P , I ⟧xtel → Set (ℓ₃ ⊔ ℓ₅)}
                    (f  : ∀ {i} → X (p , i) → Y (p , i))
                    {c} (Pr : ∀ {i} → Y (p , i) → Set c)
                    (e  : ℓ₁ ≡ ℓ₂ ⊔ ℓ₃)
                    (ia : ArgInfo)
                    {S  : ⟦ P , V ⟧xtel → Set ℓ₂}
                    (C  : ConDesc P (V ⊢< ia > S) I ℓ₃)
                  → ∀ {v i} {x : Conᵇ ℓ₄ e ia X S C (p , v , i)}
                  → AllConᵇ e ia X S C (Pr ∘ f) x
                  → AllConᵇ e ia Y S C Pr (mapConᵇ ℓ₄ ℓ₅ f e ia S C x)
    mapAllConᵇ f Pr refl _ C H = mapAllCon C f Pr H
