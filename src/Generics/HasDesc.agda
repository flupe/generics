{- {-# OPTIONS --safe --without-K #-} -}

module Generics.HasDesc where

open import Data.String.Base
open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc


record HasDesc {P} {I : ExTele P} {ℓ} (A : Indexed P I ℓ) : Setω where
  A′ : ⟦ P , I ⟧xtel → Set ℓ
  A′ = uncurry P I A

  field
    {n} : ℕ
    D   : DataDesc P I ℓ n

    names : Vec String n

    to   : ∀ {pi : ⟦ P , I ⟧xtel} → A′ pi → μ D pi
    from : ∀ {pi : ⟦ P , I ⟧xtel} → μ D pi → A′ pi

    from∘to : ∀ {pi} (x : A′ pi ) → from (to x) ≡ x
    to∘from : ∀ {pi} (x : μ D pi) → to (from x) ≡ x

    constr  : ∀ {pi} → ⟦ D ⟧Data ℓ A′ pi → A′ pi
    split   : ∀ {pi} → A′ pi → ⟦ D ⟧Data ℓ A′ pi

    -- | constr and split are coherent with from
    constr-coh  : ∀ {pi} (x : ⟦ D ⟧Data _ (μ D) pi)
                → constr (mapData _ _ from D x) ≡ from ⟨ x ⟩

    split-coh   : ∀ {pi} (x : ⟦ D ⟧Data _ (μ D) pi)
                → split (from ⟨ x ⟩) ≡ mapData _ _ from D x


  -- because they are coherent, we can show that they are in fact inverse of one another
  constr∘split : ∀ {pi} (x : A′ pi) → constr (split x) ≡ x
  constr∘split x rewrite sym (from∘to x) with to x
  ... | ⟨ x′ ⟩ rewrite split-coh x′ = constr-coh x′

  split∘constr : ∀ (funext : ∀ {a b} {A : Set a} {B : A → Set b} {f g : ∀ x → B x}
                           → (∀ x → f x ≡ g x) → f ≡ g)
                 {pi} (x : ⟦ D ⟧Data ℓ A′ pi) → split (constr x) ≡ x
  split∘constr funext x = begin
    split (constr x)
      ≡˘⟨ cong (split ∘ constr) (mapData-id funext from∘to {D = D} x) ⟩
    split (constr (mapData ℓ ℓ (from ∘ to) D x))
      ≡⟨ cong (split ∘ constr) (mapData-compose funext {f = to} {g = from} {D = D} x) ⟩
    split (constr (mapData _ ℓ from D (mapData ℓ _ to D x)))
      ≡⟨ cong split (constr-coh _) ⟩
    split (from ⟨ mapData ℓ _ to D x ⟩)
      ≡⟨ split-coh _ ⟩
    mapData _ _ from D (mapData _ _ to D x)
      ≡˘⟨ mapData-compose funext {f = to} {g = from} {D = D} x ⟩
    mapData _ _ (from ∘ to) D x
      ≡⟨ mapData-id funext from∘to {D = D} x ⟩
    x ∎
    where open ≡-Reasoning

  split-injective : ∀ {pi} {x y : A′ pi} → split x ≡ split y → x ≡ y
  split-injective {x = x} {y} sx≡sy = begin
    x                ≡˘⟨ constr∘split x ⟩
    constr (split x) ≡⟨ cong constr sx≡sy ⟩
    constr (split y) ≡⟨ constr∘split y ⟩
    y                ∎
    where open ≡-Reasoning


module _ {P} {I : ExTele P} {ℓ} (A : Indexed P I ℓ) {n} (D : DataDesc P I ℓ n)
         (let A′ = uncurry P I A)
         (split   : ∀ {pi} → A′ pi → ⟦ D ⟧Data ℓ A′ pi)
         {p}
         where

  All′ : ∀ {c} (Pr : ∀ {i} → A′ (p , i) → Set c)
      → ∀ {i} → ⟦ D ⟧Data ℓ A′ (p , i) → Set (c ⊔ ℓ)
  All′ Pr (k , x′) = AllCon (lookupCon D k) A′ Pr x′

  data Acc {i} (x : A′ (p , i)) : Set ℓ where
    acc : All′ Acc (split x) → Acc x

  postulate
    wf : ∀ {i} (x : A′ (p , i)) → Acc x

  mutual
    to-IndArg : ∀ {V} {C : ConDesc P V I ℓ} {v}
             (x : ⟦ C ⟧IndArg ℓ A′ (p , v))
             (a : AllIndArg C A′ Acc x)
           → ⟦ C ⟧IndArg (levelOfTel I) (μ D) (p , v)
    to-IndArg {C = var f} x (lift a) = to-wf x a
    to-IndArg {C = π p ia S C} x a = to-IndArgᵇ p ia S C x a
    to-IndArg {C = A ⊗ B} (xa , xb) (aa , ab) = to-IndArg {C = A} xa aa , to-IndArg {C = B} xb ab

    to-IndArgᵇ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ai {v}
            → (S : ⟦ P , V ⟧xtel → Set ℓ₂)
            → (C : ConDesc P (V ⊢< ai > S) I ℓ)
            → (x : IndArgᵇ ℓ e ai A′ S C (p , v))
            → AllIndArgᵇ e ai A′ S C Acc x
            → IndArgᵇ (levelOfTel I) e ai (μ D) S C (p , v)
    to-IndArgᵇ refl _ S C X a s = to-IndArg {C = C} (X s) (a s)

    to-Con : ∀ {i} {V} {C : ConDesc P V I ℓ} {v}
             (x : ⟦ C ⟧Con ℓ A′ (p , v , i))
             (a : AllCon C A′ Acc x)
           → ⟦ C ⟧Con (levelOfTel I) (μ D) (p , v , i)
    to-Conᵇ : ∀ {V} {ℓ₁ ℓ₂} (e : ℓ₁ ≡ ℓ₂ ⊔ ℓ) ai {v}
            → (S : ⟦ P , V ⟧xtel → Set ℓ₂)
            → (C : ConDesc P (V ⊢< ai > S) I ℓ)
            → (x : Conᵇ ℓ e ai A′ S C (p , v))
            → AllConᵇ e ai A′ S C Acc x
            → Conᵇ (levelOfTel I) e ai (μ D) S C (p , v)
    to-Conᵇ refl _ S C (s , x) a = s , to-Con {C = C} x a

    to-Con {C = var f} (lift refl) a = lift refl
    to-Con {C = π e ia S C} x a = to-Conᵇ e ia S C x a
    to-Con {C = A ⊗ B} (xa , xb) (aa , ab) = to-IndArg {C = A} xa aa , (to-Con {C = B} xb ab)
    
    to-wf : ∀ {i} (x : A′ (p , i)) → Acc x → μ D (p , i)
    to-wf x (acc a) with split x
    ... | (k , x′) = ⟨ k , to-Con {C = lookupCon D k} x′ a ⟩

  to : ∀ {i} → A′ (p , i) → μ D (p , i)
  to x = to-wf x (wf x)

module example where

  natD : DataDesc ε ε lzero 2
  natD = (var _) ∷ (var _ ⊗ var _) ∷ []

  split : ℕ → ⟦ natD ⟧Data lzero (λ _ → ℕ) _
  split zero    = zero           , (lift refl)
  split (suc n) = (suc zero) , n , (lift refl)

  wf-nat : ∀ n → Acc ℕ natD split n
  wf-nat zero    = acc (lift tt)
  wf-nat (suc n) = acc (lift (wf-nat n) , (lift tt))

  toμ : ℕ → μ natD (tt , tt)
  toμ n = to-wf ℕ natD split n (wf-nat n)

module example2 (A : Set) (B : A → Set) where
  
  data W : Set where
    node : ∀ x → (B x → W) → W

  wD : DataDesc ε ε lzero 1
  wD = π refl (ai visible relevant quantity-ω)
         (const A) (π refl (ai visible relevant quantity-ω) (λ (_ , (_ , x)) → B x) (var (const tt))
       ⊗ var (const tt))
     ∷ []

  split : (w : W) → ⟦ wD ⟧Data lzero (const W) (tt , tt)
  split (node x f) = zero , (x , f , lift refl)

  wf-W : ∀ n → Acc W wD split n
  wf-W (node x f) = acc ((λ s → lift (wf-W (f s))) , (lift tt))

  toμ : W → μ wD (tt , tt)
  toμ n = to-wf W wD split n (wf-W n)
