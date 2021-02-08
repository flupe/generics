{-# OPTIONS --safe --without-K #-}

module Generics.Parametrized.HasDesc where

open import Data.String.Base
open import Generics.Prelude hiding (lookup)
open import Generics.Parametrized.Telescope
open import Generics.Parametrized.Desc3


record HasDesc {P} {I : ExTele P} {ℓ} (A : Curried′ P I ℓ) : Setω where
  A′ : Σ[ P ⇒ I ] → Set ℓ
  A′ = uncurry′ P I A
  
  field
    {n} : ℕ
    D   : Desc P I ℓ n

    names : Vec String n

    to   : ∀ {pi : Σ[ P ⇒ I ]} → A′ pi → μ D pi
    from : ∀ {pi : Σ[ P ⇒ I ]} → μ D pi → A′ pi

    from∘to : ∀ {pi} (x : A′ pi ) → from (to x) ≡ x
    to∘from : ∀ {pi} (x : μ D pi) → to (from x) ≡ x

    constr  : ∀ {pi} → ⟦ D ⟧ ℓ A′ pi → A′ pi
    split   : ∀ {pi} → A′ pi → ⟦ D ⟧ ℓ A′ pi

    -- | constr and split are coherent with from
    constr-coh  : ∀ {pi} (x : ⟦ D ⟧ _ (μ D) pi) → constr (mapD _ _ from D x) ≡ from ⟨ x ⟩
    split-coh   : ∀ {pi} (x : ⟦ D ⟧ _ (μ D) pi) → split (from ⟨ x ⟩) ≡ mapD _ _ from D x


  -- because they are coherent, we can show that they are in fact inverse of one another
  constr∘split : ∀ {pi} (x : A′ pi) → constr (split x) ≡ x
  constr∘split x rewrite sym (from∘to x) with to x
  ... | ⟨ x′ ⟩ rewrite split-coh x′ = constr-coh x′

  split∘constr : ∀ (funext : ∀ {a b} {A : Set a} {B : A → Set b} {f g : ∀ x → B x}
                           → (∀ x → f x ≡ g x) → f ≡ g)
                 {pi} (x : ⟦ D ⟧ ℓ A′ pi) → split (constr x) ≡ x
  split∘constr funext x = begin
    split (constr x)
      ≡˘⟨ cong (split ∘ constr) (mapD-id funext from∘to {D = D} x) ⟩
    split (constr (mapD ℓ ℓ (from ∘ to) D x))
      ≡⟨ cong (split ∘ constr) (mapD-compose funext {f = to} {g = from} {D = D} x) ⟩
    split (constr (mapD _ ℓ from D (mapD ℓ _ to D x)))
      ≡⟨ cong split (constr-coh _) ⟩
    split (from ⟨ mapD ℓ _ to D x ⟩)
      ≡⟨ split-coh _ ⟩
    mapD _ _ from D (mapD _ _ to D x)
      ≡˘⟨ mapD-compose funext {f = to} {g = from} {D = D} x ⟩
    mapD _ _ (from ∘ to) D x
      ≡⟨ mapD-id funext from∘to {D = D} x ⟩
    x ∎
    where open ≡-Reasoning

  split-injective : ∀ {pi} {x y : A′ pi} → split x ≡ split y → x ≡ y
  split-injective {x = x} {y} sx≡sy = begin
    x                ≡˘⟨ constr∘split x ⟩
    constr (split x) ≡⟨ cong constr sx≡sy ⟩
    constr (split y) ≡⟨ constr∘split y ⟩
    y                ∎
    where open ≡-Reasoning

{-

private

  module DNat wherecong

    natD : Desc ε ε lzero 2
    natD = var (const tt)
         ∷ var (const tt) ⊗ var (const tt)
         ∷ []

    to : ℕ → μ natD (tt , tt)
    to zero    = ⟨ zero , lift refl ⟩
    to (suc x) = ⟨ suc zero , to x , lift refl ⟩

    from : μ natD (tt , tt) → ℕ
    from ⟨ zero , lift refl ⟩ = 0
    from ⟨ suc zero , x , lift refl ⟩ = suc (from x)

    constr : ∀ k
           → Extend {ε} {ε} {ℓ₂ = lzero} (lookup natD k) (unroll {ε} ε ℕ) (tt , tt , tt)
           → unroll {ε} ε ℕ (tt , tt)
    constr zero (lift refl) = 0
    constr (suc zero) (n , lift refl) = suc n

    natHasDesc : HasDesc ℕ
    natHasDesc = record
      { D      = natD
      ; names  = "zero" ∷ "suc" ∷ []
      ; to     = to
      ; from   = from
      ; constr = constr
      }


  module DList {a : Level} where

    P : Telescope ⊤
    P = ε ⊢ const (Set a)

    I : ExTele P
    I = ε

    listD : Desc P I a 2
    listD = var (const tt)
          ∷ π refl proj₁ ((var (const tt)) ⊗ var (const tt))
          ∷ []

    to : {pi : Σ[ P ⇒ I ]} → unroll I List pi → μ listD pi
    to []       = ⟨ zero , lift refl ⟩
    to (x ∷ xs) = ⟨ suc zero , x , to xs , lift refl ⟩

    from : {pi : Σ[ P ⇒ I ]} → μ listD pi → unroll I List pi
    from ⟨ zero , lift refl ⟩ = []
    from ⟨ suc zero , x , xs , lift refl ⟩ = x ∷ from xs

    constr : ∀ {A} k
           → Extend {P} {I} {ℓ₂ = a} (lookup listD k) (unroll {P} I List) (A , tt , tt)
           → unroll {P} I List (A , tt)
    constr zero (lift refl) = []
    constr (suc zero) (x , xs , lift refl) = x ∷ xs

    listHasDesc : HasDesc List
    listHasDesc = record
      { D      = listD
      ; names  = "[]" ∷ "_∷_" ∷ []
      ; to     = to
      ; from   = from
      ; constr = constr
      }


  module W {a b : Level} where

    WP : Telescope ⊤
    WP = ε ⊢ const (Set a) ⊢ λ (_ , A) → A → Set b

    data W (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
      sup : (x : A) (f : B x → W A B) → W A B

    wD : Desc WP ε (a ⊔ b) 1
    wD = π refl (proj₁ ∘ proj₁) (π refl (λ p → proj₂ (proj₁ p) (proj₂ p)) (var (const tt)) ⊗ (var (const tt)))
       ∷ []

    to : ∀ {pi} → unroll {WP} ε W pi → μ wD pi
    to (sup x f) = ⟨ zero , x , (to ∘ f) , lift refl ⟩

    from : ∀ {pi} → μ wD pi → unroll {WP} ε W pi
    from ⟨ zero , x , f , lift refl ⟩ = sup x (from ∘ f)

    constr : ∀ {A} {B} k
           → Extend {WP} {I = ε} {ℓ₂ = a ⊔ b} (lookup wD k) (unroll {WP} ε W) ((A , B) , tt , tt)
           → unroll {WP} ε W ((A , B) , tt)
    constr zero (x , f , lift refl) = sup x f

    WHasDesc : HasDesc W
    WHasDesc = record
      { D      = wD
      ; names  = "sup" ∷ []
      ; to     = to
      ; from   = from
      ; constr = constr
      }

  module Eq {a : Level} where
    data Id (A : Set a) (x : A) : A → Set a where
      refl : Id A x x

    P : Telescope ⊤
    P = ε ⊢ const (Set a) ⊢ proj₂

    I : ExTele P
    I = ε ⊢ proj₁ ∘ proj₁

    eqD : Desc P I a 1
    eqD = var (proj₂ ∘ proj₁) ∷ []

    to : ∀ {pi} → unroll {P} I Id pi → μ eqD pi
    to refl = ⟨ zero , lift refl ⟩

    from : ∀ {pi} → μ eqD pi → unroll {P} I Id pi
    from ⟨ zero , lift refl ⟩ = refl

    constr : ∀ {A} {x} {y} k
           → Extend {P} {I = I} {ℓ₂ = a} (lookup eqD k) (unroll {P} I Id) ((A , x) , tt , y)
           → unroll {P} I Id ((A , x) , y)
    constr zero (lift refl) = refl

    IdHasDesc : HasDesc Id
    IdHasDesc = record
      { D      = eqD
      ; names  = "refl" ∷ []
      ; to     = to
      ; from   = from
      ; constr = constr
      }

-}
