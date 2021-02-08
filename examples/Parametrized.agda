{-# OPTIONS --safe #-}

open import Generics.Prelude hiding (lookup)
open import Generics.Parametrized.Telescope
open import Generics.Parametrized.Desc3
open import Generics.Parametrized.HasDesc

module Parametrized where


module DNat where

  natD : Desc ε ε lzero 2
  natD = var (const tt)
       ∷ var (const tt) ⊗ var (const tt)
       ∷ []

  ℕ′ : Σ[ ε ⇒ ε ] → Set
  ℕ′ = uncurry′ ε ε ℕ

  -- all of this should be derived very soon
  to : ℕ → μ natD (tt , tt)
  to zero    = ⟨ zero , lift refl ⟩
  to (suc x) = ⟨ suc zero , to x , lift refl ⟩

  from : μ natD (tt , tt) → ℕ
  from ⟨ zero , lift refl ⟩ = 0
  from ⟨ suc zero , x , lift refl ⟩ = suc (from x)

  constr : ⟦ natD ⟧ lzero ℕ′ (tt , tt) → ℕ
  constr (zero     , x) = 0
  constr (suc zero , n , lift refl) = suc n

  split : ℕ → ⟦ natD ⟧ lzero ℕ′ (tt , tt)
  split zero    = zero     , lift refl
  split (suc n) = suc zero , n , lift refl

  from∘to : ∀ x → from (to x) ≡ x
  from∘to zero    = refl
  from∘to (suc n) = cong suc (from∘to n)

  to∘from : ∀ x → to (from x) ≡ x
  to∘from ⟨ zero , lift refl ⟩ = refl
  to∘from ⟨ suc zero , n , lift refl ⟩ = cong (⟨_⟩ ∘ (suc zero ,_)) (cong₂ _,_ (to∘from n) refl)

  constr-coh : ∀ x → constr (mapD lzero lzero from natD x) ≡ from ⟨ x ⟩
  constr-coh (zero , lift refl) = refl
  constr-coh (suc zero , n , lift refl) = cong suc refl

  split-coh : ∀ x → split (from ⟨ x ⟩) ≡ mapD lzero lzero from natD x
  split-coh (zero , lift refl) = refl
  split-coh (suc zero , n , lift refl) = cong (suc zero ,_) refl

  natHasDesc : HasDesc ℕ
  natHasDesc = record
    { D          = natD
    ; names      = "zero" ∷ "suc" ∷ []
    ; to         = to
    ; from       = from
    ; constr     = constr
    ; split      = split
    ; from∘to    = from∘to
    ; to∘from    = to∘from
    ; constr-coh = constr-coh
    ; split-coh  = split-coh
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

  List′ : Σ[ P ⇒ I ] → Set a
  List′ = uncurry′ P I List

  to : {pi : Σ[ P ⇒ I ]} → List′ pi → μ listD pi
  to []       = ⟨ zero , lift refl ⟩
  to (x ∷ xs) = ⟨ suc zero , x , to xs , lift refl ⟩

  from : {pi : Σ[ P ⇒ I ]} → μ listD pi → List′ pi
  from ⟨ zero , lift refl ⟩ = []
  from ⟨ suc zero , x , xs , lift refl ⟩ = x ∷ from xs

  constr : ∀ {pi} → ⟦ listD ⟧ a List′ pi → List′ pi
  constr (zero , lift refl) = []
  constr (suc zero , x , xs , lift refl) = x ∷ xs

  split : ∀ {pi} → List′ pi → ⟦ listD ⟧ a List′ pi
  split [] = zero , lift refl
  split (x ∷ xs) = suc zero , x , xs , lift refl

  from∘to : ∀ {pi} (x : List′ pi) → from (to x) ≡ x
  from∘to [] = refl
  from∘to (x ∷ xs) = cong (x ∷_) (from∘to xs)

  to∘from : ∀ {pi} (x : μ listD pi) → to (from x) ≡ x
  to∘from ⟨ zero , lift refl ⟩ = refl
  to∘from ⟨ suc zero , x , xs , lift refl ⟩ =
    cong (⟨_⟩ ∘ (suc zero ,_)) (cong₂ _,_ refl (cong₂ _,_ (to∘from xs) refl))

  constr-coh : ∀ {pi} (x : ⟦ listD ⟧ lzero (μ listD) pi) → constr (mapD lzero a from listD x) ≡ from ⟨ x ⟩
  constr-coh (zero , lift refl) = refl
  constr-coh (suc zero , x , xs , lift refl) = cong₂ _∷_ refl refl

  split-coh : ∀ {pi} (x : ⟦ listD ⟧ lzero (μ listD) pi) → split (from ⟨ x ⟩) ≡ mapD lzero a from listD x
  split-coh (zero , lift refl) = refl
  split-coh (suc zero , x , xs , lift refl) = cong (suc zero ,_) (cong₂ _,_ refl (cong₂ _,_ refl refl))

  listHasDesc : HasDesc List
  listHasDesc = record
    { D      = listD
    ; names  = "[]" ∷ "_∷_" ∷ []
    ; to     = to
    ; from   = from
    ; constr = constr
    ; split  = split
    ; from∘to = from∘to
    ; to∘from = to∘from
    ; constr-coh = constr-coh
    ; split-coh  = split-coh
    }

{-

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
