{-# OPTIONS --safe #-}

module Generics.Parametrized.HasDesc where

open import Data.String.Base
open import Generics.Prelude
open import Generics.Parametrized.Telescope
open import Generics.Parametrized.Desc3


record HasDesc {P} {I : ExTele P} {ℓ} (A : [ P ⇒ I ] ℓ) : Setω where
  field
    {n} : ℕ
    D   : Desc P I ℓ n

    names : Vec String n

    to   : ∀ (pi : Σ[ P ⇒ I ]) → unroll {P} I {ℓ} A pi → μ D pi
    from : ∀ (pi : Σ[ P ⇒ I ]) → μ D pi → unroll {P} I {ℓ} A pi

private

  module DNat where

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

    natHasDesc : HasDesc ℕ
    natHasDesc = record
      { D     = natD
      ; names = "zero" ∷ "suc" ∷ []
      ; to    = const to
      ; from  = const from
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

    to : (pi : Σ[ P ⇒ I ]) → unroll I List pi → μ listD pi
    to (A , tt) []       = ⟨ zero , lift refl ⟩
    to (A , tt) (x ∷ xs) = ⟨ suc zero , x , to _ xs , lift refl ⟩

    from : (pi : Σ[ P ⇒ I ]) → μ listD pi → unroll I List pi
    from (A , tt) ⟨ zero , lift refl ⟩ = []
    from (A , tt) ⟨ suc zero , x , xs , lift refl ⟩ = x ∷ from (A , tt) xs


    listHasDesc : HasDesc List
    listHasDesc = record
      { D     = listD
      ; names = "[]" ∷ "_∷_" ∷ []
      ; to    = to
      ; from  = from
      }


  module W {a b : Level} where

    WP : Telescope ⊤
    WP = ε ⊢ const (Set a) ⊢ λ (_ , A) → A → Set b

    data W (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
      sup : (x : A) (f : B x → W A B) → W A B

    wD : Desc WP ε (a ⊔ b) 1
    wD = π refl (proj₁ ∘ proj₁) (π refl (λ p → proj₂ (proj₁ p) (proj₂ p)) (var (const tt)) ⊗ (var (const tt)))
       ∷ []

    to : ∀ pi → unroll {WP} ε W pi → μ wD pi
    to pi (sup x f) = ⟨ zero , x , (to pi ∘ f) , lift refl ⟩

    from : ∀ pi → μ wD pi → unroll {WP} ε W pi
    from pi ⟨ zero , x , f , lift refl ⟩ = sup x (from pi ∘ f)

    WHasDesc : HasDesc W
    WHasDesc = record
      { D     = wD
      ; names = "sup" ∷ []
      ; to    = to
      ; from  = from
      }
