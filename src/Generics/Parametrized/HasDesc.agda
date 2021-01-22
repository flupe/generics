{-# OPTIONS --safe --without-K #-}

module Generics.Parametrized.HasDesc where

open import Data.String.Base
open import Generics.Prelude
open import Generics.Parametrized.Telescope
open import Generics.Parametrized.Desc


record HasDesc {P} {I : ExTele P} {ℓ} (A : [ P ⇒ I ] ℓ) : Setω where
  field
    {n} : ℕ
    D   : DDesc P I n

    names : Vec String n

    to   : ∀ (pi : [ P · I ]) → uncurry P I ℓ A pi → μ D pi
    from : ∀ (pi : [ P · I ]) → μ D pi → uncurry P I ℓ A pi

private

  module DNat where

    natD : DDesc ε ε 2
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
    P = ε ▷ const (Set a)

    I : ExTele P
    I = ε

    listD : DDesc P I 2
    listD = var (const tt)
          ∷ π proj₁ ((var (const tt)) ⊗ var (const tt))
          ∷ []

    data list (A : Set a) : Set (lsuc a) where
        []  : list A
        _∷_ : A → list A → list A

    to : (pi : [ P · I ]) → uncurry P I lzero list pi → μ listD pi
    to (A , tt) []       = ⟨ zero , lift refl ⟩
    to (A , tt) (x ∷ xs) = ⟨ suc zero , x , to _ xs , lift refl ⟩

    from : (pi : [ P · I ]) → μ listD pi → uncurry P I lzero list pi
    from (A , tt) ⟨ zero , lift refl ⟩ = []
    from (A , tt) ⟨ suc zero , x , xs , lift refl ⟩ = x ∷ from (A , tt) xs

    instance
      listHasDesc : HasDesc {ℓ = lzero} list
      listHasDesc = record
        { D     = listD
        ; names = "[]" ∷ "_∷_" ∷ []
        ; to    = to
        ; from  = from
        }


  module DW {a b : Level} where

    wD : DDesc (ε ▷ const (Set a) ▷ λ (_ , A) → A → Set b) ε 1
    wD = π (proj₁ ∘ proj₁) (π (λ p → proj₂ (proj₁ p) (proj₂ p)) (var (const tt)) ⊗ (var (const tt)))
       ∷ []


    WHasDesc : HasDesc {ℓ = lzero} {!!}
    WHasDesc = record
      { D     = wD
      ; names = {!!}
      ; to    = {!!}
      ; from  = {!!}
      }
