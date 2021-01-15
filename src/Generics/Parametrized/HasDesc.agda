module Generics.Parametrized.HasDesc where

open import Generics.Telescope
open import Generics.Parametrized.Desc

open import Data.Product
open import Data.Nat.Base
open import Data.Vec.Base
open import Data.String.Base
open import Data.Unit.Base
open import Agda.Primitive
open import Level using (Lift; lift)
open import Data.Fin.Base using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality
open import Function.Base


module _ {ps is ℓ} {TP : Tel′ ps} {TI : Tel ⟦ TP ⟧′ is} (A : (p : ⟦ TP ⟧′) → ⟦ TI ⟧ p → Set ℓ)  where

  Constr : ∀ {vs} {TV : Tel ⟦ TP ⟧′ vs} → ConDesc ℓ TP TV TI → Σ ⟦ TP ⟧′ ⟦ TV ⟧ → Set ℓ
  Constr (κ γ  ) pv = A (proj₁ pv) (γ pv)
  Constr (ι γ C) pv = uncurry A (γ pv)     → Constr C pv
  Constr (σ S C) (p , v) = (s : S (p , v)) → Constr C (p , v , s)


record HasDesc {ps is k} {TP : Tel′ ps} {TI : Tel ⟦ TP ⟧′ is} (A : (p : ⟦ TP ⟧′) → ⟦ TI ⟧ p → Set k) : Setω where
  field
    {n    } : ℕ

    names : Vec String n

    D   : Desc k TP TI n

    to   : ∀ {p i} → A p i → μ D (p , i)
    from : ∀ {p i} → μ D (p , i) → A p i

    to∘from : ∀ {pi} (x : μ D pi) → to (from x) ≡ x
    from∘to : ∀ {p i} (x : A p i) → from (to x) ≡ x

    constr : (k : Fin n) → (p : ⟦ TP ⟧′) → Constr A (lookup D k) (p , tt)

open HasDesc


private
  module Example where

    -- adding dummy parameters and indices for simplicity
    data nat (t : ⊤) : ⊤ → Set where
      ze : nat tt tt
      su : nat tt tt → nat tt tt

    hasD : HasDesc nat
    hasD .n = 2
    hasD .names = "ze" ∷ "su" ∷ []
    hasD .D = κ (const tt)
            ∷ ι (const (tt , tt)) (κ (const tt))
            ∷ []
    hasD .to ze     = ⟨ zero , lift refl ⟩
    hasD .to (su n) = ⟨ suc zero , hasD .to n , lift refl ⟩

    hasD .from ⟨ zero     , lift refl     ⟩ = ze
    hasD .from ⟨ suc zero , n , lift refl ⟩ = su (hasD .from n)

    hasD .to∘from x = {!!}

    hasD .from∘to ze     = refl
    hasD .from∘to (su n) = ? -- cong su (hasD .from∘to n)

    hasD .constr zero       tt = ze
    hasD .constr (suc zero) tt = su
