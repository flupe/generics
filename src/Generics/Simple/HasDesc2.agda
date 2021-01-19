{-# OPTIONS --safe --without-K #-}

module Generics.Simple.HasDesc2 where

open import Agda.Primitive
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Sigma
open import Agda.Builtin.String
open import Agda.Builtin.Equality
open import Data.Fin.Base
open import Data.Vec.Base
open import Function.Base
open import Relation.Binary.PropositionalEquality

open import Generics.Simple.Desc

private
  variable
    ℓ : Level


module _ {ℓ} {I : Set ℓ} (A : I → Set ℓ) where

  Constr : ConDesc I → Set ℓ
  Constr C = ∀ {γ} → ⟦ C ⟧C A γ → A γ

  Constr-proof : ∀ {n} {D : Desc I n}
                 (to   : ∀ {γ} → A γ   → μ D γ)
                 (from : ∀ {γ} → μ D γ → A γ  )
                 {k} → Constr (lookup D k) → Set ℓ
  Constr-proof {D = D} to from {k} con =
    ∀ {γ} (x : ⟦ _ ⟧C (μ D) γ) → con (mapC from x) ≡ from ⟨ k , x ⟩


record HasDesc {I : Set ℓ} (A : I → Set ℓ) : Set (lsuc ℓ) where
  field
    {n} : ℕ
    D   : Desc I n

    names : Vec String n

    to   : ∀ {i} → A i → μ D i
    from : ∀ {i} → μ D i → A i

    to∘from : ∀ {i} (x : μ D i) → to (from x) ≡ x
    from∘to : ∀ {i} (x : A i  ) → from (to x) ≡ x

  field
    -- | "primitive" constructors of A γ
    constr       : ∀ k → Constr A (lookup D k)
    -- | proof that constr indeed holds the constructors of A
    constr-proof : ∀ k → Constr-proof A to from (constr k)


private
  module ConstrFromFrom {I : Set ℓ} (A : I → Set ℓ) ⦃ H : HasDesc A ⦄ where
  
    open HasDesc H using (n; D; to; from; to∘from)

    -- Can we retrieve constr & constr-proof from to/from?
    -- Yes we can:
  
    constr : ∀ k → Constr A (lookup D k)
    constr k = from ∘ ⟨_⟩ ∘ (k ,_) ∘ mapC to

    constr-proof : ∀ k → Constr-proof A to from (constr k)
    constr-proof k x = cong (from ∘ ⟨_⟩ ∘ (k ,_)) $ begin
        mapC to (mapC from x)     ≡˘⟨ mapC-∘ ⟩
        mapC (to ∘ from) x        ≡⟨ mapC-id to∘from ⟩
        x                         ∎
      where open ≡-Reasoning

    -- This begs the question: why don't we define it as such, rather than require it from the user?
    -- Simply because this definition of constr requires to fully convert
    -- the recursive arguments to construct a value in μ D γ, then convert the result to A γ.
  
    -- Our goal is to avoid as much as possible working in μ D γ
    -- Therefore we need to be provided with primitives in A γ
    -- and make sure they are "coherent". Hence constr-proof.

private
  module FromFromConstr {I : Set ℓ} (A : I → Set ℓ) ⦃ H : HasDesc A ⦄ where

    open HasDesc H using (n; D; to; constr)

    -- Likewise, we can define `from` using only primitive constructors,
    -- However it does not pass the termination check.
    -- Hence why we also require `from` in the definition of HasDesc

    -- {-# TERMINATING #-}
    -- from : ∀ {γ} → μ D γ → A γ
    -- from ⟨ k , x ⟩ = constr k (mapC from x)
