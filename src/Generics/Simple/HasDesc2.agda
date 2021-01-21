{-# OPTIONS --without-K #-}

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
open import Data.Product

open import Generics.Simple.Desc

private
  variable
    a b : Level


record HasDesc {a b} {I : Set a} (A : I → Set (a ⊔ b)) : Set (a ⊔ lsuc b) where
  field
    {n} : ℕ
    D   : Desc I b n

    names : Vec String n

    to   : ∀ {i} → A i → μ D i
    from : ∀ {i} → μ D i → A i

    to∘from : ∀ {i} (x : μ D i) → to (from x) ≡ x
    from∘to : ∀ {i} (x : A i  ) → from (to x) ≡ x

    -- | "primitive" constructors & destructors of A γ
    constr  : ∀ {i} → ⟦ D ⟧D A i → A i
    dissect : ∀ {i} → A i → ⟦ D ⟧D A i

    -- | proof that constr indeed holds the constructors of A
    constr-coh  : ∀ {i} (x : μ D i) → constr (mapD from {D} (unwrap x)) ≡ from x
    dissect-coh : ∀ {i} (x : μ D i) → dissect (from x) ≡ mapD from {D} (unwrap x)
  

  constr∘dissect : ∀ {i} (x : A i) → constr (dissect x) ≡ x
  constr∘dissect x rewrite sym (from∘to x) | dissect-coh (to x) | constr-coh (to x) = refl

  -- dissect∘constr : ∀ {i} (x : ⟦ D ⟧D A i) → dissect (constr x) ≡ x


private
  module ConstrFromFrom {a b} {I : Set a} (A : I → Set (a ⊔ b)) ⦃ H : HasDesc {b = b} A ⦄ where
  
    open HasDesc H using (n; D; to; from; to∘from)
    open Generics.Simple.Desc.Properties

    -- Can we retrieve constr & constr-proof from to/from?
    -- Yes we can:
  
    constr : ∀ {i} → ⟦ D ⟧D A i → A i
    constr (k , x) = from ⟨ k , mapC to x ⟩

    constr-coh : ∀ {i} (x : ⟦ D ⟧D (μ D) i) → constr (mapD from {D} x) ≡ from ⟨ x ⟩
    constr-coh (k , x) = cong (from ∘ ⟨_⟩ ∘ (k ,_)) $ begin
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
  module FromFromConstr {a b} {I : Set a} (A : I → Set (a ⊔ b)) ⦃ H : HasDesc {b = b} A ⦄ where

    open HasDesc H using (n; D; to; constr)

    -- Likewise, we can define `from` using only primitive constructors,
    -- However it does not pass the termination check (unless we define μ with Size).
    -- Hence why we also require `from` in the definition of HasDesc

    -- {-# TERMINATING #-}
    -- from : ∀ {γ} → μ D γ → A γ
    -- from ⟨ k , x ⟩ = constr (k , mapC from x)
