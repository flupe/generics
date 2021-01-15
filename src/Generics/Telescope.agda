module Generics.Telescope where

open import Agda.Primitive
open import Agda.Builtin.List
open import Data.Unit.Base
open import Data.Product
open import Function.Base


LevelTel : Set
LevelTel = List Level

telLevel : LevelTel → Level
telLevel []       = lzero
telLevel (a ∷ as) = telLevel as ⊔ a

-- Telescopes depend on some set A so
-- that we can make Telescope depend on the interpretation
-- of other telescopes
Tel : ∀ {ℓ} → Set ℓ → LevelTel → Setω
⟦_⟧ : ∀ {ℓ as} {A : Set ℓ} → Tel A as → A → Set (telLevel as)

record ⋆ : Setω where
  instance constructor *

record Σω {ℓ} (A : Set ℓ) a as : Setω where
  inductive
  constructor _▷_
  field
    T : Tel A as
    B : Σ A ⟦ T ⟧ → Set a
open Σω

infixl 7 _▷_


Tel A []       = ⋆
Tel A (a ∷ as) = Σω A a as

⟦_⟧ {as = []    } _ a = ⊤
⟦_⟧ {as = x ∷ as} {A} t a = Σ (⟦ T t ⟧ a) (B t ∘ (a ,_))

Tel′ : LevelTel → Setω
Tel′ = Tel ⊤

⟦_⟧′ : ∀ {as} → Tel′ as → Set (telLevel as)
⟦ T ⟧′ = ⟦ T ⟧ tt


private
  module Example where

    open import Data.Nat.Base using (ℕ)
    open import Data.Fin.Base

    t : Tel ⊤ _ 
    t = * ▷ const ℕ ▷ Fin ∘ proj₂ ∘ proj₂

    s : ⟦ t ⟧ tt
    s = (tt , 3) , suc zero
