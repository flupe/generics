open import Data.Fin.Base
open import Data.Vec.Base
open import Data.Unit.Polymorphic
open import Level
open import Function.Base

open import Data.Product
open import Generics.Prelude
open import Generics.Simple.Desc
open import Generics.Simple.HasDesc2
open import Generics.Simple.Constructions.Elim
open import Relation.Binary.PropositionalEquality


module Generics.Simple.Constructions.Case where

  module Case {a b} {I : Set a} (A : I → Set (a ⊔ b)) ⦃ H : HasDesc {b = b} A ⦄
              {c} (P : ∀ {i} → A i → Set c) where
  
    open HasDesc H
  
    -- | Returns the type of the case method for the kᵗʰ constructor
    con-method : Fin n → Set (a ⊔ b ⊔ c)
    con-method k = ∀ {i} → (x : ⟦ lookup D k ⟧C A i) → P (constr (k , x))
  
    -- | A vector containing the types of every constructor's case method
    case-methods : Vec (Set (a ⊔ b ⊔ c)) n
    case-methods = tabulate (con-method)
  
    -- | The generalized case analysis principle
    case : Members case-methods → ∀ {i} (x : A i) → P x
    case methods x with dissect x | sym (constr∘dissect x)
    ... | k , x′ | refl = subst id (lookupTabulate con-method k) (lookupMember methods k) x′

  -- | Returns the type of the case analysis principle for the given datatype
  Case : ∀ {a b} {I : Set a} (A : I → Set (a ⊔ b)) ⦃ H : HasDesc {b = b} A ⦄
           {c} (P : ∀ {i} → A i → Set c)
       → Set (a ⊔ b ⊔ c)
  Case A ⦃ H ⦄ {b} P = curryMembersType {b = b} (Case.case A P)

  -- | Returns the case analysis principle for the given datatype
  case : ∀ {a b} {I : Set a} (A : I → Set (a ⊔ b)) ⦃ H : HasDesc {b = b} A ⦄
           {c} (P : ∀ {i} → A i → Set c)
       → Case A P
  case A ⦃ H ⦄ P = curryMembers (Case.case A P)
