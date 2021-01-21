open import Agda.Primitive
open import Data.Fin.Base
open import Data.Unit.Polymorphic
open import Data.Vec.Base
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Function.Base

open import Generics.Prelude
open import Generics.Simple.Desc
open import Generics.Simple.HasDesc2
open import Generics.Simple.Constructions.Induction as Induction


module Generics.Simple.Constructions.Elim where

  module Elim {a b} {I : Set a} (A : I → Set (a ⊔ b)) (H : HasDesc {b = b} A)
              {c} (P : ∀ {i} → A i → Set c) where
                
    open HasDesc H

    PC : {C : ConDesc I b} → ∀ {i} → ⟦ C ⟧C A i → Set (a ⊔ c)
    PC {κ γ  } x       = ⊤
    PC {ι γ C} (x , d) = P x × PC d
    PC {σ S C} (s , d) = PC d

    -- | Returns the type of the induction method for the kth constructor
    con-method : Fin n → Set (a ⊔ b ⊔ c)
    con-method k = ∀ {i} {x : ⟦ lookup D k ⟧C A i} → PC x → P (constr (k , x)) 

    -- | A vector containing the types for every induction method
    elim-methods : Vec (Set (a ⊔ b ⊔ c)) n
    elim-methods = tabulate con-method

    P′ : ∀ {γ} → μ D γ → Set c
    P′ x′ = P (from x′)

    module Ind = Induction D P′

    module _ (methods : Members elim-methods) where
      
      to-hypothesis : ∀ {γ} (X : μ D γ) → All D P′ X → P′ X
      to-hypothesis {γ} X@(⟨ k , x ⟩) IH
        rewrite sym (constr-coh X) = method (PC′ C x IH)
        where
          C = lookup D k

          method : ∀ {γ} {x : ⟦ C ⟧C A γ} → PC x → P (constr (k , x))
          method = subst id (lookupTabulate con-method k) (lookupMember methods k)

          PC′ : ∀ C′ (x : ⟦ C′ ⟧C (μ D) γ) → AllC P′ x → PC (mapC from x)
          PC′ (κ γ   ) (_) (H      ) = tt
          PC′ (ι γ C′) (x , d) (Px , Pd) = Px , PC′ C′ d Pd
          PC′ (σ S C′) (s , d) (Pd     ) = PC′ (C′ s) d Pd

      elim : ∀ {γ} → (x : A γ) → P x
      elim x rewrite sym (from∘to x) = Ind.ind to-hypothesis (to x)


  -- | Returns the type of the eliminator for the given datatype
  Elim : ∀ {a b} {I : Set a} (A : I → Set (a ⊔ b)) ⦃ H : HasDesc {b = b} A ⦄
           {c} (P : ∀ {i} → A i → Set c)
       → Set (a ⊔ b ⊔ c)
  Elim A ⦃ H ⦄ {b} P = curryMembersType {b = b} (Elim.elim A H P)
  

  -- | Returns the eliminator for the given datatype
  elim : ∀ {a b} {I : Set a} (A : I → Set (a ⊔ b)) ⦃ H : HasDesc {b = b} A ⦄
           {c} (P : ∀ {i} → A i → Set c)
       → Elim A P
  elim A ⦃ H ⦄ P = curryMembers (Elim.elim A H P)
