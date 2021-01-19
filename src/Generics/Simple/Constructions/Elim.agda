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

  module Elim {i} {I : Set i} (A : I → Set i) (H : HasDesc A)
              {j} (P : ∀ {γ} → A γ → Set j) where
                
    open HasDesc H

    PC : ∀ {C γ} → ⟦ C ⟧C A γ → Set (i ⊔ j)
    PC {κ γ  } x       = ⊤
    PC {ι γ C} (x , d) = P x × PC d
    PC {σ S C} (s , d) = PC d

    -- | Returns the type of the induction method for the kth constructor
    con-method : Fin n → Set (i ⊔ j)
    con-method k = ∀ {γ} {x : ⟦ lookup D k ⟧C A γ} → PC x → P (constr k x) 

    -- | A vector containing the types for every induction method
    elim-methods : Vec (Set (i ⊔ j)) n
    elim-methods = tabulate con-method

    P′ : ∀ {γ} → μ D γ → Set j
    P′ x′ = P (from x′)

    module Ind = Induction D P′

    module _ (methods : Members elim-methods) where
      
      to-hypothesis : ∀ {γ} (X : μ D γ) → Ind.All X → P′ X
      to-hypothesis {γ} X@(⟨ k , x ⟩) IH
        rewrite sym (constr-proof k x) = method (PC′ C x IH)
        where
          C = lookup D k

          method : ∀ {γ} {x : ⟦ C ⟧C A γ} → PC x → P (constr k x)
          method = subst id (lookupTabulate con-method k) (lookupMember methods k)

          PC′ : ∀ C′ (x : ⟦ C′ ⟧C (μ D) γ) → Ind.AllCon C′ x → PC (mapC from x)
          PC′ (κ γ   ) (refl ) (H      ) = tt
          PC′ (ι γ C′) (x , d) (Px , Pd) = Px , PC′ C′ d Pd
          PC′ (σ S C′) (s , d) (Pd     ) = PC′ (C′ s) d Pd

      elim : ∀ {γ} → (x : A γ) → P x
      elim x rewrite sym (from∘to x) = Ind.ind to-hypothesis (to x)


  -- | Returns the type of the eliminator for the given datatype
  Elim : ∀ {a} {I : Set a} (A : I → Set a) ⦃ H : HasDesc {a} A ⦄
           {b} (P : {γ : I} → A γ → Set b)
       → Set (a ⊔ b)
  Elim A ⦃ H ⦄ {b} P = curryMembersType {b = b} (Elim.elim A H P)
  

  -- | Returns the eliminator for the given datatype
  elim : ∀ {a} {I : Set a} (A : I → Set a) ⦃ H : HasDesc {a} A ⦄
           {b} (P : {γ : I} → A γ → Set b)
       → Elim A P
  elim A ⦃ H ⦄ P = curryMembers (Elim.elim A H P)
