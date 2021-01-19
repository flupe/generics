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
      
      -- goal: prove that given every induction method on A γ, we can retrieve the 
      -- induction hypothesis on μ D γ
      to-hypothesis : ∀ {γ} (X : μ D γ) → Ind.All X → P′ X
      to-hypothesis {γ} X@(⟨ k , x ⟩) = {!!}
        where
          C      = lookup D k
          method = lookupMember methods k

      -- then, it's only a matter of applying the generalized induction principle
      elim : ∀ {γ} → (x : A γ) → P x
      elim x rewrite sym (from∘to x) = Ind.ind to-hypothesis (to x)

{-

  module Elim {i} {I : Set i} (A : I → Set i) (H : HasDesc A)
              {j} (P : ∀ {γ} → A γ → Set j) where

    open HasDesc H

    unfold : (tie : ∀ {γ} → A γ → Set (i ⊔ j)) → ∀ C → Constr A C → Set (i ⊔ j)
    unfold tie (κ _  ) con = tie con
    unfold tie (ι γ C) con = (x : A γ) → P x → unfold tie (C  ) (con x)
    unfold tie (σ S C) con = (x : S)         → unfold tie (C x) (con x)

    -- | Returns the type of the induction method for the kth constructor
    con-method : Fin n → Set (i ⊔ j)
    con-method k = unfold (λ x → ⊤ {i ⊔ j} → P x) (lookup D k) (constr k)


    P′ : ∀ {γ} → μ D γ → Set j
    P′ x′ = P (from x′)

    module Ind = Induction D P′


    module _ (methods : Members elim-methods) where

      -- goal: prove that given every induction method on A γ, we can retrieve the 
      -- induction hypothesis on μ D γ
      to-hypothesis : ∀ {γ} (X : μ D γ) → Ind.All X → P′ X
      to-hypothesis {γ} X@(⟨ k , x ⟩) IH = walk C (constr-proof k) method id pack x IH refl
        where
          -- we retrieve the correct induction method from our little bag
          C      = lookup D k

          method = subst id (lookupTabulate _ k) (lookupMember methods k)

          -- this function gets called at the end and finishes the proof
          pack : ∀ {x₁ x₂} → x₂ ≡ from ⟨ k , x₁ ⟩ → x ≡ x₁ → (⊤ {i ⊔ j} → P x₂) → P′ X
          pack refl refl Px₂ = Px₂ tt
          
          -- the entire point of this little walk is to construct x₁ and x₂
          walk : ∀ C′ {f : ∀ {γ} → ⟦ C′ ⟧C (μ D) γ → A γ → Set i}
                      {g : ∀ {γ} → A γ → Set (i ⊔ j)}
               → {cons : Constr A C′}                     -- ^ partial constructor in A γ
               → Constr-proof′ A to C′ f cons 
               → unfold g C′ cons                         -- ^ partial induction method for C
               → (mk : ⟦ C′ ⟧C (μ D) γ → ⟦ C ⟧C (μ D) γ) 
               → (∀ {y z} → f y z → x ≡ mk y → g z → P′ X)
               → ∀ x′ → Ind.AllCon C′ x′ → x ≡ mk x′
               → P′ X
          walk (κ γ   ) {f} {g} {cons} p Px x tie refl _ w = tie p w Px
          walk (ι γ C′) {f} {g} {cons} mkp mkP mk tie (x , d) (Px , Pd) =
            walk C′ (mkp (from x)) (mkP (from x) Px) (mk ∘ (x ,_))
                 (tie ∘ subst (λ x → f (x , _) _) (to∘from x)) d Pd 
          walk (σ S C′) {f} {g} {cons} mkp mkP mk tie (s , d) =
            walk (C′ s) (mkp s) (mkP s) (mk ∘ (s ,_)) tie d 


      -- then, it's only a matter of applying the generalized induction principle
      elim : {γ : I} → (x : A γ) → P x
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

-}
