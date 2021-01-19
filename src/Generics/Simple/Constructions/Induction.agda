open import Generics.Simple.Desc
open import Data.Unit.Polymorphic
open import Data.Product
open import Data.Vec.Base
open import Relation.Binary.PropositionalEquality


module Generics.Simple.Constructions.Induction
         {i n} {I : Set i} (D : Desc I n)
         {j} (P : {γ : I} → μ D γ → Set j) where


  -- | Predicate stating that P holds for every recursive subobject in x
  AllCon : ∀ {γ} (C : ConDesc I) (x : ⟦ C ⟧C (μ D) γ) → Set j
  AllCon (κ _  ) (_    ) = ⊤
  AllCon (ι _ C) (x , d) = P x × AllCon C d
  AllCon (σ _ F) (s , d) = AllCon (F s) d


  -- | Predicate stating that P holds for every recursive subobject in x
  All : ∀ {γ} (x : μ D γ) → Set j
  All ⟨ k , x ⟩ = AllCon (lookup D k) x


  module _ (f : {γ : I} (x : μ D γ) → All x → P x) where
    all-con : ∀ {C γ} (x : ⟦ C ⟧C (μ D) γ) → AllCon C x
    all     : ∀ {γ} (x : μ D γ) → All x

    all-con {κ _  } refl = tt
    all-con {ι _ C} (x , d) = f x (all x) , all-con {C} d
    all-con {σ _ F} (s , d) = all-con {F s} d

    all ⟨ k , x ⟩ = all-con {lookup D k} x
    

    -- | The generalized induction principle
    ind : ∀ {γ} (x : μ D γ) → P x
    ind x = f x (all x)
