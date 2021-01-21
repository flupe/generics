open import Generics.Simple.Desc
open import Data.Unit.Polymorphic
open import Data.Product
open import Data.Vec.Base
open import Relation.Binary.PropositionalEquality


module Generics.Simple.Constructions.Induction
         {a b n} {I : Set a} (D : Desc I b n)
         {c} (P : ∀ {i} → μ D i → Set c) where

  module _ (f : {i : I} (x : μ D i) → All D P x → P x) where
    all-con : ∀ {C γ} (x : ⟦ C ⟧C (μ D) γ) → AllC P x
    all     : ∀ {γ} (x : μ D γ) → All D P x

    all-con {κ _  } _ = tt
    all-con {ι _ C} (x , d) = f x (all x) , all-con {C} d
    all-con {σ _ F} (s , d) = all-con {F s} d

    all ⟨ k , x ⟩ = all-con {lookup D k} x

    -- | The generalized induction principle
    ind : ∀ {γ} (x : μ D γ) → P x
    ind x = f x (all x)
