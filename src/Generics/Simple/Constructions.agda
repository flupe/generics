{-# OPTIONS --safe #-}
module Generics.Simple.Constructions where

open import Generics.Simple.Desc
open import Generics.Simple.HasDesc
open import Data.Unit.Polymorphic.Base
open import Data.Vec.Base
open import Data.Product
open import Data.Fin.Base
open import Data.Nat.Base using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality
open import Agda.Primitive
open import Generics.Prelude
open import Function.Base




module Recursion {i n} {I : Set i} (D : Desc {i} I n)
                 {j} (P : ∀ {γ} → μ D γ → Set j) where

  mutual
    -- | Predicate stating that P holds for every recursive subobject
    -- | *guarded by constructors* in x
    BelowCon : ∀ {C γ} (x : ⟦ C ⟧C (μ D) γ) → Set j
    BelowCon {κ _  } _       = ⊤
    BelowCon {ι _ _} (x , d) = (P x × Below x) × BelowCon d
    BelowCon {σ _ _} (_ , d) = BelowCon d

    -- | Predicate stating that P holds for every recursive subobject
    -- | *guarded by constructors* in x
    Below : ∀ {γ} (x : μ D γ) → Set j
    Below ⟨ _ , x ⟩ = BelowCon x

  module _ (p : ∀ {γ} (x : μ D γ) → Below x → P x) where

    step : ∀ {γ} (x : μ D γ) → Below x → P x × Below x
    step x m = p x m , m

    mutual
      below-con : ∀ {C γ} (x : ⟦ C ⟧C (μ D) γ) → BelowCon x
      below-con {κ _  } _       = tt
      below-con {ι _ _} (x , d) = step x (below x) , below-con d
      below-con {σ _ _} (_ , d) = below-con d

      below : ∀ {γ} (x : μ D γ) → Below x
      below ⟨ _ , x ⟩ = below-con x
  
    -- | The generalized structural recursion principle
    rec : ∀ {γ} (x : μ D γ) → P x
    rec x = p x (below x)



module Recursor {i} {I : Set i} (A : I → Set i) ⦃ H : HasDesc {i} A ⦄
                {j} (P : {γ : I} → A γ → Set j) where

  open HasDesc H
  module R = Recursion D (P ∘ from)

  Below : ∀ {γ} → A γ → Set j
  Below x = R.Below (to x)

  rec : (∀ {γ} (x : A γ) → Below x → P x) → ∀ {γ} (x : A γ) → P x
  rec f x rewrite sym (from∘to x) = px -- transport P (from∘to x) px
    where
      px : P (from (to x))
      px = R.rec (λ x′ bx′ → f (from x′) (subst R.Below (sym $ to∘from x′) bx′)) (to x)

{-

{-





  Below-method : (k : Fin (n H)) → indexVec (Elim.elim-methods (const (Set j))) k
  Below-method k =
    let meth = walk (indexVec (D H) k) (constr H k) (λ x _ _ → x) []
    in transport id (sym (indexTabulate (Elim.con-method (const (Set j))) k)) meth
    where
      walk : (C : ConDesc I)
           → (con : con-type A C)
           → {f : ∀ {γ} → A γ → Set (i ⊔ lsuc j)}
           → (tie : Set j → ∀ {γ} (x : A γ) → f x)
           → List (Set j)
           → Elim.unfold (const (Set j)) C con f
      walk (κ _  ) con tie acc = tie {!!} con
      walk (ι γ C) con tie acc = λ x Px → walk C (con x) tie ((Px × P x) ∷ acc)
      walk (π _ C) con tie acc = λ s → walk (C s) (con s) tie acc

  -- | Predicate stating that P holds for every recursive subobject
  -- | *guarded by constructors* in x
  -- Below using the eliminator
  Below : ∀ {γ} (x : A γ) → Set j
  Below = Elim.elim _ (declareMembers Below-method)


  -- below-method : (k : Fin (n H)) → indexVec (Elim.elim-methods Below) k
  -- below-method k =
  --   let meth = walk (indexVec (D H) k) (constr H k) λ x → {!!}
  --   in transport id (sym (indexTabulate (Elim.con-method Below) k)) {!!}
  --   where
  --     walk : (C : ConDesc I)
  --          → (con : con-type A C)
  --          → {f : ∀ {γ} → (x : A γ) → Set (i ⊔ j)}
  --          → (tie : ∀ {γ} (x : A γ) → f x)
  --          → Elim.unfold Below C con f
  --     walk (κ _  ) con tie = {!!}
  --     walk (ι γ C) con tie = λ x Bx → {!!}
  --     walk (π _ C) con tie = λ s → walk (C s) (con s) {!!}


  below : (∀ {γ} (x : A γ) → Below x → P x)
        → ∀ {γ} (x : A γ) → Below x
  below P x = {!through-elim!} -- Elim.elim Below (declareMembers below-method)

  rec : (∀ {γ} (x : A γ) → Below x → P x)
      → ∀ {γ} (x : A γ) → P x
  rec f x = f x (below f x)
  -}

