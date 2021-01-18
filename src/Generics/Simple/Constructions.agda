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


module Induction {i n} {I : Set i} (D : Desc I n) {j} (P : {γ : I} → μ D γ → Set j) where

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


module Eliminator {i} {I : Set i} (A : I → Set i) (H : HasDesc A)
                  {j} (P : ∀ {γ} → A γ → Set j) where

  open HasDesc H -- retrieve description, conversion methods, constructors

  unfold : (tie : ∀ {γ} → A γ → Set (i ⊔ j)) → ∀ C → Constr A C → Set (i ⊔ j)
  unfold tie (κ _  ) con = tie con
  unfold tie (ι γ C) con = (x : A γ) → P x → unfold tie (C  ) (con x)
  unfold tie (σ S C) con = (x : S)         → unfold tie (C x) (con x)

  -- | Returns the type of the induction method for the kth constructor
  con-method : Fin n → Set (i ⊔ j)
  con-method k = unfold (λ x → ⊤ {i ⊔ j} → P x) (lookup D k) (constr k)

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
             → {cons : Constr A C′}                            -- ^ partial constructor in A γ
             → Constr-proof′ A to C′ f cons 
             → unfold g C′ cons                                -- ^ partial induction method for C
             → (mk : ⟦ C′ ⟧C (μ D) γ → ⟦ C ⟧C (μ D) γ) -- ^ build full constructor from partial constructor
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
Elim A ⦃ H ⦄ {b} P = curryMembersType {b = b} (Eliminator.elim A H P)

-- | Returns the eliminator for the given datatype
elim : ∀ {a} {I : Set a} (A : I → Set a) ⦃ H : HasDesc {a} A ⦄
             {b} (P : {γ : I} → A γ → Set b)
     → Elim A P
elim A ⦃ H ⦄ P = curryMembers (Eliminator.elim A H P)



module Case {a} {I : Set a} (A : I → Set a) ⦃ H : HasDesc {a} A ⦄
            {b} (P : {γ : I} → A γ → Set b) where

  open HasDesc H

  unfold : ∀ C → Constr A C → (∀ {γ} → A γ → Set (a ⊔ b)) → Set (a ⊔ b)
  unfold (κ _  ) con tie = tie con
  unfold (ι γ C) con tie = (x : A γ) → unfold (C  ) (con x) tie
  unfold (σ S C) con tie = (x : S  ) → unfold (C x) (con x) tie 

  -- | Returns the type of the case method for the kᵗʰ constructor
  con-method : Fin n → Set (a ⊔ b)
  con-method k = unfold (lookup D k) (constr k) λ x → ⊤ {a ⊔ b} → P x

  -- | A vector containing the types of every constructor's case method
  case-methods : Vec (Set (a ⊔ b)) n
  case-methods = tabulate (con-method)

  module Elim = Eliminator A H P

  -- | Converts a kᵗʰ case method to a kᵗʰ elim method
  case-to-elim : (k : Fin n) → con-method k → Elim.con-method k
  case-to-elim k method =
    walk (lookup D k) method
    where
      walk : ∀ C {con} → unfold C con _ → Elim.unfold _ C con
      walk (κ γ  ) m = m
      walk (ι γ C) m = λ x _ → walk C (m x)
      walk (σ S C) m = λ s   → walk (C s) (m s)

  -- | The generalized case analysis principle
  case : Members case-methods → {γ : I} (x : A γ) → P x
  case = Elim.elim ∘ {!!} -- mapMembers {!!} -- case-to-elim 

-- | Returns the type of the case analysis principle for the given datatype
Case : ∀ {a} {I : Set a} (A : I → Set a) ⦃ H : HasDesc {a} A ⦄
              {b} (P : {γ : I} → A γ → Set b)
          → Set (a ⊔ b)
Case A ⦃ H ⦄ {b} P = curryMembersType {b = b} (Case.case A P)

-- | Returns the case analysis principle for the given datatype
case : ∀ {a} {I : Set a} (A : I → Set a) ⦃ H : HasDesc {a} A ⦄
             {b} (P : {γ : I} → A γ → Set b)
         → Case A P
case A ⦃ H ⦄ P = curryMembers (Case.case A P)

{-

{-



module Recursion {i n} {I : Set i} (D : Desc {i} I n)
                 {j} (P : ∀ {γ} → μ D γ → Set j) where

  mutual
    -- | Predicate stating that P holds for every recursive subobject
    -- | *guarded by constructors* in x
    BelowCon : ∀ {C γ} (x : ⟦ C ⟧ᶜ (μ D) γ) → Set j
    BelowCon {κ _  } _       = ⋆
    BelowCon {ι _ _} (x , d) = (P x × Below x) × BelowCon d
    BelowCon {π _ _} (_ , d) = BelowCon d

    -- | Predicate stating that P holds for every recursive subobject
    -- | *guarded by constructors* in x
    Below : ∀ {γ} (x : μ D γ) → Set j
    Below ⟨ _ , x ⟩ = BelowCon x

  module _ (p : ∀ {γ} (x : μ D γ) → Below x → P x) where

    step : ∀ {γ} (x : μ D γ) → Below x → P x × Below x
    step x m = p x m , m

    mutual
      below-con : ∀ {C γ} (x : ⟦ C ⟧ᶜ (μ D) γ) → BelowCon x
      below-con {κ _  } _       = ∗
      below-con {ι _ _} (x , d) = step x (below x) , below-con d
      below-con {π _ _} (_ , d) = below-con d

      below : ∀ {γ} (x : μ D γ) → Below x
      below ⟨ _ , x ⟩ = below-con x
  
    -- | The generalized structural recursion principle
    rec : ∀ {γ} (x : μ D γ) → P x
    rec x = p x (below x)


module Recursor {i} {I : Set i} (A : I → Set i) ⦃ H : HasDesc {i} A ⦄
                {j} (P : {γ : I} → A γ → Set j) where

  open HasDesc ⦃ ... ⦄
  module R = Recursion D (P ∘ from)

  Below : ∀ {γ} → A γ → Set j
  Below x = R.Below (to x)

  rec : (∀ {γ} (x : A γ) → Below x → P x) → ∀ {γ} (x : A γ) → P x
  rec f x = transport P (from∘to x) px
    where
      px : P (from (to x))
      px = R.rec (λ x′ bx′ → f (from x′) (transport R.Below (sym (to∘from x′)) bx′))
                 (to x)


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

module SoIAmConfusion {a n} {I : Set a} (D : Desc {a} I n)
                 (X : I → Set a) where

  -- | Relation between two interpretations of the same constructor
  -- maybe we should use JMeq instead?
  NoConfusionCon : ∀ {C γ} (x y : ⟦ C ⟧ᶜ X γ) → Set a
  NoConfusionCon {κ _  } (refl  ) (refl  ) = ⊤′
  NoConfusionCon {ι _ _} (x , dx) (y , dy) = x ≡ y × NoConfusionCon dx dy
  NoConfusionCon {π _ _} (x , dx) (y , dy) = Σ (x ≡ y) λ { refl → NoConfusionCon dx dy }

  NoConfusion : ∀ {γ} (x y : ⟦ D ⟧ᵈ X γ) → Set a
  NoConfusion (kx , x) (ky , y) with kx == ky
  ... | yes refl = NoConfusionCon x y
  ... | no kx≢ky = ⊥′

  noConfRefl : ∀ {C γ} (x : ⟦ C ⟧ᶜ X γ) → NoConfusionCon x x
  noConfRefl {κ γ  } refl    = unit
  noConfRefl {ι γ C} (x , d) = refl , noConfRefl d
  noConfRefl {π S C} (s , d) = refl , noConfRefl d

  noConf : ∀ {γ} {x y : ⟦ D ⟧ᵈ X γ} → x ≡ y → NoConfusion x y
  noConf {x = kx , x} {ky , y} refl with kx == ky
  ... | yes refl = noConfRefl x
  ... | no kx≢ky = ⊥-elim (kx≢ky refl) 

  noConfCon : ∀ {C γ} {x y : ⟦ C ⟧ᶜ X γ} → NoConfusionCon x y → x ≡ y
  noConfCon {κ γ  } {x = refl} {refl} nc = refl
  noConfCon {ι γ C} (refl , nc) = cong _ (noConfCon nc)
  noConfCon {π S C} (refl , nc) = cong _ (noConfCon nc)

  noConf₂ : ∀ {γ} {x y : ⟦ D ⟧ᵈ X γ} → NoConfusion x y → x ≡ y
  noConf₂ {x = kx , x} {ky , y} with kx == ky
  ... | yes refl = cong (kx ,_) ∘ noConfCon
  ... | no kx≢ky = λ ()


module NoConfusion {a} {I : Set a} (A : I → Set a) ⦃ H : HasDesc {a} A ⦄ where

  open HasDesc ⦃ ... ⦄
  module C = SoIAmConfusion D A

  NoConfusion : ∀ {γ} (x y : A γ) → Set a
  NoConfusion x y = C.NoConfusion (step x) (step y)

  noConf : ∀ {γ} {x y : A γ} → x ≡ y → NoConfusion x y
  noConf {x = x} {y} = C.noConf ∘ cong step

  noConf₂ : ∀ {γ} {x y : A γ} → NoConfusion x y → x ≡ y
  noConf₂ {x = x} {y} = aux ∘ C.noConf₂
    where
      aux : step x ≡ step y → x ≡ y
      aux p = trans (sym $ unstep∘step x)
            $ trans (cong unstep p) (unstep∘step y)

-}
