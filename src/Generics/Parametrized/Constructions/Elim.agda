module Generics.Parametrized.Constructions.Elim where

open import Generics.Prelude hiding (lookup)
open import Generics.Parametrized.Telescope
open import Generics.Parametrized.Desc3
open import Generics.Parametrized.HasDesc
import Generics.Parametrized.Constructions.Induction as Induction

module Elim {P} {I : ExTele P} {ℓ} (A : Curried′ P I ℓ) (H : HasDesc {P} {I} {ℓ} A)
            {c} (Pr : ∀ {pi} → uncurry′ P I A pi → Set c) where

      open HasDesc H
      
      IH : ∀ (C : CDesc P ε I ℓ) {pi} → Extend C ℓ A′ pi → Set (ℓ ⊔ c)
      IH C x = AllExtend C A′ Pr x

      con-method : Fin n → Set (levelTel P ⊔ levelTel I ⊔ ℓ ⊔ c)
      con-method k = ∀ {pi} {x : Extend (lookup D k)  ℓ A′ pi } → IH (lookup D k) x → Pr (constr (k , x))

      elim-methods : Vec (Set (levelTel P ⊔ levelTel I ⊔ ℓ ⊔ c)) n
      elim-methods = tabulate con-method

      Pr′ : ∀ {pi} → μ D pi → Set c
      Pr′ = Pr ∘ from

      module Ind = Induction Pr′

      module _ (methods : Members elim-methods) where

         to-hypothesis : ∀ {pi} (X : μ D pi) → All D Pr′ X → Pr′ X
         to-hypothesis {pi} ⟨ k , x ⟩ all
           rewrite sym (constr-coh (k , x)) = method (mapAllExtend C from Pr all)
           where
             C = lookup D k

             method : ∀ {pi} {x : Extend C ℓ A′ pi} → IH C x → Pr (constr (k , x))
             method = subst id (lookupTabulate con-method k) (lookupMember methods k)

         elim : ∀ {pi} (x : A′ pi) → Pr x
         elim x rewrite sym (from∘to x) = Ind.ind to-hypothesis (to x)

{-


-}
