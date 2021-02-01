{-# OPTIONS --safe --without-K #-}

module Generics.Simple.Desc where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Data.Product
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Relation.Binary.PropositionalEquality
open import Data.Product.Properties
open import Function.Bundles
open import Data.Unit.Polymorphic

open import Level
open import Data.Fin.Base
open import Data.Vec.Base
open import Function.Base
open import Agda.Builtin.Reflection
open import Reflection.Argument.Information

private
  variable
    a b : Level
    I   : Set a
    n   : ℕ

-- from effectfully's

data RelValue {a} (A : Set a) : Relevance → Set a where
  relv :  A → RelValue A relevant
  irrv : .A → RelValue A irrelevant


<_>_ : ∀ {a} → Relevance → Set a → Set a
<_>_ = flip RelValue


data ConDesc (I : Set a) (b : Level) : Set (a ⊔ lsuc b) where
  κ : (γ : I) → ConDesc I b
  ι : (γ : I) (ai : ArgInfo) (C : ConDesc I b) → ConDesc I b
  σ : (S : Set b) (ai : ArgInfo) (f : < relevance ai > S → ConDesc I b) → ConDesc I b

syntax σ S (λ x → B) = σ[ x ∈ S ] B


⟦_⟧C : ∀ {a} {I : Set a} {b} → ConDesc I b → (I → Set (a ⊔ b)) → I → Set (a ⊔ b)
⟦_⟧C {a} {b = b} (κ γ) X i = Lift (a ⊔ b) (γ ≡ i)
⟦ ι γ ai C ⟧C X i = < relevance ai > X γ × ⟦ C ⟧C X i
⟦ σ S ai C ⟧C X i = Σ[ s ∈ < relevance ai > S ] ⟦ C s ⟧C X i


Desc : ∀ (I : Set a) b → ℕ → Set (a ⊔ lsuc b)
Desc I b = Vec (ConDesc I b)


⟦_⟧D : {I : Set a} → Desc I b n → (I → Set (a ⊔ b)) → (I → Set (a ⊔ b)) 
⟦_⟧D {n = n} D X i = Σ[ k ∈ Fin n ] ⟦ lookup D k ⟧C X i


data μ {I : Set a} (D : Desc I b n) (i : I) : Set (a ⊔ b) where
  ⟨_⟩ : ⟦ D ⟧D (μ D) i → μ D i


private
  variable
    D   : Desc I b n
    i   : I

unwrap : μ D i → ⟦ D ⟧D (μ D) i
unwrap ⟨ x ⟩ = x


AllC : ∀ {a b c} {I : Set a} {A : I → Set (a ⊔ b)}
        (P : ∀ {i} → A i → Set c)
        {C : ConDesc I b}
     → ∀ {i} → ⟦ C ⟧C A i → Set (a ⊔ b ⊔ c)
AllC P {C = κ γ  } tt = ⊤
AllC P {C = ι γ ai C} (x , d) = P x × AllC P d
AllC P {C = σ S ai C} (s , d) = AllC P d


All : ∀ {a b c n} {I : Set a} (D : Desc I b n)
      (P : ∀ {i} → μ D i → Set c)
    → ∀ {i} → μ D i → Set (a ⊔ b ⊔ c)
All D P ⟨ k , x ⟩ = AllC P x


mapC : ∀ {a b} {I : Set a} {A B : I → Set (a ⊔ b)}
       (f : ∀ {γ} → A γ → B γ)
       {C : ConDesc I b}
     → ∀ {i} → ⟦ C ⟧C A i → ⟦ C ⟧C B i
mapC f {κ γ  } (x    ) = x
mapC f {ι γ ai C} (x , d) = f x , mapC f d
mapC f {σ S ai C} (s , d) = s   , mapC f d


mapD : ∀ {a b n} {I : Set a} {A B : I → Set (a ⊔ b)}
       (f : ∀ {i} → A i → B i)
       {D : Desc I b n} 
     → ∀ {i} → ⟦ D ⟧D A i → ⟦ D ⟧D B i
mapD f (k , x) = k , mapC f x


module Properties where

  open Inverse using (f)

  mapC-id : ∀ {a b} {I : Set a} {A : I → Set (a ⊔ b)}
            {f   : ∀ {i} → A i → A i}
            (fid : ∀ {i} (x : A i) → f x ≡ x)
            {C : ConDesc I b}
          → ∀ {i} {x : ⟦ C ⟧C A i} → mapC f x ≡ x

  mapC-id fid {κ γ  } {x = x} = refl
  mapC-id {f = f} fid {ι γ ai C} {x = x , d} rewrite fid x | mapC-id fid {x = d} = refl
  mapC-id fid {σ S ai C} {x = x , d} rewrite mapC-id fid {x = d} = refl


  mapC-∘ : ∀ {a b} {I : Set a} {A B C : I → Set (a ⊔ b)}
           {f : ∀ {i} → A i → B i}
           {g : ∀ {i} → B i → C i}
           {C′ : ConDesc I b}
         → ∀ {i} {x : ⟦ C′ ⟧C A i} → mapC (g ∘ f) x ≡ mapC g (mapC f x)

  mapC-∘ {C′ = κ γ  } = refl
  mapC-∘ {C′ = ι γ ai C} = Σ-≡,≡↔≡ .f (refl , mapC-∘)
  mapC-∘ {C′ = σ S ai C} = Σ-≡,≡↔≡ .f (refl , mapC-∘)
