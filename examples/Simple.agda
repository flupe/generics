module Simple where

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

open import Data.Vec.Base hiding (map)
open import Data.Vec.Relation.Unary.All hiding (map)
open import Data.Fin.Base hiding (_≤_; _+_)
open import Data.Nat.Base
open import Relation.Binary.PropositionalEquality
open import Function.Bundles
open import Data.Product.Properties
open import Level hiding (zero; suc)

open import Generics.Simple.Desc
open import Generics.Simple.HasDesc2
open import Generics.Simple.Constructions.Elim

-- description of natural numbers
natD : Desc ⊤ 2
natD = κ tt
     ∷ ι tt (κ tt)
     ∷ []

nat : Set
nat = μ natD tt

ze : nat
ze = ⟨ zero , refl ⟩

su : nat → nat
su n = ⟨ suc zero , n , refl ⟩

open HasDesc

instance
  natHasDesc : HasDesc {I = ⊤} (λ _ → ℕ)

  natHasDesc .n = 2
  natHasDesc .D = natD

  natHasDesc .names = "zero" ∷ "suc" ∷ []

  natHasDesc .to zero    = ze
  natHasDesc .to (suc n) = su (natHasDesc .to n)

  natHasDesc .from ⟨ zero     , refl     ⟩ = zero
  natHasDesc .from ⟨ suc zero , n , refl ⟩ = suc (natHasDesc .from n)

  natHasDesc .to∘from ⟨ zero     , refl     ⟩ = refl
  natHasDesc .to∘from ⟨ suc zero , n , refl ⟩ rewrite (natHasDesc .to∘from n) = cong ⟨_⟩ refl
  natHasDesc .from∘to zero    = refl
  natHasDesc .from∘to (suc n) = cong suc (natHasDesc .from∘to n)

  natHasDesc .constr (zero    ) (refl    ) = zero
  natHasDesc .constr (suc zero) (n , refl) = suc n

  natHasDesc .constr-proof (zero    ) (refl    ) = refl
  natHasDesc .constr-proof (suc zero) (n , refl) = refl


nat-elim : ∀ {i} (P : ℕ → Set i) → Elim (λ _ → ℕ) P
nat-elim P = elim _ _

thm : ∀ n → n ≤ n + 1
thm = nat-elim (λ n → n ≤ n + 1)
        (λ where {tt} {refl    } _          → z≤n     )
        (λ where {tt} {n , refl} (n≤sn , _) → s≤s n≤sn)


vecD : (A : Set) → Desc ℕ 2
vecD A = κ 0
       ∷ σ[ n ∈ ℕ ] σ[ x ∈ A ] ι n (κ (suc n))
       ∷ []

vec : (A : Set) → ℕ → Set
vec A = μ (vecD A)

-- nil : ∀ {A} → vec A 0
-- nil = ⟨ zero , refl ⟩

-- cons : ∀ {n A} → A → vec A n → vec A (suc n)
-- cons x xs = ⟨ suc zero , _ , x , xs , refl ⟩

pattern nil       = ⟨ zero , refl ⟩
pattern cons x xs = ⟨ suc zero , _ , x , xs , refl ⟩

map : ∀ {n A B} → (A → B) → vec A n → vec B n
map f (nil      ) = nil
map f (cons x xs) = cons (f x) (map f xs)
