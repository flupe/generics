module Simple where

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

open import Data.Vec.Base hiding (map)
open import Data.Vec.Relation.Unary.All hiding (map)
open import Data.Fin.Base
open import Data.Nat.Base

open import Generics.Desc.Simple
open import Generics.HasDesc.Simple

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

-- TODO: move following elsewhere

cong : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

subst : ∀ {i j} {A : Set i} {B : A → Set j} {x y} → x ≡ y → B x → B y
subst refl x = x

Σ≡ : ∀ {i j} {A : Set i} {B : A → Set j} {x₁ x₂ : A} {y₁ : B x₁} {y₂ : B x₂}
   → (p : x₁ ≡ x₂) → subst p y₁ ≡ y₂ → (x₁ , y₁) ≡ (x₂ , y₂)
Σ≡ refl refl = refl

sym : ∀ {i} {A : Set i} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

instance
  natHasDesc : HasDesc {I = ⊤} (λ _ → ℕ)

  natHasDesc .n = 2
  natHasDesc .D = natD

  natHasDesc .to zero    = ze
  natHasDesc .to (suc n) = su (natHasDesc .to n)

  natHasDesc .from ⟨ zero     , refl     ⟩ = zero
  natHasDesc .from ⟨ suc zero , n , refl ⟩ = suc (natHasDesc .from n)

  natHasDesc .to∘from ⟨ zero , refl ⟩         = refl
  natHasDesc .to∘from ⟨ suc zero , n , refl ⟩ = cong (λ x → ⟨ suc zero , x ⟩)
                                                     (Σ≡ {!!} {!!})

  natHasDesc .from∘to zero    = refl
  natHasDesc .from∘to (suc n) = cong suc (natHasDesc .from∘to n)

  natHasDesc .constr zero       = zero
  natHasDesc .constr (suc zero) = suc

  natHasDesc .constr-proof zero         = refl
  natHasDesc .constr-proof (suc zero) n = cong suc (sym (natHasDesc .from∘to n))


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
