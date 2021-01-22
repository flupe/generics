{-# OPTIONS --safe --without-K #-}
module Generics.Prelude where

open import Agda.Primitive    public
open import Agda.Builtin.Nat  public renaming (Nat to ℕ)
open import Agda.Builtin.Unit public
open import Agda.Builtin.List public
open import Function.Base     public
open import Data.Product      public hiding (map; uncurry; uncurry′)
open import Level             public using (Lift; lift)

open import Relation.Binary.PropositionalEquality public hiding ([_])
open import Data.Vec.Base     public using (_∷_; []; Vec; lookup; map; tabulate)
open import Data.Fin.Base     public using (Fin; zero; suc)


data Members {a} : {n : ℕ} → Vec (Set a) n → Set (lsuc a) where
  []  : Members []
  _∷_ : ∀ {n A AS} → A → Members {n = n} AS → Members (A ∷ AS)


lookupMember : ∀ {a n} {xs : Vec (Set a) n} → Members xs → ∀ k → lookup xs k
lookupMember (x ∷ _ ) (zero ) = x
lookupMember (_ ∷ xs) (suc k) = lookupMember xs k


curryMembersType : ∀ {a b n} {xs : Vec (Set a) n} {B : Set (a ⊔ b)} (f : Members xs → B) → Set (a ⊔ b)
curryMembersType {a} {b} {xs = xs} {B} f = aux xs
  where
    aux : ∀ {n} → Vec (Set a) n → Set (a ⊔ b)
    aux []       = B
    aux (A ∷ AS) = A → aux AS


declareMembers : ∀ {a n} {xs : Vec (Set a) n}
               → (f : (k : Fin n) → lookup xs k)
               → Members xs
declareMembers {xs = []}     f = []
declareMembers {xs = A ∷ xs} f = f zero ∷ declareMembers (f ∘ suc)


curryMembers : ∀ {a b n} {xs : Vec (Set a) n} {B : Set (a ⊔ b)}
             → (f : Members xs → B)
             → curryMembersType {b = b} f
curryMembers {xs = []}     f = f []
curryMembers {xs = A ∷ AS} f = λ x → curryMembers (f ∘ (x ∷_))


mapP : ∀ {a b} {A : Set a} {P : A → Set b} (f : (x : A) → P x) {n : ℕ}
       (xs : Vec A n) → Members (map P xs)
mapP f [] = []
mapP f (x ∷ xs) = (f x) ∷ (mapP f xs)


mapMembers : ∀ {a n} {xs ys : Vec (Set a) n}
           → (f : (k : Fin n) → lookup xs k → lookup ys k)
           → Members xs
           → Members ys
mapMembers {ys = []}     f []       = []
mapMembers {ys = y ∷ ys} f (z ∷ zs) = (f zero z) ∷ mapMembers (f ∘ suc) zs

mapMembers′ : ∀ {a b n} {B : Set b} {xs : Vec (Set a) n}
           → (f : (k : Fin n) → lookup xs k → B)
           → Members xs
           → Vec B n
mapMembers′ f []       = []
mapMembers′ f (z ∷ zs) = (f zero z) ∷ mapMembers′ (f ∘ suc) zs


lookupTabulate : ∀ {a n} {A : Set a} (f : Fin n → A)
               → (k : Fin n) → lookup (tabulate f) k ≡ f k
lookupTabulate {n = suc n} f zero    = refl
lookupTabulate {n = suc n} f (suc k) = lookupTabulate (f ∘ suc) k
