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
open import Data.Vec.Base     public using (_∷_; []; Vec; map; lookup)
open import Data.Fin.Base     public using (Fin; zero; suc)

open import Agda.Builtin.Reflection public
  using ( ArgInfo; Relevance; Visibility
        ; arg-info; visible; hidden; instance′
        ; modality
        ; relevant; irrelevant
        )


data SetList : ℕ → Setω where
  []  : SetList 0
  _∷_ : ∀ {a n} → Set a → SetList n → SetList (suc n)


lubLvl : ∀ {n} → SetList n → Level
lubLvl [] = lzero
lubLvl (_∷_ {ℓ} _ AS) = ℓ ⊔ lubLvl AS


lookupLvl : ∀ {n} → SetList n → Fin n → Level
lookupLvl (_∷_ {a} A AS) zero = a
lookupLvl (A ∷ AS) (suc k) = lookupLvl AS k


lookupSet : ∀ {n} (AS : SetList n) k → Set (lookupLvl AS k)
lookupSet (A ∷ AS) zero = A
lookupSet (A ∷ AS) (suc k) = lookupSet AS k

tabulate : ∀ {n} (fl : Fin n → Level) → (∀ k → Set (fl k)) → SetList n
tabulate {zero} fl f = []
tabulate {suc n} fl f = f zero ∷ tabulate (fl ∘ suc) λ k → f (suc k)

Members : ∀ {n} (AS : SetList n) → Setω
Members {n} AS = (k : Fin n) → lookupSet AS k

extend : ∀ {ℓ n} {A : Set ℓ} {AS : SetList n} → A → Members AS → Members (A ∷ AS)
extend x xs zero = x
extend x xs (suc k) = xs k

CurryMembers : ∀ {n} {AS : SetList n} {ℓ} {B : Set ℓ} (f : Members AS → B) → Set (lubLvl AS ⊔ ℓ)
CurryMembers {AS = []} {B = B} f = B
CurryMembers {AS = A ∷ AS} f = (x : A) → CurryMembers {AS = AS} λ m → f (extend x m)


curryMembers : ∀ {n} {AS : SetList n} {ℓ} {B : Set ℓ}
             → (f : Members AS → B)
             → CurryMembers {AS = AS} f
curryMembers {AS = []} {B = B} f = f (λ ())
curryMembers {AS = A ∷ AS} f x = curryMembers λ m → f (extend x m)

lookupTabulate : ∀ {n} (fl : Fin n → Level) (f : ∀ k → Set (fl k))
               → Members (tabulate fl f)
               → (k : Fin n) → f k
lookupTabulate {suc n} fl f m zero = m zero
lookupTabulate {suc n} fl f m (suc k) =
  lookupTabulate (fl ∘ suc) (λ k → f (suc k)) (λ k → m (suc k)) k

mapTabulate : ∀ {n} {fl1 fl2 : Fin n → Level}
                    {f1 : ∀ k → Set (fl1 k)}
                    {f2 : ∀ k → Set (fl2 k)}
               → (f : ∀ k → f1 k → f2 k)
               → Members (tabulate fl1 f1)
               → Members (tabulate fl2 f2)
mapTabulate {zero} f m ()
mapTabulate {suc n} f m zero = f zero (m zero)
mapTabulate {suc n} f m (suc k) = mapTabulate (λ k → f (suc k)) (λ k → m (suc k)) k


{-
tabulate : ∀ {n} {ℓ} → (Fin n → Set ℓ) → SetList n
tabulate {zero} f = []
tabulate {suc n} f = f zero ∷ tabulate (f ∘ suc)

lookupTabulate : ∀ {n} {ℓ} (f : Fin n → Set ℓ)
               → Members (tabulate f)
               → (k : Fin n) → f k
lookupTabulate {suc n} f m zero = m zero
lookupTabulate {suc n} f m (suc k) = lookupTabulate (f ∘ suc) (λ k → m (suc k)) k


mapP : ∀ {a b} {A : Set a} {P : A → Set b} (f : (x : A) → P x) {n : ℕ}
       (xs : Vec A n) → Members (map P xs)
mapP f [] = []
mapP f (x ∷ xs) = (f x) ∷ (mapP f xs)


mapmembers : ∀ {a n} {xs ys : vec (set a) n}
           → (f : (k : fin n) → lookup xs k → lookup ys k)
           → members xs
           → members ys
mapmembers {ys = []}     f []       = []
mapmembers {ys = y ∷ ys} f (z ∷ zs) = (f zero z) ∷ mapmembers (f ∘ suc) zs

mapMembers′ : ∀ {a b n} {B : Set b} {xs : Vec (Set a) n}
           → (f : (k : Fin n) → lookup xs k → B)
           → Members xs
           → Vec B n
mapMembers′ f []       = []
mapMembers′ f (z ∷ zs) = (f zero z) ∷ mapMembers′ (f ∘ suc) zs




-}
