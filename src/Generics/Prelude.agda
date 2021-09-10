{-# OPTIONS --safe --without-K #-}
module Generics.Prelude where

open import Function.Base     public
open import Data.Product      public hiding (map; uncurry; uncurry′)
open import Level             public using (Setω; Level; _⊔_; Lift; lift)
                                     renaming (zero to lzero; suc to lsuc)

open import Relation.Binary.PropositionalEquality public
  hiding ([_]; Extensionality; ∀-extensionality)
open import Data.Nat.Base     public using (ℕ; zero; suc; _+_)
                                     renaming (_∸_ to _-_)
open import Data.Unit         public using (⊤; tt)
open import Data.List         public using (List; []; _∷_)
open import Data.Vec.Base     public using (Vec; []; _∷_; map; lookup)
open import Data.Fin.Base     public using (Fin; zero; suc)
open import Axiom.Extensionality.Propositional public

open import Agda.Builtin.Reflection public
  using ( ArgInfo; Relevance; Visibility
        ; arg-info; visible; hidden; instance′
        ; modality
        ; relevant; irrelevant
        )

private variable
  m n   : ℕ
  k     : Fin n
  l     : Level
  A B   : Set l

-- Instead of the definitions from Function.Nary.NonDependent in the
-- standard library, we use a *functional* representation of vectors
-- of levels and types. This makes it much easier to work with
-- operations like lookup and tabulate, at the cost of losing certain
-- eta laws for nil and cons (see the comment for `uncurryₙ` below).

Levels : ℕ → Set
Levels n = Fin n → Level

private variable ls : Levels n

[]l : Levels 0
[]l ()

_∷l_ : Level → Levels n → Levels (suc n)
(l ∷l ls) zero = l
(l ∷l ls) (suc k) = ls k

headl : Levels (suc n) → Level
headl ls = ls zero

taill : Levels (suc n) → Levels n
taill ls = ls ∘ suc

⨆ : Levels n → Level
⨆ {zero} ls = lzero
⨆ {suc n} ls = ls zero ⊔ ⨆ (ls ∘ suc)

Sets : (ls : Levels n) → Setω
Sets {n} ls = (k : Fin n) → Set (ls k)

private variable As : Sets ls

[]S : {ls : Levels 0} → Sets ls
[]S ()

_∷S_ : Set (headl ls) → Sets (taill ls) → Sets ls
(A ∷S As) zero    = A
(A ∷S As) (suc k) = As k

headS : Sets ls → Set (headl ls)
headS As = As zero

tailS : Sets ls → Sets (taill ls)
tailS As k = As (suc k)

Els : (As : Sets ls) → Setω
Els {n} As = (k : Fin n) → As k

private variable xs : Els As

[]El : {As : Sets {zero} ls} → Els As
[]El ()

_∷El_ : headS As → Els (tailS As) → Els As
(x ∷El xs) zero    = x
(x ∷El xs) (suc k) = xs k

headEl : Els As → headS As
headEl xs = xs zero

tailEl : Els As → Els (tailS As)
tailEl xs k = xs (suc k)

Pis : (As : Sets ls) (B : Els As → Set l) → Set (⨆ ls ⊔ l)
Pis {zero}  As B = B []El
Pis {suc n} As B = (x : As zero) → Pis (tailS As) (λ xs → B (x ∷El xs))

Arrows : (As : Sets ls) (B : Set l) → Set (⨆ ls ⊔ l)
Arrows As B = Pis As (λ _ → B)

curryₙ : {B : Els As → Set l} → ((xs : Els As) → B xs) → Pis As B
curryₙ {zero}  f = f []El
curryₙ {suc n} f = λ x → curryₙ (λ xs → f (x ∷El xs))

-- It is not possible to define the dependent version of uncurryₙ, as
-- it requires the laws that `xs = []El` for all `xs : Els {zero} As`
-- and `xs = headEl xs ∷El tailEl xs` for all `xs : Els {suc n} As`,
-- which do not hold definitionally and require funExt to prove.
uncurryₙ : Arrows As B → Els As → B
uncurryₙ {zero}  f _  = f
uncurryₙ {suc n} f xs = uncurryₙ (f (headEl xs)) (tailEl xs)
