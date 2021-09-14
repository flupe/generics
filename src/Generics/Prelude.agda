{-# OPTIONS --safe --without-K #-}
module Generics.Prelude where

open import Function.Base     public
open import Data.Product      public hiding (map; uncurry; uncurry′)
open import Level             public using (Setω; Level; _⊔_; Lift; lift)
                                     renaming (zero to lzero; suc to lsuc)

open import Relation.Binary.PropositionalEquality public
  hiding ([_]; Extensionality; ∀-extensionality)
open import Data.Nat.Base        public using (ℕ; zero; suc; _+_)
                                        renaming (_∸_ to _-_)
open import Data.Unit            public using (⊤; tt)
open import Data.List            public using (List; []; _∷_)
open import Data.Vec.Base        public using (Vec; []; _∷_; map; lookup)
open import Data.Fin.Base as Fin public using (Fin; zero; suc)
open import Axiom.Extensionality.Propositional public


open import Reflection                      public
  hiding (var; return; _>>=_; _>>_; assocˡ; assocʳ; visibility; relevance; module Arg)
import Reflection.Argument
module Arg = Reflection.Argument
open import Reflection.Argument.Information public using (ArgInfo; arg-info; visibility)
                                                   renaming (modality to getModality)
open import Reflection.Argument.Modality    public using (Modality; modality)
open import Reflection.Argument.Relevance   public using (Relevance; relevant; irrelevant)
open import Reflection.Argument.Visibility  public using (Visibility; visible; hidden; instance′)

private variable
  m n   : ℕ
  k     : Fin n
  l l'  : Level
  A B   : Set l

record Irr (A : Set l) : Set l where
  constructor irrv
  field
    .unirr : A
open Irr public

<_>_ : Relevance → Set l → Set l
< relevant   > A = A
< irrelevant > A = Irr A

relevance : ArgInfo → Relevance
relevance = Reflection.Argument.Modality.relevance ∘ getModality

-- TODO: deal with quantities
Π<_> : (i : ArgInfo) (A : Set l) → (< relevance i > A → Set l') → Set (l ⊔ l')
Π< arg-info visible   (modality relevant q)   > A B = (x : A) → B x
Π< arg-info visible   (modality irrelevant q) > A B = .(x : A) → B (irrv x)
Π< arg-info hidden    (modality relevant q)   > A B = {x : A} → B x
Π< arg-info hidden    (modality irrelevant q) > A B = .{x : A} → B (irrv x)
Π< arg-info instance′ (modality relevant q)   > A B = {{x : A}} → B x
Π< arg-info instance′ (modality irrelevant q) > A B = .{{x : A}} → B (irrv x)

_→<_>_ : Set l → ArgInfo → Set l' → Set (l ⊔ l')
A →< i > B = Π< i > A λ _ → B

fun<_> : (i : ArgInfo) {A : Set l} {B : < relevance i > A → Set l'}
       → (f : (x : < relevance i > A) → B x) → Π< i > A B
fun< arg-info visible   (modality relevant q)   > f x     = f x
fun< arg-info visible   (modality irrelevant q) > f x     = f (irrv x)
fun< arg-info hidden    (modality relevant q)   > f {x}   = f x
fun< arg-info hidden    (modality irrelevant q) > f {x}   = f (irrv x)
fun< arg-info instance′ (modality relevant q)   > f {{x}} = f x
fun< arg-info instance′ (modality irrelevant q) > f {{x}} = f (irrv x)

app<_> : (i : ArgInfo) {A : Set l} {B : < relevance i > A → Set l'}
       → (f : Π< i > A B) → (x : < relevance i > A) → B x
app< arg-info visible   (modality relevant q)   > f x        = f x
app< arg-info visible   (modality irrelevant q) > f (irrv x) = f x
app< arg-info hidden    (modality relevant q)   > f x        = f {x}
app< arg-info hidden    (modality irrelevant q) > f (irrv x) = f {x}
app< arg-info instance′ (modality relevant q)   > f x        = f {{x}}
app< arg-info instance′ (modality irrelevant q) > f (irrv x) = f {{x}}

-- Instead of the definitions from Function.Nary.NonDependent in the
-- standard library, we use a *functional* representation of vectors
-- of levels and types. This makes it much easier to work with
-- operations like lookup and tabulate, at the cost of losing certain
-- eta laws for nil and cons (see the comment for `uncurryₙ` below).

Levels : ℕ → Set
Levels n = Fin n → Level

private variable ls ls' : Levels n

[]l : Levels 0
[]l ()

_∷l_ : Level → Levels n → Levels (suc n)
(l ∷l ls) zero = l
(l ∷l ls) (suc k) = ls k

headl : Levels (suc n) → Level
headl ls = ls zero

taill : Levels (suc n) → Levels n
taill ls = ls ∘ suc

_++l_ : Levels m → Levels n → Levels (m + n)
_++l_ {zero} ls ls' = ls'
_++l_ {suc m} ls ls' zero = headl ls
_++l_ {suc m} ls ls' (suc x) = (taill ls ++l ls') x

⨆ : Levels n → Level
⨆ {zero} ls = lzero
⨆ {suc n} ls = ls zero ⊔ ⨆ (ls ∘ suc)

Sets : (ls : Levels n) → Setω
Sets {n} ls = (k : Fin n) → Set (ls k)

private variable As Bs : Sets ls

[]S : {ls : Levels 0} → Sets ls
[]S ()

_∷S_ : Set (headl ls) → Sets (taill ls) → Sets ls
(A ∷S As) zero    = A
(A ∷S As) (suc k) = As k

headS : Sets ls → Set (headl ls)
headS As = As zero

tailS : Sets ls → Sets (taill ls)
tailS As k = As (suc k)

_++S_ : Sets ls → Sets ls' → Sets (ls ++l ls')
_++S_ {zero}  As Bs = Bs
_++S_ {suc m} As Bs zero = headS As
_++S_ {suc m} As Bs (suc k) = (tailS As ++S Bs) k

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

_++El_ : Els As → Els Bs → Els (As ++S Bs)
_++El_ {zero} xs ys = ys
_++El_ {suc m} xs ys zero = headEl xs
_++El_ {suc m} xs ys (suc k) = (tailEl xs ++El ys) k

++El-proj₁ : Els (As ++S Bs) → Els As
++El-proj₁ xs zero    = xs zero
++El-proj₁ xs (suc k) = ++El-proj₁ (tailEl xs) k

++El-proj₂ : Els (As ++S Bs) → Els Bs
++El-proj₂ {zero}  xs k = xs k
++El-proj₂ {suc m} xs k = ++El-proj₂ (tailEl xs) k

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
