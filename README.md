A library for datatype-generic programming in Agda.
To learn more about the structure of the library, see `README.agda`.

## Goal

The goal of this library is two-fold:

- For regular Agda users, this library provides familiar constructions
  that can derived easily. *Decidable equality*, *Elimination principle*,
  *Case analysis* and more are available as ready-to-use constructions for any
  user-defined Agda datatype[^1].

- From the perspective of developers, this library uses an internal encoding
  that makes it fairly easy to define new datatype-generic constructions.
  Those constructions can be defined using regular Agda code, without having
  to rely on reflection in any way.

[^1]: Not actually *any* datatype. We support inductive parametrized and indexed
  datatypes, whose constructors may hold both relevant and irrelevant values.
  We however do not handle neither mutually-recursive definitions nor coinductive
  datatypes. Universe-polymorphism sorta works, provided levels are the first
  parameters of the datatype.

## How to use

To get started with deriving constructions for a given datatype,
just import the library:

```agda
open import Generics
```

Then, derive a first-class *encoding* of the datatype at hand:

```agda
data List (A : Set) : Set where
  nil  : List A
  cons : A → List A → List A

listD : HasDesc List
listD = deriveDesc List
```

That's all that is required to use the generic constructions provided by the library!

```agda
import Generics.Constructions.Fold

fold : {A B : Set} → B → (A → B → B) → List A → B
fold = deriveFold listD

sum : List Nat → Nat
sum = fold 0 _+_

decEq : {A : Set} → {{ DecEq A }} → DecEq (List A)
decEq = deriveDecEq listD

show : {A : Set} → {{ Show A }} → Show (List A)
show = deriveShow listD
```

The library satisfies the two important requirements:

- It can be used within Agda's `--safe` flag.

- Datatype-generic constructions are implemented such that they reduce on open
  terms. This is crucial to make our constructions practical when proving
  properties about abstract values.

  For example, the elimination principle derived for `Nat` will reduce properly.

  ```agda
  data Nat : Set where
    Z : Nat
    S : Nat → Nat

  natD : HasDesc Nat
  natD = deriveDesc Nat

  elimNat : (P : Nat → Set) → P Z → (∀ {n} → P n → P (S n))
          → ∀ n → P n
  elimNat = deriveElim natD

  elimZ : ∀ P PZ PS   → elimNat P PZ PS Z     ≡ PZ
  elimZ = refl

  elimS : ∀ P PZ PS n → elimNat P PZ PS (S n) ≡ PS (elimNat P PZ PS n)
  elimS = refl
  ```

## Related


- Effectfully's [`Generic` library](https://github.com/effectfully/generic)
  - [Descriptions, Computational vs Propositional](http://effectfully.blogspot.com/2016/04/descriptions.html)
  - [Deriving Eliminators of Described Datatypes](http://effectfully.blogspot.com/2016/06/deriving-eliminators-of-described-data.html)
- McBride and Dagand's work on universes of datatype descriptions.
- Yorick Sijsling's [master thesis](https://github.com/yoricksijsling/ornaments-thesis)
  about generic programming and ornaments.
- Larry Diehl's [`generic-elim` library](https://github.com/larrytheliquid/generic-elim)

