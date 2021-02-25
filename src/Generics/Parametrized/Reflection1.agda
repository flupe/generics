{-# OPTIONS --safe --without-K #-}

module Generics.Parametrized.Reflection1 where

open import Generics.Prelude hiding (Vec)
open import Generics.Parametrized.Telescope
open import Generics.Parametrized.Desc3
open import Generics.Parametrized.HasDesc
open import Data.Bool.Base

open import Agda.Builtin.Reflection renaming (name to name′)
open import Agda.Builtin.List
open import Agda.Builtin.Nat
import Data.Nat.Induction as Nat
import Data.List.Base as List
import Data.List.Categorical as List
open import Data.Nat.Base
open import Function.Base
open import Data.String using (String)


{- WIP -}
open import Category.Functor
open import Category.Applicative
open import Category.Monad

functor : ∀ {i} → RawFunctor {i} TC
functor = record { _<$>_ = λ f x → bindTC x (returnTC ∘ f) }

applicative : ∀ {i} → RawApplicative {i} TC
applicative = record
  { pure = returnTC
  ; _⊛_  = λ f x → bindTC f λ f → bindTC x (returnTC ∘ f)
  }

monad : ∀ {i} → RawMonad {i} TC
monad = record
  { return = returnTC
  ; _>>=_  = bindTC
  }

open RawMonad {lzero} monad hiding (_⊗_)
open List.TraversableA {lzero} applicative


argVR : Term → Arg Term
argVR = arg (arg-info visible relevant)

module _ (n : ℕ) where
  mkVar : (o k : ℕ) → Term
  mkVar o zero = def (quote proj₂) (argVR (var o []) ∷ [])
  mkVar o (suc k) = def (quote proj₁) (argVR (mkVar o k) ∷ [])

  mutual
    downsize : (o : ℕ) -- offset: number of locally bound variables (i.e not in the outer telescope)
             → Term
             → Term
    downsize o (var k args) =
      let args′ = downsizeArgs o args in
      if k <ᵇ o then var k args′
      else if k ∸ o <ᵇ n
          then def (quote proj₂) (argVR (mkVar o (k ∸ o)) ∷ args′)
          else var (k ∸ pred n) args′
    downsize o (con c args) = con c (downsizeArgs o args)
    downsize o (def f args) = def f (downsizeArgs o args)
    downsize o (lam v (abs n t)) = lam v (abs n (downsize (suc o) t))
    downsize o (pat-lam cs args) = pat-lam cs (downsizeArgs (suc o) args)
    downsize o (pi (arg ia a) (abs na b)) =
      pi (arg ia (downsize o a))
         (abs na (downsize (suc o) b))
    downsize o (agda-sort s) = agda-sort (downsizeSort o s)
    downsize o (lit l)    = lit l
    downsize o (meta x xs) = meta x (downsizeArgs o xs)
    downsize o unknown = unknown

    downsizeSort : ℕ → Sort → Sort
    downsizeSort o (set t) = set (downsize o t)
    downsizeSort o (lit n) = lit n
    downsizeSort o unknown = unknown

    downsizeArgs : ℕ → List (Arg Term) → List (Arg Term)
    downsizeArgs o [] = []
    downsizeArgs o (arg i x ∷ xs) = arg i (downsize o x)
                                  ∷ downsizeArgs o xs

    downsizeTel : ℕ → List (String × Arg Type) → List (String × Arg Type)
    downsizeTel o [] = []
    downsizeTel o ((s , arg i t) ∷ xs) = (s , arg i (downsize o t)) ∷ downsizeTel (suc o) xs

    downsizeClause : ℕ → List Clause → List Clause
    downsizeClause o [] = []
    downsizeClause o (clause tel ps t ∷ xs) =
      clause (downsizeTel o tel) ps (downsize (o + List.length tel) t) ∷ downsizeClause o xs
    downsizeClause o (absurd-clause tel ps ∷ xs) =
      absurd-clause (downsizeTel o tel) ps ∷ downsizeClause o xs


getTelescope : ℕ → Type → TC (Term × Type)
getTelescope n type = quoteωTC {Telescope ⊤} ε >>= aux n type 0
  where
    aux : ℕ     -- expected size of the remaining telescope
        → Type
        → ℕ     -- current size of the telescope
        → Term → TC (Term × Type)
    aux 0 t n T = return (T , t)
    aux (suc k) (pi (arg _ a) (abs _ b)) n P =
      aux k b (suc n) (con (quote _⊢_)
        ( argVR P
        ∷ argVR (lam visible (abs "P" (downsize n 0 a)))
        ∷ []))
    aux _ _ _ _ = typeError (strErr "ill-formed type signature" ∷ [])

dropPis : ℕ → Type → Type
dropPis (suc n) (pi a (abs _ b)) = dropPis n b
dropPis _ t = t

module _ (name : Name) (nP : ℕ) where
  getCon : Type → TC Term
  -- TODO: stop ignoring higher-order inductive arguments for now
  getCon (pi (arg xi a@(def n args)) (abs _ b)) =
    if primQNameEquality name n then (do
      b′ ← getCon b
      return (con (quote _⊗_) ( argVR (con (quote CDesc.var) (argVR (con (quote tt) []) ∷ []))
                              ∷ argVR b′
                              ∷ []))) -- it's an indective argument (first-order)
    else do
      b′ ← getCon b
      return (con (quote π) ( argVR (con (quote refl) [])
                            ∷ argVR (lam visible (abs "PV" a)) -- TODO: lift everything
                            ∷ argVR b′
                            ∷ []))
  -- TODO: things different from def on the left

  getCon (def n args) = -- because we're at the end, it must be the inductive type being defined
    -- TODO: drop n first args, fold over rest
    return (con (quote CDesc.var) (argVR (lam visible (abs "_" (con (quote tt) []))) ∷ []))

  getCon _ = typeError (strErr "ill-formed constructor type signature." ∷ [])


  deriveDesc : List Name → TC Term
  deriveDesc []       = return (con (quote Desc.[]) [])
  deriveDesc (c ∷ cs) =
    con (quote Desc._∷_)
      <$> sequenceA ( (argVR <$> (getType c >>= normalise <&> dropPis nP >>= getCon))
                    ∷ (argVR <$> deriveDesc cs)
                    ∷ [])

macro
  test : Name → Term → TC ⊤
  test name hole = do
    d  ← getDefinition name
    d′ ← quoteTC d
    typeError (termErr d′ ∷ [])

f : (A : Set) (b : A) → ℕ
f A b = zero

macro
  -- getParams : Term → Term → TC ⊤
  -- getParams type hole = normalise type >>= getTelescope >>= unify hole

  deriveHasDesc : Name → Term → TC ⊤
  deriveHasDesc name hole = do
    data-type n cs ← getDefinition name
      where _ → typeError (strErr "Given name is not a datatype." ∷ [])
    type    ← getType name >>= normalise
    (P , b) ← getTelescope n type
    D       ← deriveDesc name n cs
    unify hole D

data Id (A : Set) (x : A) : A → Set where
  refl : Id A x x

data Maybe (A : Set) : Set where
  nothing : Maybe A

data Vec   (A : Set) : ℕ → Set where

