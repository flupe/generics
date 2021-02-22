{-# OPTIONS --safe --without-K #-}

module Generics.Parametrized.Reflection1 where

open import Generics.Prelude hiding (Vec)
open import Generics.Parametrized.Telescope
open import Generics.Parametrized.Desc3
open import Generics.Parametrized.HasDesc
open import Data.Bool.Base

open import Agda.Builtin.Reflection
open import Agda.Builtin.List
open import Agda.Builtin.Nat
import Data.Nat.Induction as Nat
import Data.List.Base as List
open import Data.Nat.Base
open import Function.Base

infixl 7 _>>=_

_>>=_ = bindTC
_>>_ : ∀ {i} {A B : Set i} → TC A → TC B → TC B
_>>_ x y = x >>= (const y)
return = returnTC

_<$>_ : ∀ {i} {A B : Set i} → (A → B) → TC A → TC B
f <$> x = x >>= (return ∘ f)

argVR : Term → Arg Term
argVR = arg (arg-info visible relevant)

module _ (n : ℕ) where
  mkVar : (o k : ℕ) → Term
  mkVar o zero = def (quote proj₂) (argVR (var o []) ∷ [])
  mkVar o (suc k) = def (quote proj₁) (argVR (mkVar o k) ∷ [])

  mutual
    downsize : (o : ℕ) → Term → Term
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
    downsize o (lit l) = lit l
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


getTelescope : Type → TC Term
getTelescope typ = quoteωTC {Telescope ⊤} ε >>= aux typ 0
  where
    -- n: size of aux telescope i.e size of bound variables
    -- we need to rewrite every var k (k < n) to projᵢ ( ... projⱼ (var 0))
    -- and downsize bigger occurences

    aux : Type → ℕ → Term → TC Term
    aux (agda-sort s) n P = return P -- for now, ignore last element and return telescope
                                     -- later: return sort level?
    aux (pi (arg _ a) (abs _ b)) n P =
      aux b (suc n) (con (quote _⊢_)
        ( argVR P
        ∷ argVR (lam visible (abs "P" (downsize n 0 a)))
                -- TODO: choose better arg name
        ∷ []))
    aux _ n P = typeError (strErr "ill-formed type signature" ∷ [])

macro
  getParams : Term → Term → TC ⊤
  getParams typ hole = normalise typ >>= getTelescope >>= unify hole
