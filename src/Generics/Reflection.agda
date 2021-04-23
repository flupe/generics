module Generics.Reflection where

open import Generics.Prelude
open import Generics.Telescope
open import Generics.Desc
open import Generics.HasDesc
open import Data.Bool.Base

open import Agda.Builtin.Reflection renaming (name to name′)
open import Agda.Builtin.List
open import Agda.Builtin.Nat
import Data.Nat.Induction as Nat
import Data.List.Base as List
open import Data.List.Base using ([_])
import Data.List.Categorical as List
open import Data.Nat.Base
open import Function.Base
open import Data.String using (String)

open import Category.Functor
open import Category.Applicative
open import Category.Monad


{- WIP -}

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

pattern VRA x = arg (arg-info visible relevant) x
pattern HRA x = arg (arg-info hidden relevant) x

strerror : ∀ {A : Set} → String → TC A
strerror = typeError ∘ [_] ∘ strErr

ε′ : List (Arg Term) → Term
ε′ = con (quote Telescope.ε)

_⊢′<_>_ : Term → Relevance → Term → Term
T ⊢′< r > f = con (quote _⊢<_>_) (VRA T ∷ VRA (quoteTerm r) ∷ VRA f ∷ [])

{-



mkVar′ : (o k : ℕ) → Name → Term
mkVar′ o zero    t = def t (VRA (var 0 []) ∷ [])
mkVar′ o (suc k) t = def (quote proj₁) (VRA (mkVar′ o k t) ∷ [])

mkVar : (o k : ℕ) → Name → List (Arg Term) → Term
mkVar o k t args = def (quote proj₂) (VRA (mkVar′ o k t) ∷ args)

mapArg : {A : Set} → (A → A) → Arg A → Arg A
mapArg f (arg i x) = arg i (f x)

mapArgM : {A : Set} → (A → TC A) → Arg A → TC (Arg A)
mapArgM f (arg i x) = arg i <$> f x

mapAbs : {A : Set} → (A → A) → Abs A → Abs A
mapAbs f (abs n x) = abs n (f x)

mapAbsM : {A : Set} → (A → TC A) → Abs A → TC (Abs A)
mapAbsM f (abs n x) = abs n <$> f x

mapSortM : (Term → TC Term) → Sort → TC Sort
mapSortM f (set t) = set <$> f t
mapSortM f (lit n) = return (lit n)
mapSortM f unknown = return unknown

module _ (nP nI : ℕ) where

  mutual
    downsize : (o : ℕ) -- offset: number of locally bound variables (i.e not in the outer telescope)
             → Term
             → Term
    downsize o (var k args) =
      let args′ = downsizeArgs o args in
           if k <ᵇ o           then var k args′
      else if k ∸ o <ᵇ nI      then mkVar o (k ∸ o     ) (quote proj₂) args′
      else if k ∸ o <ᵇ nI + nP then mkVar o (k ∸ o ∸ nI) (quote proj₁) args′
      else                          var (k ∸ pred (nP + nI)) args′

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

    downsizeTel : ℕ → List (String × Arg Type) → List (String × Arg Type)
    downsizeTel o [] = []
    downsizeTel o ((s , arg i t) ∷ xs) = (s , arg i (downsize o t)) ∷ downsizeTel (suc o) xs

    downsizeClause : ℕ → List Clause → List Clause
    downsizeClause o [] = []
    downsizeClause o (clause tel ps t ∷ xs) =
      clause (downsizeTel o tel) ps (downsize (o + List.length tel) t) ∷ downsizeClause o xs
    downsizeClause o (absurd-clause tel ps ∷ xs) =
      absurd-clause (downsizeTel o tel) ps ∷ downsizeClause o xs

-- TODO: get rid of this terminating flag
{-# TERMINATING #-}
down : ℕ → Term → TC Term
down o (var k args) =
       if k <ᵇ o then return (var k args) -- locally bound, do nothing
  else if k ≡ᵇ o then typeError (strErr "var 0 shouldn't be used inside term" ∷ [])
  else return (var (pred k) args) -- lower everything else
down o (con c args) = con c <$> mapA (mapArgM (down o)) args
down o (def f args) = def f <$> mapA (mapArgM (down o)) args
down o (lam v t) = lam v <$> mapAbsM (down (suc o)) t
down o (pat-lam cs args) = {!!}
down o (pi a b) = do
  a′ ← mapArgM (down o) a
  b′ ← mapAbsM (down (suc o)) b
  return (pi a b)
down o (agda-sort s) = agda-sort <$> mapSortM (down o) s
down o (lit l) = return (lit l)
down o (meta x args) = meta x <$> mapA (mapArgM (down o)) args
down o unknown = return unknown


------------------------------
-- STEP 1: DERIVING TELESCOPES
------------------------------

sortToLevel : Sort → Term
sortToLevel (set t) = t
sortToLevel (lit zero)    = def (quote lzero) []
sortToLevel (lit (suc n)) = def (quote lsuc) (VRA (sortToLevel (lit n)) ∷ []) 
sortToLevel unknown = unknown

module _ (nP : ℕ) where

  getIndexTel : Term → Type → TC (Term × Type)
  getIndexTel P type = aux type 0 ε″
    where
      ε″ : Term
      ε″ = ε′ $ HRA unknown -- level
              ∷ HRA (def (quote tel) (VRA P ∷ VRA (con (quote tt) []) ∷ []))
              ∷ []

      aux : Type → ℕ → Term → TC (Term × Term)
      aux t@(agda-sort s) n T = return (T , sortToLevel s)
      aux (pi (arg _ a) (abs _ b)) n T =
        aux b (suc n) (T ⊢′ lam visible (abs "PI" (downsize nP n 0 a)))
      aux _ _ _ = typeError (strErr "ill-formed type signature when deriving index telescope." ∷ [])
  
  getTelescope : Type → TC (Term × Term × Term)
  getTelescope type = aux nP type 0 (ε′ (HRA unknown ∷ HRA (def (quote ⊤) []) ∷ []))
    where
      aux : (rem : ℕ   )
          → (typ : Type)
          → (siz : ℕ   )
          → (tel : Term)
          → TC (Term × Term × Type)
      aux 0 typ n P = (P ,_) <$> getIndexTel P typ
      aux (suc k) (pi (arg _ a) (abs _ b)) n P =
        aux k b (suc n) (P ⊢′ lam visible (abs "P" (downsize 0 n 0 a)))
      aux _ _ _ _ = typeError (strErr "ill-formed type signature when deriving parameter telescope" ∷ [])

dropPis : ℕ → Type → Type
dropPis (suc n) (pi a (abs _ b)) = dropPis n b
dropPis _ t = t

-------------------------------
-- STEP 3: DERIVING DESCRIPTION
-------------------------------

data Chunks : Set where
  Cκ   : Chunks
  Cπ   : Chunks → Chunks
  _C⊗_ : Chunks → Chunks → Chunks

module _ (name : Name) (nP : ℕ) where
  toIndex : ℕ → List (Arg Term) → Term
  toIndex nV xs =
    lam visible (abs "PV" (List.foldl cons (quoteTerm tt) (List.drop nP xs)) )
    where cons : Term → Arg Term → Term
          cons x (arg _ y) = con (quote _,_) ( VRA x
                                             ∷ VRA (downsize nP nV 0 y)
                                             ∷ [])

  {-# TERMINATING #-}
  getCon : ℕ → Type → TC (Term × Chunks)
  -- TODO: stop ignoring higher-order inductive arguments for now
  getCon nV (pi (arg xi a@(def n args)) (abs _ b)) =
    if primQNameEquality name n then (do
      (b′ , C) ← down 0 b >>= getCon nV
      return $ con (quote _⊗_) ( VRA (con (quote CDesc.var) (VRA (toIndex nV args) ∷ []))
                              ∷ VRA b′
                              ∷ [])
             , Cκ C⊗ C)
    else do
      (b′ , C) ← getCon (suc nV) b
      return $ con (quote π) ( VRA (con (quote refl) [])
                            ∷ VRA (lam visible (abs "PV" (downsize nP nV 0 a)))
                            ∷ VRA b′
                            ∷ [])
             , Cπ C

  -- TODO: we assume it isn't an inductive argument
  getCon nV (pi (arg xi a) (abs _ b)) = do
    (b′ , C) ← getCon (suc nV) b
    return $ con (quote π) ( VRA (con (quote refl) [])
                           ∷ VRA (lam visible (abs "PV" (downsize nP nV 0 a)))
                           ∷ VRA b′
                           ∷ [])
           , Cπ C

  getCon nV (def n args) = return (con (quote CDesc.var) (VRA (toIndex nV args) ∷ []) , Cκ)
  getCon _ _ = typeError (strErr "ill-formed constructor type signature." ∷ [])

  deriveDesc : List Name → TC (Term × List (Name × Chunks))
  deriveDesc []       = return (con (quote Desc.[]) [] , [])
  deriveDesc (c ∷ cs) = do
    (C  , chk ) ← getType c >>= normalise <&> dropPis nP >>= getCon 0
    (CS , chks) ← deriveDesc cs
    return $ con (quote Desc._∷_) (VRA C ∷ VRA CS ∷ []) , (c , chk) ∷ chks
    --  <$> sequenceA ( (VRA <$> (getType c >>= normalise <&> dropPis nP >>= getCon 0))
    --                ∷ (VRA <$> deriveDesc cs)
    --                ∷ [])

-- temporary record until we derive everything
-- acts as a safety net/checkpoint

record Data {P : Telescope ⊤} {I : ExTele P} {ℓ} (A : Curried′ P I ℓ) : Setω where
  constructor mkData

  A′ : Σ[ P ⇒ I ] → Set ℓ
  A′ = uncurry′ P I A

  field
    {n}    : ℕ
    D      : Desc P I ℓ n
    names  : Vec String n

    -- to     : {pi : Σ[ P ⇒ I ]} → A′ pi → μ D pi
    -- from   : {pi : Σ[ P ⇒ I ]} → μ D pi → A′ pi
    -- constr : {pi : Σ[ P ⇒ I ]} → ⟦ D ⟧ ℓ A′ pi → A′ pi
    -- split  : {pi : Σ[ P ⇒ I ]} → A′ pi → ⟦ D ⟧ ℓ A′ pi

    -- from∘to : (pi : Σ[ P ⇒ I ]) (x : A′ pi) → from pi (to pi x) ≡ x

    -- constr-coh  : ∀ pi (x : ⟦ D ⟧ _ (μ D) pi) → constr (mapD _ _ from D x) ≡ from ⟨ x ⟩
    -- split-coh   : ∀ pi (x : ⟦ D ⟧ _ (μ D) pi) → split (from ⟨ x ⟩) ≡ mapD _ _ from D x

open Data


toNames : (xs : List Name) → TC Term
toNames [] = return (con (quote Vec.[]) [])
toNames (x ∷ xs) = do
  x′  ← quoteTC (primShowQName x) >>= normalise
  xs′ ← toNames xs
  return $ con (quote Vec._∷_) (VRA x′ ∷ VRA xs′ ∷ [])

-------------------------------
-- STEP 3: DERIVING CONVERSIONS
-------------------------------

module _ (nP : ℕ) (to′ : Name) where

  deriveTo  : List (Name × Chunks) → TC (List Clause)
  deriveTo′ : Term → List (Name × Chunks) → TC (List Clause)
  -- no constructors, absurd clause
  deriveTo [] = return [ absurd-clause [ "x" , VRA unknown ] (HRA (dot unknown) ∷ VRA (absurd 0) ∷ []) ]
  deriveTo cs = deriveTo′ (con (quote Fin.zero) []) cs

  deriveClause : ℕ → Chunks → List (String × Arg Type) × List (Arg Pattern) × Term
  deriveClause o Cκ        = [] , [] , con (quote lift) (VRA (con (quote refl) []) ∷ [])
  deriveClause o (Cπ C)    =
    let (tel , pat , t) = deriveClause (suc o) C
    in ("x" , VRA unknown) ∷ tel
           , VRA (var o) ∷ pat
           , con (quote _,_) (VRA (var o []) ∷ VRA t ∷ [])
  deriveClause o (Cκ C⊗ C) =
    let (tel , pat , t) = deriveClause (suc o) C
    in ("x" , VRA unknown) ∷ tel
     , VRA (var o) ∷ pat
     , con (quote _,_) (VRA (def to′ (VRA unknown ∷ VRA (var o []) ∷ [])) ∷ VRA t ∷ [])
  deriveClause o (_ C⊗ B) = {!!} , {!!}

  deriveTo′ k ((c , C) ∷ CS) = do
    let (tel , pat , t) = deriveClause (suc 0) C
    CS′ ← deriveTo′ (con (quote Fin.suc) (VRA k ∷ [])) CS
    return $ clause (("pi" , HRA unknown) ∷ tel)
                    (HRA (var 0) ∷ VRA (con c pat) ∷ [])
                    (con (quote ⟨_⟩) (VRA (con (quote _,_) (VRA k ∷ VRA t ∷ [])) ∷ []))
           ∷ CS′
  deriveTo′ _ [] = return []

module _ (nP : ℕ) (from′ : Name) where

  deriveFrom  : List (Name × Chunks) → TC (List Clause)
  deriveFrom′ : Pattern → List (Name × Chunks) → TC (List Clause)
  -- no constructors, absurd clause
  deriveFrom [] = return [ absurd-clause [ "x" , VRA unknown ] (VRA (dot unknown) ∷ VRA (con (quote ⟨_⟩) (VRA (absurd 0) ∷ [])) ∷ []) ]
  deriveFrom cs = deriveFrom′ (con (quote Fin.zero) []) cs

  deriveFClause : ℕ → Chunks → List (String × Arg Type) × Pattern × List (Arg Term)
  deriveFClause o Cκ        = [] , con (quote lift) (VRA (con (quote refl) []) ∷ []) , []
  deriveFClause o (Cπ C)    =
    let (tel , pat , t) = deriveFClause (suc o) C
    in ("x" , VRA unknown) ∷ tel
           , con (quote _,_) (VRA (var o) ∷ VRA pat ∷ [])
           , VRA (var o []) ∷ t
  deriveFClause o (Cκ C⊗ C) =
    let (tel , pat , t) = deriveFClause (suc o) C
    in ("x" , VRA unknown) ∷ tel
     , con (quote _,_) (VRA (var o) ∷ VRA pat ∷ [])
     , VRA (def from′ (VRA unknown ∷ VRA (var o []) ∷ [])) ∷ t
  deriveFClause o (_ C⊗ B) = {!!} , {!!}

  deriveFrom′ k ((c , C) ∷ CS) = do
    let (tel , pat , t) = deriveFClause (suc 0) C
    CS′ ← deriveFrom′ (con (quote Fin.suc) (VRA k ∷ [])) CS
    return $ clause (("pi" , VRA unknown) ∷ tel)
                    (VRA (var 0) ∷ VRA (con (quote ⟨_⟩) (VRA (con (quote _,_) (VRA k ∷ VRA pat ∷ [])) ∷ [])) ∷ [])
                    (con c t)
           ∷ CS′
  deriveFrom′ _ [] = return []

module _ (nP : ℕ) (from′ : Name) where

  deriveConstr  : List (Name × Chunks) → TC (List Clause)
  deriveConstr′ : Pattern → List (Name × Chunks) → TC (List Clause)
  -- no constructors, absurd clause
  deriveConstr [] = return [ absurd-clause [ "x" , VRA unknown ] (HRA (dot unknown) ∷ VRA (con (quote ⟨_⟩) (VRA (absurd 0) ∷ [])) ∷ []) ]
  deriveConstr cs = deriveConstr′ (con (quote Fin.zero) []) cs

  deriveCClause : ℕ → Chunks → List (String × Arg Type) × Pattern × List (Arg Term)
  deriveCClause o Cκ        = [] , con (quote lift) (VRA (con (quote refl) []) ∷ []) , []
  deriveCClause o (Cπ C)    =
    let (tel , pat , t) = deriveCClause (suc o) C
    in ("x" , VRA unknown) ∷ tel
           , con (quote _,_) (VRA (var o) ∷ VRA pat ∷ [])
           , VRA (var o []) ∷ t
  deriveCClause o (Cκ C⊗ C) =
    let (tel , pat , t) = deriveCClause (suc o) C
    in ("x" , VRA unknown) ∷ tel
     , con (quote _,_) (VRA (var o) ∷ VRA pat ∷ [])
     , VRA (var o []) ∷ t
  deriveCClause o (_ C⊗ B) = {!!} , {!!}

  deriveConstr′ k ((c , C) ∷ CS) = do
    let (tel , pat , t) = deriveCClause (suc 0) C
    CS′ ← deriveConstr′ (con (quote Fin.suc) (VRA k ∷ [])) CS
    return $ clause (("pi" , HRA unknown) ∷ tel)
                    (HRA (var 0) ∷ VRA (con (quote _,_) (VRA k ∷ VRA pat ∷ [])) ∷ [])
                    (con c t)
           ∷ CS′
  deriveConstr′ _ [] = return []


module _ (nP : ℕ) (from∘to′ : Name) where
  deriveFromTo : List (Name × Chunks) → TC (List Clause)
  deriveFromTo′ : List (Name × Chunks) → TC (List Clause)

  deriveFromTo [] = return [ absurd-clause [ "x" , VRA unknown ] (VRA (dot unknown) ∷ VRA (absurd 0) ∷ []) ]
  deriveFromTo cs = deriveFromTo′ cs

  deriveFTClause : ℕ → Chunks → List (String × Arg Type) × List (Arg Pattern) × List (Arg Term)
  deriveFTClause o Cκ        = [] , [] , []
  deriveFTClause o (Cπ C)    =
    let (tel , pat , t) = deriveFTClause (suc o) C
    in ("x" , VRA unknown) ∷ tel , VRA (var o) ∷ pat , t
  deriveFTClause o (Cκ C⊗ C) =
    let (tel , pat , t) = deriveFTClause (suc o) C
    in ("x" , VRA unknown) ∷ tel , VRA (var o) ∷ pat
       , (VRA (def from∘to′ (VRA unknown ∷ VRA (var o []) ∷ [])) ∷ [])
  deriveFTClause o (_ C⊗ B) = {!!} , {!!}

  deriveFromTo′ ((c , C) ∷ CS) = do
    let (tel , pat , t) = deriveFTClause (suc 0) C
    CS′  ← deriveFromTo′ CS
    aux′ ← freshName "aux"

    declareDef (VRA aux′) unknown
    defineFun aux′
      [ clause (("pi" , VRA unknown) ∷ [])
               (VRA (var 0) ∷ List.map (const (VRA (con (quote refl) []))) t)
               (con (quote refl) [])
      ]

    return $ clause (("pi" , VRA unknown) ∷ tel)
                    (VRA (var 0) ∷ VRA (con c pat) ∷ [])
                    (def aux′ (VRA unknown ∷ t))
           ∷ CS′
  deriveFromTo′ [] = return []

module _ (nP : ℕ) (to′ : Name) where

  deriveSplit  : List (Name × Chunks) → TC (List Clause)
  deriveSplit′ : Term → List (Name × Chunks) → TC (List Clause)
  -- no constructors, absurd clause
  deriveSplit [] = return [ absurd-clause [ "x" , VRA unknown ] (HRA (dot unknown) ∷ VRA (absurd 0) ∷ []) ]
  deriveSplit cs = deriveSplit′ (con (quote Fin.zero) []) cs

  deriveSClause : ℕ → Chunks → List (String × Arg Type) × List (Arg Pattern) × Term
  deriveSClause o Cκ        = [] , [] , con (quote lift) (VRA (con (quote refl) []) ∷ [])
  deriveSClause o (Cπ C)    =
    let (tel , pat , t) = deriveSClause (suc o) C
    in ("x" , VRA unknown) ∷ tel
           , VRA (var o) ∷ pat
           , con (quote _,_) (VRA (var o []) ∷ VRA t ∷ [])
  deriveSClause o (Cκ C⊗ C) =
    let (tel , pat , t) = deriveSClause (suc o) C
    in ("x" , VRA unknown) ∷ tel
     , VRA (var o) ∷ pat
     , con (quote _,_) (VRA (var o []) ∷ VRA t ∷ [])
  deriveSClause o (_ C⊗ B) = {!!} , {!!}

  deriveSplit′ k ((c , C) ∷ CS) = do
    let (tel , pat , t) = deriveSClause (suc 0) C
    CS′ ← deriveSplit′ (con (quote Fin.suc) (VRA k ∷ [])) CS
    return $ clause (("pi" , HRA unknown) ∷ tel) (HRA (var 0) ∷ VRA (con c pat) ∷ []) (con (quote _,_) (VRA k ∷ VRA t ∷ []))
           ∷ CS′
  deriveSplit′ _ [] = return []

---------------------
-- WRAPPING UP: MACRO
---------------------

macro
  deriveHasDesc : Name → Term → TC ⊤
  deriveHasDesc name hole = do
    data-type nP cs ← getDefinition name
      where _ → typeError (strErr "Given name is not a datatype." ∷ [])
    let n       = List.length cs
    names       ← toNames cs
    type        ← getType name >>= normalise
    (P , I , s) ← getTelescope nP type
    (D , chks)  ← deriveDesc name nP cs

    -- refining type by hand to solve implicits
    D′          ← checkType D (def (quote Desc) (VRA P ∷ VRA I ∷ VRA s ∷ VRA (lit (nat n)) ∷ []))

    to′     ← freshName "to"
    from′   ← freshName "from"
    constr′ ← freshName "constr"
    split′  ← freshName "split"

    -- from∘to′ ← freshName "from∘to"

    -- declareDef (VRA to′)
    --   $ pi (HRA (def (quote Σ[_⇒_]) (VRA P ∷ VRA I ∷ []))) $ abs "pi"
    --     $ pi (VRA (def (quote uncurry′) (VRA P ∷ VRA I ∷ VRA (def name []) ∷ VRA (var 0 []) ∷ [])))
    --       $ abs "x" $ def (quote μ) (VRA D′ ∷ VRA (var 1 []) ∷ [])

    declareDef (VRA from′) unknown
      -- $ pi (HRA (def (quote Σ[_⇒_]) (VRA P ∷ VRA I ∷ []))) $ abs "pi"
      --   $ pi (VRA (def (quote μ) (VRA D′ ∷ VRA (var 0 []) ∷ [])))
      --     $ abs "x" (def (quote uncurry′) (VRA P ∷ VRA I ∷ VRA (def name []) ∷ VRA (var 1 []) ∷ []))

    -- declareDef (VRA constr′)
    --   $ pi (HRA (def (quote Σ[_⇒_]) (VRA P ∷ VRA I ∷ []))) $ abs "pi"
    --     $ pi (VRA (def (quote ⟦_⟧) (VRA D ∷ VRA unknown ∷ VRA (def (quote uncurry′) (VRA P ∷ VRA I ∷ VRA (def name []) ∷ [])) ∷ VRA (var 0 []) ∷ [])))
    --       $ abs "x" unknown

    -- declareDef (VRA split′)
    --   $ pi (HRA (def (quote Σ[_⇒_]) (VRA P ∷ VRA I ∷ []))) $ abs "pi"
    --     $ pi (VRA (def (quote uncurry′) (VRA P ∷ VRA I ∷ VRA (def name []) ∷ VRA (var 0 []) ∷ [])))
    --       $ abs "x" unknown

    -- declareDef (VRA from∘to′) unknown

    -- deriveTo     nP to′     chks >>= defineFun to′
    deriveFrom nP from′ chks >>= defineFun from′
    -- deriveConstr nP constr′ chks >>= defineFun constr′
    -- deriveSplit  nP split′  chks >>= defineFun split′

    -- deriveFromTo nP from∘to′ chks  >>= defineFun from∘to′

    -- typeError (strErr (primShowQName to′) ∷ [])

    unify hole (con (quote mkData)
      ( HRA P
      ∷ HRA I
      ∷ HRA s
      ∷ VRA D′
      ∷ VRA names

      -- ∷ VRA (lam hidden (abs "pi" (def to′ (HRA (var 0 []) ∷ []))))
      ∷ VRA (lam hidden (abs "pi" (def from′ (HRA (var 0 []) ∷ []))))
      -- ∷ VRA (def constr′ [])
      -- ∷ VRA (def split′  []) -- VRA (def split′  [])
      -- TODO: maybe add eta-expension manually  lam (...) []

      -- ∷ VRA (def from∘to′  [])
      ∷ []))

macro
  debug : Name → Term → TC ⊤
  debug n h = do
    d  ← getDefinition n
    e′ ← quoteTC d
    typeError (termErr e′ ∷ [])

--------
-- TESTS
--------
      
data BB : Set where
  tt ff : BB

data L (A : Set) : Set where
  nil  : L A
  cons : A → L A → L A

data Id (A : Set) (x : A) : A → Set where
  refl : Id A x x

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

data V (A : Set) : ℕ → Set where
  nil  : V A 0
  cons : ∀ n → A → V A n → V A (suc n)

data F : Set where

-- TODO: fix absurd clause for empty type in from
-- absurd comes from Fin, not something else

-- {-
DD : Data L
DD = deriveHasDesc L
-- -}

-- {-# TERMINATING #-}
-- 
-- DD : Desc (ε ⊢ const Set) ε lzero 2
-- DD = var (const tt) ∷ π refl (proj₂ ∘ proj₁) ((var (const tt)) ⊗ (var (const tt))) ∷ []
-- 
-- from′ : ∀ {pi} → μ DD pi → uncurry′ _ _ L pi
-- from′ ⟨ zero , lift refl ⟩ = nil
-- from′ ⟨ suc zero , x , xs , lift refl ⟩ = cons x (from′ xs)
-- 
-- DD2 : Data {P = ε ⊢ const Set} {I = ε} L
-- DD2 = mkData DD ("nil" ∷ "cons" ∷ []) from′

data Tree : Set where
  leaf : Tree
  node : Tree → Tree → Tree

-- treeD : Desc ε ε lzero 2
-- treeD = var (const tt)
--       ∷ var (const tt) ⊗ (var (const tt) ⊗ var (const tt))
--       ∷ []
-- 
-- tto : Tree → μ treeD (tt , tt)
-- tto leaf = ⟨ zero , lift refl ⟩
-- tto (node a b) = ⟨ suc zero , tto a , tto b , lift refl ⟩
-- 
-- ffrom : μ treeD (tt , tt) → Tree
-- ffrom ⟨ zero , lift refl ⟩ = leaf
-- ffrom ⟨ suc zero , a , b , lift refl ⟩ = node (ffrom a) (ffrom b)
-- 
-- ffrom∘to : ∀ x → ffrom (tto x) ≡ x
-- ffrom∘to leaf = refl
-- ffrom∘to (node a b) rewrite ffrom∘to a | ffrom∘to b = refl

-}
