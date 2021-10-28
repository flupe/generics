{-# OPTIONS --safe #-}
module Generics.Reflection where

open import Function.Base
import Data.Unit    as ⊤
import Data.Product as Product
import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat.Base hiding (_⊔_)
open import Data.List.Base   as List hiding (_++_)
import Data.Vec.Base as Vec
open import Data.String as S using (String; _++_)
open import Data.Bool.Base
open import Data.Maybe.Base using (Maybe; just; nothing; maybe)
open import Agda.Builtin.Reflection renaming ( primQNameEquality to _Name≈_
                                             )
open import Reflection.Abstraction using (unAbs)
open import Reflection.Argument    using (_⟨∷⟩_; _⟅∷⟆_)
open import Reflection.Term hiding (Telescope; var)
open import Relation.Nullary using (yes; no)

open import Category.Monad   as Monad

import Data.List.Categorical as List
import Data.Nat.Induction    as Nat
import Data.Char             as C

open import Reflection.TypeChecking.Monad.Instances using (tcMonad)
open import Reflection.Traversal hiding (_,_)

open import Generics.Prelude
open import Generics.Telescope
open import Generics.Desc renaming (_,_ to _,ω_)
import Generics.Accessibility as Accessibility
open import Generics.HasDesc
import Function.Identity.Categorical as Identity

open List.TraversableM ⦃...⦄
open Monad.RawMonad    ⦃...⦄


tErr : Term → TC ⊤
tErr = typeError ∘ [_] ∘ termErr

sErr : String → TC ⊤
sErr = typeError ∘ [_] ∘ strErr

open Actions

-- `liftN n f` maps numbers 0..(n-1) to themselves, and numbers
-- `n + k` to `n + (f k)`
liftN : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
liftN zero    f k       = f k
liftN (suc n) f zero    = zero
liftN (suc n) f (suc k) = suc (liftN n f k)

mapVars : (ℕ → ℕ) → Term → Term
mapVars f = traverseTerm Identity.applicative actions (0 Reflection.Traversal., [])
  where
    actions : Actions Identity.applicative
    actions .onVar  ctx = liftN (ctx .Cxt.len) f
    actions .onMeta _   = id
    actions .onCon  _   = id
    actions .onDef  _   = id

prettyName : Name → String
prettyName f = maybe id "" (List.last (S.wordsBy ('.' C.≟_) (showName f)))

{-
When converting types to telescopes
variables are converted to context lookups:
Given K := [(oₒ : Oₒ) ⋯ (o₁ : O₁)] "forced" arguments (reversed)
      P := [A₁ ⋯ Aₙ] parameters
      I := [B₁ ⋯ Bₘ] indices,

we want to replace a term in context (Γ , O₁ , ⋯ , Oₒ , A₁ , ⋯ , Aₙ , B₁ , ⋯ , Bₘ , C₁ , ⋯ , Cₚ)
into a term in context               (Γ , Σ P I , C₁ , ⋯ , Cₚ)

 A term (var k) should be replaced by:
   - (var k)                                 if k < p

   - (proj₂ (proj₂ (var p)))                 if p         <= k < p + m      (inside I)
     (proj₂ (proj₁ (proj₂ (var p))))         ...
     (proj₂ (proj₁ (proj₁ (proj₂ (var p))))) ...

   - (proj₂ (proj₁ (var p))                  if p + m     <= k < p + m + n  (inside P)
   - (proj₂ (proj₁ (proj₁ (var p)))          ...
   - (proj₂ (proj₁ (proj₁ (proj₁ (var p))))  ...

   - K[k - (n + m + p)]                      if p + m + n <= k < p + m + n + o

   - var (k + 1 - n - m - o)                 if p + m + n + o <= k
-}

-- o: position of (PI : Σ P I) in the context
--    (i.e number of locally bound variables)
mkVar : (o k : ℕ) → Name → List (Arg Term) → Term
mkVar o k t args = def (quote proj₂) (aux o k ⟨∷⟩ args)
  where
    aux : (o k : ℕ) → Term
    aux o zero    = def t (var o [] ⟨∷⟩ [])
    aux o (suc k) = def (quote proj₁) (aux o k ⟨∷⟩ [])

mkPVar : (o k : ℕ) → List (Arg Term) → Term
mkPVar o k = mkVar o k (quote proj₁)

mkIVar : (o k : ℕ) → List (Arg Term) → Term
mkIVar o k = mkVar o k (quote proj₂)

-- TODO: telescopize should account for forced arguments

module _ (fargs : List Term) (nP nI : ℕ) where

    telescopize       : ℕ → Term → Term
    telescopizeSort   : ℕ → Sort → Sort
    telescopizeArgs   : ℕ → List (Arg Term) → List (Arg Term)
    telescopizeTel    : ℕ → List (String × Arg Type) → List (String × Arg Type)
    telescopizeClause : ℕ → List Clause → List Clause

    lookupForced : List Term → ℕ → ℕ → List (Arg Term) → Term
    lookupForced [] n o = var (suc (n + o))
    -- WARN: we ignore args, this should go alright
    --       ALSO, we might/should lift everything up, probably
    lookupForced (x ∷ xs) zero o = const (mapVars (λ n → n + suc o) x)
    lookupForced (x ∷ xs) (suc n) o = lookupForced xs n o

    telescopize o (var k args) =
      let args′ = telescopizeArgs o args in
           if k <ᵇ o           then var k args′
      else if k ∸ o <ᵇ nI      then mkIVar o (k ∸ o     ) args′
      else if k ∸ o <ᵇ nI + nP then mkPVar o (k ∸ o ∸ nI) args′
      else                          lookupForced fargs (k ∸ (nI + nP + o)) o args
  --  else                          var (k ∸ pred (nP + nI)) args′

    telescopize o (con c args) = con c (telescopizeArgs o args)
    telescopize o (def f args) = def f (telescopizeArgs o args)
    telescopize o (lam v (abs s t)) = lam v (abs s (telescopize (suc o) t))
    telescopize o (pat-lam cs args) = pat-lam (telescopizeClause o cs) (telescopizeArgs o args)
    telescopize o (Π[ s ∶ arg i a ] b) = Π[ s ∶ arg i (telescopize o a) ] telescopize (suc o) b
    telescopize o (sort s) = sort (telescopizeSort o s)
    telescopize o (lit l) = lit l
    telescopize o (meta x args) = meta x (telescopizeArgs o args)
    telescopize o unknown = unknown

    telescopizeSort o (set t)  = set  (telescopize o t)
    telescopizeSort o (prop t) = prop (telescopize o t)
    telescopizeSort o x = x

    telescopizeArgs o [] = []
    telescopizeArgs o (arg i x ∷ xs) = arg i (telescopize o x) ∷ telescopizeArgs o xs

    telescopizeTel o [] = []
    telescopizeTel o ((s , arg i t) ∷ xs) = (s , arg i (telescopize o t))
                                          ∷ telescopizeTel (suc o) xs

    telescopizeClause o [] = []
    telescopizeClause o (clause tel ps t ∷ xs)
      -- careful: telescopes bring (length tel) variables in scope
      = clause (telescopizeTel o tel) ps (telescopize (o + length tel) t)
      ∷ telescopizeClause o xs
    telescopizeClause o (absurd-clause tel ps ∷ xs) =
      absurd-clause (telescopizeTel o tel) ps ∷ telescopizeClause o xs

-- sanity check
private
  module TelescopizeTests where
    t : Term
    t = var 4 []

    -- locally bound variable
    t₁ : Term
    t₁ = telescopize [] 0 0 5 t

    t₁-ok : t₁ ≡ var 4 []
    t₁-ok = refl

    -- retrieving var in index telescope, 4 variable locally-bound
    t₂ : Term
    t₂ = telescopize [] 2 1 4 t

    t₂-ok : t₂ ≡ def (quote proj₂) (def (quote proj₂) (var 4 [] ⟨∷⟩ []) ⟨∷⟩ [])
    t₂-ok = refl

    -- retrieving var in parameter telescope, 2 variable locally-bound
    t₃ : Term
    t₃ = telescopize [] 1 2 2 t

    t₃-ok : t₃ ≡ def (quote proj₂) (def (quote proj₁) (var 2 [] ⟨∷⟩ []) ⟨∷⟩ [])
    t₃-ok = refl

    -- retrieving var outside parameter & index telescope
    t₄ : Term
    t₄ = telescopize [] 1 1 2 t

    t₄-ok : t₄ ≡ var 3 []
    t₄-ok = refl

    -- retrieving 4th var in index telescope
    t₅ : Term
    t₅ = telescopize [] 0 5 1 t

    t₅-ok : t₅ ≡ def (quote proj₂)
                   (def (quote proj₁)
                    (def (quote proj₁)
                     (def (quote proj₁) (def (quote proj₂) (var 1 [] ⟨∷⟩ []) ⟨∷⟩ []) ⟨∷⟩
                      [])
                     ⟨∷⟩ [])
                    ⟨∷⟩ [])
    t₅-ok = refl


-----------------------------
-- Deriving telescopes

getIndexTel : List Term → ℕ → Type → TC Term
getIndexTel fargs nP ty = aux ty 0 (con (quote ε) [])
  where aux : Type → ℕ → Term → TC Term
        aux (agda-sort s) n I = return I
        aux (Π[ s ∶ arg i a ] b) n I = do
          i′ ← quoteTC i >>= normalise
          aux b (suc n) (con (quote _⊢<_>_)
              (I ⟨∷⟩ i′
                 ⟨∷⟩ vLam "PI" (telescopize fargs nP n 0 a)
                 ⟨∷⟩ []))
        aux _ _ _ = typeError [ strErr "ill-formed type signature when deriving index telescope" ]

getTels : List Term → ℕ → Type → TC (Term × Term)
getTels fargs nP ty = aux nP ty 0 (quoteTerm (ε {A = ⊤}))
  where aux : ℕ → Type → ℕ → Term → TC (Term × Term)
        aux zero ty _ P = (P ,_) <$> getIndexTel fargs nP ty
        aux (suc nP) (Π[ s ∶ arg i a ] b) n P = do
          i′ ← quoteTC i >>= normalise
          aux nP b (suc n) (con (quote _⊢<_>_)
              (P ⟨∷⟩ i′
                 ⟨∷⟩ vLam "PI" (telescopize fargs 0 n 0 a)
                 ⟨∷⟩ []))
        aux _ _ _ _ = typeError [ strErr "ill-formed type signature when deriving parameter telescope" ]

-----------------------------
-- Deriving descriptions

-- we cannot unquote things in Setω directly
-- so we can't unquote Terms of type Telescope directly
-- instead we produce skeletons to ease code generation
data Skel : Set where
  Cκ   : Skel
  Cπ   : ArgInfo → Skel → Skel
  _C⊗_ : Skel → Skel → Skel

dropPis : ℕ → Type → Type
dropPis (suc n) (pi a (abs _ b)) = dropPis n b
dropPis _ t = t


module _ (fargs : List Term) (dt : Name) (nP : ℕ) where

  toIndex : ℕ → List (Arg Term) → Term
  toIndex nV xs = vLam "PV" $ foldl cons (quoteTerm ⊤.tt) (drop (nP + List.length fargs) xs)
    where cons : Term → Arg Term → Term
          cons x (arg _ y) =
            con (quote Product._,_) ( x
                          ⟨∷⟩ telescopize fargs nP nV 0 y
                          ⟨∷⟩ [])

  getRecDesc : ℕ → Type → TC (Maybe (Term × Skel))
  getRecDesc n (def nm args) = do
    if nm Name≈ dt
      then return (just (con (quote ConDesc.var) (toIndex n args ⟨∷⟩ []) , Cκ))
      else return nothing
  getRecDesc n (Π[ s ∶ arg i a ] b) = do
    getRecDesc (suc n) b >>= λ where
      (just (right , skright)) → do
        i′ ← quoteTC i >>= normalise
        return $ just ( con (quote ConDesc.π) (i′ ⟨∷⟩ vLam "PV" (telescopize fargs nP n 0 a) ⟨∷⟩ right ⟨∷⟩ [])
                      , Cπ i skright
                      )
      nothing  → return nothing
  getRecDesc n ty = return nothing

  getDesc : (ℕ → ℕ) → ℕ → Type → TC (Term × Skel)
  getDesc f n (def nm args) =
    -- we're gonna assume nm == dt
    -- TODO: why does this work???
    --       surely args contain parameters
    return (con (quote ConDesc.var) (toIndex n (List.map (Arg.map (mapVars f)) args) ⟨∷⟩ []) , Cκ)
  getDesc f n (Π[ s ∶ arg i a ] b) =
    getRecDesc n (mapVars f a) >>= λ where
      -- (possibly higher order) inductive argument
      (just (left , skleft)) → do
        -- we cannot depend on inductive argument (for now)
        -- note: inductive arguments are relevant (for now)
        -- /!\ inductive arguments to not bind a variable, so we strengthen the term
        (right , skright) ← getDesc ((_- 1) ∘ f) n b
        return (con (quote ConDesc._⊗_) (left ⟨∷⟩ right ⟨∷⟩ []) , (skleft C⊗ skright))
      -- plain old argument
      nothing → do
        (right , skright) ← getDesc (liftN 1 f) (suc n) b
        i′    ← quoteTC i >>= normalise
        return ( con (quote ConDesc.π) (i′
                                    ⟨∷⟩ vLam "PV" (telescopize fargs nP n 0 a)
                                    ⟨∷⟩ right
                                    ⟨∷⟩ [])
               , Cπ i skright
               )
  getDesc _ _ _ = typeError [ strErr "ill-formed constructor type" ]


-- TODO: the reason we do this is that I've failed to make the PI arguments
--       implicit in the reflection code
record HD {P} {I : ExTele P} {ℓ} (A : Indexed P I ℓ) : Setω where
  constructor mkHD

  A′ : ⟦ P , I ⟧xtel → Set ℓ
  A′ = uncurry P I A

  field
    {n} : ℕ
    D : DataDesc P I n
    names : Vec String n
    constr : ∀ pi → ⟦ D ⟧Data A′ pi → A′ pi
    split  : ∀ pi → A′ pi → ⟦ D ⟧Data A′ pi
    split∘constr : ∀ pi → (x : ⟦ D ⟧Data A′ pi) → split pi (constr pi x) ≡ω x
    constr∘split : ∀ pi → (x : A′ pi          ) → constr pi (split pi x) ≡  x

  open Accessibility A D (λ {pi} → split pi)

  field wf : ∀ pi (x : A′ pi) → Acc x

badconvert : ∀ {P} {I : ExTele P} {ℓ} {A : Indexed P I ℓ}
           → HD {P} {I} {ℓ} A → HasDesc {P} {I} {ℓ} A
badconvert d = record
  { D            = HD.D d
  ; names        = HD.names d
  ; constr       = λ {PI} → HD.constr d PI
  ; split        = λ {PI} → HD.split d PI
  ; split∘constr = λ {PI} → HD.split∘constr d PI
  ; constr∘split = λ {PI} → HD.constr∘split d PI
  ; wf           = λ {PI} → HD.wf d PI
  }


withAI : ArgInfo → Term → Term
withAI i t with relevance i
... | relevant   = t
... | irrelevant = con (quote irrv) [ vArg t ]

patAI : ArgInfo → Pattern → Pattern
patAI i t with relevance i
... | relevant   = t
... | irrelevant = con (quote irrv) [ vArg t ]


deriveThings : (gargs : List (Arg Term)) (nP : ℕ)
               (qconstr qsplit qsplitconstr qconstrsplit qwf : Name)
               (cons : List (Name × Skel))
             → TC ⊤
deriveThings gargs nP qconstr qsplit qsplitconstr qconstrsplit  qwf cons = do
  let clauses = deriveDef cons
  -- TODO: use some n-ary magic
  let (constr_cls      , rest  ) = unzip clauses 
  let (split_cls       , rest  ) = unzip rest
  let (splitconstr_cls , rest  ) = unzip rest
  let (constrsplit_cls , wf_cls) = unzip rest
  defineFun qconstr       constr_cls
  defineFun qsplit        split_cls
  defineFun qsplitconstr  splitconstr_cls
  defineFun qconstrsplit  constrsplit_cls
  defineFun qwf           wf_cls
  where
    deriveIndArg : Skel → ℕ × List (String × Arg Type) × List (Arg Pattern) × List (Arg Term)
    deriveIndArg Cκ = 0 , [] , [] , []
    deriveIndArg (Cπ ia C) =
      let (o , tel , pat , args) = deriveIndArg C
      in suc o
       , ("x" , vArg unknown) ∷ tel
       , arg ia (var o) ∷ pat
       , arg ia (var o []) ∷ args

    -- WARNING: intentionally wrong, never used when deriving descriptions
    deriveIndArg (A C⊗ B) = 0 , [] , [] , []

    deriveCon : Skel → ℕ × List (String × Arg Type) -- variable types
                         × Pattern            -- pattern for ⟦_⟧Data
                         × List (Arg Pattern) -- pattern for arguments of A′ cons
                         × List (Arg Term)    -- arguments for constructor
                         × Term               -- return value for split
                         × Term               -- body of wf
    deriveCon Cκ
      = 0 , [] -- we bind zero vars
      , con (quote Eq.refl) []
      , []
      , []
      , con (quote Eq.refl) []
      , def (quote ttω) []
    deriveCon (Cπ ia C) =
      let (o , vars , datapat , apat , cargs , sval , wfval) = deriveCon C
      in suc o
       , ("s" , arg ia unknown) ∷ vars -- TODO: unsure about ia here
       , con (quote Product._,_) (patAI ia (var o) ⟨∷⟩ datapat ⟨∷⟩ [])
       , arg ia (var o) ∷ apat
       , arg ia (var o []) ∷ cargs
       , con (quote Product._,_) (withAI ia (var o []) ⟨∷⟩ sval ⟨∷⟩ [])
       , wfval
    deriveCon (A C⊗ B) =
      let (ro , rtel , rpat , rargs)  = deriveIndArg A in
      let (o , vars , datapat , apat , cargs , sval , wfval) = deriveCon B
      in suc o
       , ("x" , vArg unknown) ∷ vars -- we only support visible relevant inductive args
       , con (quote Product._,_) (var o ⟨∷⟩ datapat ⟨∷⟩ [])
       , var o ⟨∷⟩ apat
       , var o [] ⟨∷⟩ cargs
       , con (quote Product._,_) (var o [] ⟨∷⟩ sval ⟨∷⟩ [])
       , def (quote _ω,ω_)
             (pat-lam [ clause rtel rpat
                          (def qwf (unknown  -- PI of inductive argument
                                     ⟨∷⟩ var (o + ro) rargs
                                     ⟨∷⟩ []))
                      ] []
             ⟨∷⟩ wfval ⟨∷⟩ []) -- TODOOOO
    deriveClause : Pattern → Term → Name × Skel
                 → Clause × Clause × Clause × Clause × Clause
    deriveClause kp kt (consname , shape) =
      let (o , vars , datapat , apat , cargs , sval , wfval) = deriveCon shape
      in clause (("pi" , vArg unknown) ∷ vars)
                (var o ⟨∷⟩ con (quote _,ω_) (kp ⟨∷⟩ datapat ⟨∷⟩ []) ⟨∷⟩ [])
                (con consname (nP ⋯⟅∷⟆ cargs)) -- TODO: maybe forced args go here
       , clause (("pi" , vArg unknown) ∷ vars)
                (var o ⟨∷⟩ con consname apat ⟨∷⟩ [])
                (con (quote _,ω_) (kt ⟨∷⟩ sval ⟨∷⟩ []))
       , clause (("pi" , vArg unknown) ∷ vars)
                (var o ⟨∷⟩ con (quote _,ω_) (kp ⟨∷⟩ datapat ⟨∷⟩ []) ⟨∷⟩ [])
                (def (quote reflω) [])
       , clause (("pi" , vArg unknown) ∷ vars)
                (var o ⟨∷⟩ con consname apat ⟨∷⟩ [])
                (con (quote Eq.refl) [])
       , clause (("pi" , vArg unknown) ∷ vars)
                (var o ⟨∷⟩ con consname apat ⟨∷⟩ [])
                (con (quote Accessibility.Acc.acc) (wfval ⟨∷⟩ []))

    deriveClauses : Pattern -- pattern for index of constructor
                  → Term    -- term for index constructor
                  → List (Name × Skel)
                  → List (Clause × Clause × Clause × Clause × Clause)
    deriveClauses _ _ [] = []
    deriveClauses kp kt (x ∷ xs)
      = deriveClause kp kt x
      ∷ deriveClauses (con (quote Fin.suc) (kp ⟨∷⟩ []))
                      (con (quote Fin.suc) (kt ⟨∷⟩ []))
                      xs

    deriveDef : List (Name × Skel) → List (Clause × Clause × Clause × Clause × Clause)
    deriveDef [] = [ cls , cls , cls , cls , cls ]
      where cls = absurd-clause (("PI" , hArg unknown) ∷ ("x" , vArg unknown) ∷ [])
                                (var 1 ⟨∷⟩ absurd 0 ⟨∷⟩ [] )
    deriveDef xs = deriveClauses (con (quote Fin.zero) [])
                                 (con (quote Fin.zero) [])
                                 xs

macro
  deriveDesc : Term → Term → TC ⊤
  deriveDesc t hole = do
    -- Arguments are used for enabling universe-polymorphic defintions
    -- these arguments should be prepended to every use of nm as a type
    def nm gargs ← return t
      where _ → typeError [ strErr "Expected name with arguments." ]

    let fargs = reverse (List.map Arg.unArg gargs)

    data-type nP cs ← getDefinition nm
      where _ → typeError [ strErr "Name given is not a datatype." ]

    let nCons = List.length cs
    let nArgs = List.length gargs

    names ← quoteTC (Vec.fromList (List.map prettyName cs))

    -- we get the type of the family, with the provided arguments removed
    ty ← getType nm >>= normalise <&> dropPis nArgs >>= normalise

    -- (nP - nArgs) is the amount of actual parameters we consider in our encoding
    -- the remaining Pi types are indices
    (P , I) ← getTels fargs (nP - nArgs) ty

    descs&skels ← forM cs λ cn → do
      -- get the type of current constructor, with explicit arguments and parameters stripped
      conTyp ← getType cn >>= normalise <&> dropPis nP
      (desc , skel) ← getDesc fargs nm (nP - nArgs) id 0 conTyp
      return $ (cn , skel) , desc

    let descs = List.map proj₂ descs&skels
    let skels = List.map proj₁ descs&skels

    let D = foldr (λ C D → con (quote DataDesc._∷_) (C ⟨∷⟩ D ⟨∷⟩ []))
                  (con (quote DataDesc.[]) [])
                  descs

    qconstr      ← freshName "constr"
    qsplit       ← freshName "split"
    qsplitconstr ← freshName "split∘constr"
    qconstrsplit ← freshName "constr∘split"
    qwf          ← freshName "wf"

    declareDef (vArg qconstr)
      (pi (vArg (def (quote ⟦_,_⟧xtel) (P ⟨∷⟩ I ⟨∷⟩ [])))
          (abs "PI" (pi (vArg unknown) (abs "x" unknown))))

    declareDef (vArg qsplit)
      (pi (vArg (def (quote ⟦_,_⟧xtel) (P ⟨∷⟩ I ⟨∷⟩ [])))
          (abs "PI" (pi (vArg unknown) (abs "x" unknown))))

    declareDef (vArg qconstrsplit)
      (pi (vArg (def (quote ⟦_,_⟧xtel) (P ⟨∷⟩ I ⟨∷⟩ [])))
          (abs "PI" (pi (vArg unknown) (abs "x" unknown))))

    declareDef (vArg qsplitconstr)
      (pi (vArg (def (quote ⟦_,_⟧xtel) (P ⟨∷⟩ I ⟨∷⟩ [])))
          (abs "PI" (pi (vArg unknown) (abs "x" unknown))))

    declareDef (vArg qwf)
      (pi (vArg (def (quote ⟦_,_⟧xtel) (P ⟨∷⟩ I ⟨∷⟩ [])))
          (abs "PI" (pi (vArg unknown) (abs "x" unknown))))

    deriveThings gargs (nP - nArgs) qconstr qsplit qsplitconstr qconstrsplit qwf skels

    unify hole (def (quote badconvert) ((con (quote mkHD)
      (   P                 -- P
      ⟅∷⟆ I                 -- I
      ⟅∷⟆ unknown           -- ℓ
      ⟅∷⟆ def nm gargs      -- A
      ⟅∷⟆ lit (nat nCons)   -- n
      ⟅∷⟆ D                 -- D
      ⟨∷⟩ names             -- names
      ⟨∷⟩ def qconstr      []
      ⟨∷⟩ def qsplit       []
      ⟨∷⟩ def qsplitconstr []
      ⟨∷⟩ def qconstrsplit []
      ⟨∷⟩ def qwf          []
      ⟨∷⟩ [])) ⟨∷⟩ []))
