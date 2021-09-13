module Generics.Reflection where

open import Function.Base
open import Data.Nat.Base
open import Data.List.Base   as List hiding (_++_)
import Data.Vec.Base as Vec
open import Data.String using (String; _++_)
open import Data.Bool.Base
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Agda.Builtin.Reflection renaming ( primShowQName     to showQName
                                             ; primQNameEquality to _Name≈_
                                             )
open import Reflection.Abstraction using (unAbs)
open import Reflection.Argument    using (_⟨∷⟩_; _⟅∷⟆_)
open import Reflection.Term hiding (Telescope; var)
open import Relation.Nullary using (yes; no)

open import Category.Monad   as Monad

import Data.List.Categorical as List
import Data.Nat.Induction    as Nat

-- open import Data.List.Instances using (listFunctor)
open import Reflection.TypeChecking.Monad.Instances using (tcMonad)
open import Reflection.Traversal hiding (_,_)

open import Generics.Prelude
open import Generics.Telescope
open import Generics.Desc
open import Generics.HasDesc
import Function.Identity.Categorical as Identity

open List.TraversableM ⦃...⦄
open Monad.RawMonad    ⦃...⦄

tErr : Term → TC ⊤
tErr = typeError ∘ [_] ∘ termErr

sErr : String → TC ⊤
sErr = typeError ∘ [_] ∘ strErr

open Actions

weakn : Term → Term
weakn = traverseTerm Identity.applicative actions (0 Reflection.Traversal., [])
  where
    actions : Actions Identity.applicative
    actions .onVar _ zero = zero
    actions .onVar _ (suc n) = n
    actions .onMeta _ = id
    actions .onCon  _ = id
    actions .onDef  _ = id


{-
When converting types to telescopes
variables are converted to context lookups:
Given P := [A₁ ⋯ Aₙ] (where Aᵢ₊₁ depends on A₁ ⋯ Aᵢ)
      I := [B₁ ⋯ Bₘ],
we want to replace a term in context (Γ , A₁ , ⋯ , Aₙ , B₁ , ⋯ , Bₘ , C₁ , ⋯ , Cₚ)
into a term in context               (Γ , Σ P I , C₁ , ⋯ , Cₚ)
(We assume C₁ ⋯ Cₚ are the types of locally-bound variables)

 A term (var k) should be replaced by:
   - (var k)                                 if k < p

   - (proj₂ (proj₂ (var p)))                 if p         <= k < p + m      (inside I)
     (proj₂ (proj₁ (proj₂ (var p))))         ...
     (proj₂ (proj₁ (proj₁ (proj₂ (var p))))) ...

   - (proj₂ (proj₁ (var p))                  if p + m     <= k < p + m + n  (inside P)
   - (proj₂ (proj₁ (proj₁ (var p)))          ...
   - (proj₂ (proj₁ (proj₁ (proj₁ (var p))))  ...

   - var (k + 1 - n - m)                     if p + m + n <= k
-}


-- o: position of Σ P I in the context (i.e number of locally bound variables)
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


module _ (nP nI : ℕ) where

    telescopize       : ℕ → Term → Term
    telescopizeSort   : ℕ → Sort → Sort
    telescopizeArgs   : ℕ → List (Arg Term) → List (Arg Term)
    telescopizeTel    : ℕ → List (String × Arg Type) → List (String × Arg Type)
    telescopizeClause : ℕ → List Clause → List Clause

    telescopize o (var k args) =
      let args′ = telescopizeArgs o args in
           if k <ᵇ o           then var k args′
      else if k ∸ o <ᵇ nI      then mkIVar o (k ∸ o     ) args′
      else if k ∸ o <ᵇ nI + nP then mkPVar o (k ∸ o ∸ nI) args′
      else                          var (k ∸ pred (nP + nI)) args′

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
    t₁ = telescopize 0 0 5 t

    t₁-ok : t₁ ≡ var 4 []
    t₁-ok = refl

    -- retrieving var in index telescope, 4 variable locally-bound
    t₂ : Term
    t₂ = telescopize 2 1 4 t

    t₂-ok : t₂ ≡ def (quote proj₂) (def (quote proj₂) (var 4 [] ⟨∷⟩ []) ⟨∷⟩ [])
    t₂-ok = refl

    -- retrieving var in parameter telescope, 2 variable locally-bound
    t₃ : Term
    t₃ = telescopize 1 2 2 t

    t₃-ok : t₃ ≡ def (quote proj₂) (def (quote proj₁) (var 2 [] ⟨∷⟩ []) ⟨∷⟩ [])
    t₃-ok = refl

    -- retrieving var outside parameter & index telescope
    t₄ : Term
    t₄ = telescopize 1 1 2 t

    t₄-ok : t₄ ≡ var 3 []
    t₄-ok = refl

    -- retrieving 4th var in index telescope
    t₅ : Term
    t₅ = telescopize 0 5 1 t

    t₅-ok : t₅ ≡ def (quote proj₂)
                   (def (quote proj₁)
                    (def (quote proj₁)
                     (def (quote proj₁) (def (quote proj₂) (var 1 [] ⟨∷⟩ []) ⟨∷⟩ []) ⟨∷⟩
                      [])
                     ⟨∷⟩ [])
                    ⟨∷⟩ [])
    t₅-ok = refl


-----------------------------
-- deriving telescopes

getIndexTel : ℕ → Type → TC Term
getIndexTel nP ty = aux ty 0 (con (quote ε) [])
  where aux : Type → ℕ → Term → TC Term
        aux (agda-sort s) n I = return I
        aux (Π[ s ∶ arg i a ] b) n I = do
          i′ ← quoteTC i >>= normalise
          aux b (suc n) (con (quote _⊢<_>_)
              (I ⟨∷⟩ i′
                 ⟨∷⟩ vLam "PI" (telescopize nP n 0 a)
                 ⟨∷⟩ []))
        aux _ _ _ = typeError [ strErr "ill-formed type signature when deriving index telescope" ]

getTels : ℕ → Type → TC (Term × Term)
getTels nP ty = aux nP ty 0 (quoteTerm (ε {A = ⊤}))
  where aux : ℕ → Type → ℕ → Term → TC (Term × Term)
        aux zero ty _ P = (P ,_) <$> getIndexTel nP ty
        aux (suc nP) (Π[ s ∶ arg i a ] b) n P = do
          i′ ← quoteTC i >>= normalise
          aux nP b (suc n) (con (quote _⊢<_>_)
              (P ⟨∷⟩ i′
                 ⟨∷⟩ vLam "PI" (telescopize 0 n 0 a)
                 ⟨∷⟩ []))
        aux _ _ _ _ = typeError [ strErr "ill-formed type signature when deriving parameter telescope" ]

-----------------------------
-- deriving descriptions

-- we cannot unquote things in Setω directly
-- so we can't unquote Terms of type Telescope directly
-- instead we produce skeleton to ease late code gen
data Skel : Set where
  Cκ   : Skel
  Cπ   : ArgInfo → Skel → Skel
  _C⊗_ : Skel → Skel → Skel

dropPis : ℕ → Type → Type
dropPis (suc n) (pi a (abs _ b)) = dropPis n b
dropPis _ t = t


module _ (dt : Name) (nP : ℕ) where

  toIndex : ℕ → List (Arg Term) → Term
  toIndex nV xs = vLam "PV" $ foldl cons (quoteTerm tt) (drop nP xs)
    where cons : Term → Arg Term → Term
          cons x (arg _ y) =
            con (quote _,_) ( x
                          ⟨∷⟩ telescopize nP nV 0 y
                          ⟨∷⟩ [])

  getRecDesc : ℕ → Type → TC (Maybe (Term × Skel))
  getRecDesc n (def nm args) = do
    if nm Name≈ dt
      then return (just (con (quote Desc.var) (toIndex n args ⟨∷⟩ []) , Cκ))
      else return nothing
  getRecDesc n (Π[ s ∶ arg i a ] b) = do
    getRecDesc (suc n) b >>= λ where
      (just (right , skright)) → do
        i′ ← quoteTC i >>= normalise
        return $ just ( con (quote Desc.π) (con (quote refl) [] ⟨∷⟩ i′ ⟨∷⟩ vLam "PV" (telescopize nP n 0 a) ⟨∷⟩ right ⟨∷⟩ [])
                      , Cπ i skright
                      )
      nothing  → return nothing
  getRecDesc n ty = return nothing

  {-# TERMINATING #-}
  getDesc : ℕ → Type → TC (Term × Skel)
  getDesc n (def nm args) =
    -- we're gonna assume nm == dt
    return (con (quote Desc.var) (toIndex n args ⟨∷⟩ []) , Cκ)
  getDesc n (Π[ s ∶ arg i a ] b) =
    getRecDesc n a >>= λ where
      -- (possibly higher order) inductive argument
      (just (left , skleft)) → do
        -- we cannot depend on inductive argument (for now)
        -- note: inductive arguments are relevant (for now)
        -- /!\ inductive arguments to not bind a variable, so we weaken term
        --     this causes termination checking issues
        (right , skright) ← getDesc n (weakn b)
        return (con (quote Desc._⊗_) (left ⟨∷⟩ right ⟨∷⟩ []) , (skleft C⊗ skright))
      -- plain old argument
      nothing → do
        (right , skright) ← getDesc (suc n) b
        i′    ← quoteTC i >>= normalise
        return ( con (quote Desc.π) (con (quote refl) []
                                ⟨∷⟩ i′
                                ⟨∷⟩ vLam "PV" (telescopize nP n 0 a)
                                ⟨∷⟩ right
                                ⟨∷⟩ [])
               , Cπ i skright
               )
  getDesc _ _ = typeError [ strErr "ill-formed constructor type" ]



record HD {P} {I : ExTele P} {ℓ} (A : Indexed P I ℓ) : Setω where
  constructor mkHD

  A′ : ⟦ P , I ⟧xtel → Set ℓ
  A′ = uncurry P I A

  field
    {n}   : ℕ
    D     : DataDesc P I ℓ n
    names : Vec String n

    to     : (pi : ⟦ P , I ⟧xtel) → A′ pi → μ D pi
    split  : (pi : ⟦ P , I ⟧xtel) → A′ pi → ⟦ D ⟧Data ℓ A′ pi
    from   : (pi : ⟦ P , I ⟧xtel) → μ D pi → A′ pi
    constr : (pi : ⟦ P , I ⟧xtel) → ⟦ D ⟧Data ℓ A′ pi → A′ pi

    constr-coh  : (pi : ⟦ P , I ⟧xtel) (x : ⟦ D ⟧Data _ (μ D) pi)
                → constr _ (mapData _ _ (λ {pi} → from pi) D x) ≡ from pi ⟨ x ⟩
    split-coh   : (pi : ⟦ P , I ⟧xtel) (x : ⟦ D ⟧Data _ (μ D) pi)
                → split _ ((λ {pi} → from pi) ⟨ x ⟩) ≡ mapData _ _ (λ {pi} → from pi) D x

postulate
  todo : ∀ {ℓ} {A : Set ℓ} → A

badconvert : ∀ {P} {I : ExTele P} {ℓ} {A : Indexed P I ℓ}
           → HD {P} {I} {ℓ} A → HasDesc {P} {I} {ℓ} A
badconvert d = record
  { D          = HD.D d
  ; names      = HD.names d
  ; to         = λ {PI} → HD.to   d PI
  ; from       = λ {PI} → HD.from d PI
  ; from∘to    = todo
  ; to∘from    = todo
  ; constr     = λ {PI} → HD.constr d PI
  ; split      = λ {PI} → HD.split d PI
  ; constr-coh = λ {PI} → HD.constr-coh d PI
  ; split-coh  = λ {PI} → HD.split-coh d PI
  }


withAI : ArgInfo → Term → Term
withAI (arg-info v (modality relevant q  ))   t = t
withAI i@(arg-info v (modality irrelevant q)) t = con (quote irrv) [ arg i t ]

patAI : ArgInfo → Pattern → Pattern
patAI (arg-info v (modality relevant q  ))   t = t
patAI i@(arg-info v (modality irrelevant q)) t = con (quote irrv) [ arg i t ]

fromAI : ArgInfo → Term → Arg Term
fromAI i@(arg-info v (modality irrelevant q)) t = arg i (def (quote Irr.unirr) [ vArg t ])
fromAI i t = arg i t


deriveToSplit : Name → Name → List (Name × Skel) → TC ⊤
deriveToSplit qto qsplit cons = do
  let cls = deriveDef cons
  defineFun qto    (List.map proj₁ cls)
  defineFun qsplit (List.map proj₂ cls)
  return tt
  where
    derive⟦⟧ : Skel → ℕ × List (String × Arg Type) × List (Arg Pattern) × List (Arg Term)
    derive⟦⟧ Cκ = 0 , [] , [] , []
    derive⟦⟧ (Cπ i C) =
      let (o , tel , pat , args) = derive⟦⟧ C
      in suc o
       , ("x" , arg i unknown) ∷ tel
       , arg i (var o) ∷ pat
       , fromAI i (var o []) ∷ args
    derive⟦⟧ (A C⊗ B) = todo -- never actually used, weirdly

    deriveExtend : Skel → ℕ × List (String × Arg Type) × List (Arg Pattern)
                            × Term × Term
    deriveExtend Cκ = 0 , [] , [] , con (quote lift) (con (quote refl) [] ⟨∷⟩ [])
                                  , con (quote lift) (con (quote refl) [] ⟨∷⟩ [])
    deriveExtend (Cπ i C) =
      let (o , tel , pat , tto , tsplit) = deriveExtend C
      in suc o
       , ("x" , arg i unknown) ∷ tel
       , arg i (var o) ∷ pat
       , con (quote _,_) (withAI i (var o []) ⟨∷⟩ tto    ⟨∷⟩ [])
       , con (quote _,_) (withAI i (var o []) ⟨∷⟩ tsplit ⟨∷⟩ [])
    deriveExtend (A C⊗ B) =
      let (ro , rtel , rpat , rargs)  = derive⟦⟧ A
          (o , tel , pat , tto , tsplit) = deriveExtend B
      in suc o
       , ("f" , vArg unknown) ∷ tel
       , var o ⟨∷⟩ pat
       , (con (quote _,_)
           (pat-lam [ clause rtel rpat
                             (def qto (unknown ⟨∷⟩ var (o + ro) rargs ⟨∷⟩ []))
                    ] []
           ⟨∷⟩ tto
           ⟨∷⟩ []))
       , (con (quote _,_) (var o [] ⟨∷⟩ tsplit ⟨∷⟩ []))

    deriveClause : Term → Name × Skel → Clause × Clause
    deriveClause k (n , s) =
      let (o , tel , pat , tto , tsplit) = deriveExtend s
      in clause (("PI" , vArg unknown) ∷ tel)
                (var o ⟨∷⟩ con n pat ⟨∷⟩ [])
                (con (quote ⟨_⟩) (con (quote _,_) (k ⟨∷⟩ tto ⟨∷⟩ []) ⟨∷⟩ []))
       , clause (("PI" , vArg unknown) ∷ tel)
                (var o ⟨∷⟩ con n pat ⟨∷⟩ [])
                (con (quote _,_) (k ⟨∷⟩ tsplit ⟨∷⟩ []))

    deriveClauses : Term → List (Name × Skel) → List (Clause × Clause)
    deriveClauses k [] = []
    deriveClauses k (x ∷ xs) =
      deriveClause k x ∷ deriveClauses (con (quote Fin.suc) (k ⟨∷⟩ [])) xs

    deriveDef : List (Name × Skel) → List (Clause × Clause)
    deriveDef [] = [ absurd-clause (("PI" , hArg unknown) ∷ ("x" , vArg unknown) ∷ [])
                                   (var 1 ⟨∷⟩ absurd 0 ⟨∷⟩ [] )
                   , absurd-clause (("PI" , hArg unknown) ∷ ("x" , vArg unknown) ∷ [])
                                   (var 1 ⟨∷⟩ absurd 0 ⟨∷⟩ [] )
                   ]
    deriveDef xs = deriveClauses (con (quote Fin.zero) []) xs

-- TODO: actually fill in with parameters in scope
-- needed because if the first argument of a constructor is implicit,
-- won't know where to insert
nToUnknowns : ℕ → List (Arg Term)
nToUnknowns zero = []
nToUnknowns (suc n) = hArg unknown ∷ nToUnknowns n

deriveFromConstr : ℕ → Name → Name → Name → Name → List (Name × Skel) → TC ⊤
deriveFromConstr nP qfrom qconstr qconstrcoh qsplitcoh cons = do
  let cls = deriveDef cons
  defineFun qfrom      (List.map proj₁ cls)
  -- ttt ← quoteTC (List.map proj₁ cls) >>= normalise
  -- tErr ttt
  defineFun qconstr    (List.map (proj₁ ∘ proj₂)  cls)
  defineFun qconstrcoh (List.map (proj₂ ∘ proj₂)  cls)
  defineFun qsplitcoh  (List.map (proj₂ ∘ proj₂)  cls)
  return tt
  where
    derive⟦⟧ : Skel → ℕ × List (String × Arg Type) × List (Arg Pattern) × List (Arg Term)
    derive⟦⟧ Cκ = 0 , [] , [] , []
    derive⟦⟧ (Cπ i C) =
      let (o , tel , pat , args) = derive⟦⟧ C
      in suc o
       , ("x" , vArg unknown) ∷ tel
       , arg i (var o) ∷ pat
       , fromAI i (var o []) ∷ args
    derive⟦⟧ (A C⊗ B) = todo -- never actually used, weirdly

    deriveExtend : Skel → ℕ × List (String × Arg Type) × Pattern
                            × List (Arg Term) × List (Arg Term)
    deriveExtend Cκ = 0 , [] , con (quote lift) (con (quote refl) [] ⟨∷⟩ [])
                             , []
                             , []
    deriveExtend (Cπ i@(arg-info v m) C) =
      let (o , tel , pat , tfrom , tconstr) = deriveExtend C
      in suc o
       , ("x" , arg (arg-info visible m) unknown) ∷ tel
       , con (quote _,_) (patAI i (var o) ⟨∷⟩ pat ⟨∷⟩ [])
       , arg i (var o []) ∷ tfrom
       , arg i (var o []) ∷ tconstr
    deriveExtend (A C⊗ B) =
      let (ro , rtel , rpat , rargs)  = derive⟦⟧ A
          (o , tel , pat , tfrom , tconstr) = deriveExtend B
      in suc o
       , ("f" , vArg unknown) ∷ tel
       , con (quote _,_) (var o ⟨∷⟩ pat ⟨∷⟩ []) -- var o ⟨∷⟩ pat
       , pat-lam [ clause rtel rpat (def qfrom (unknown ⟨∷⟩ var (o + ro) rargs ⟨∷⟩ [])) ] []
           ⟨∷⟩ tfrom
       , var o [] ⟨∷⟩ tconstr -- (con (quote _,_) (var o [] ⟨∷⟩ tsplit ⟨∷⟩ []))

    deriveClause : Pattern → Name × Skel → Clause × Clause × Clause
    deriveClause k (n , s) =
      let (o , tel , pat , tfrom , tsplit) = deriveExtend s
      in clause (("PI" , vArg unknown) ∷ tel)
                (var o ⟨∷⟩ con (quote ⟨_⟩)
                  [ vArg (con (quote _,_) (k ⟨∷⟩ pat ⟨∷⟩ [])) ] ⟨∷⟩ [])
                (con n (nToUnknowns nP List.++ tfrom))
       , clause (("PI" , vArg unknown) ∷ tel)
                (var o ⟨∷⟩ con (quote _,_) (k ⟨∷⟩ pat ⟨∷⟩ []) ⟨∷⟩ [])
                (con n (nToUnknowns nP List.++ tsplit))
       , clause (("PI" , vArg unknown) ∷ tel)
                -- TODO: ⟦ ⟧Data (μ D) instead of ⟦ ⟧Data A′
                (var o ⟨∷⟩ con (quote _,_) (k ⟨∷⟩ pat ⟨∷⟩ []) ⟨∷⟩ [])
                (con (quote refl) [])

    deriveClauses : Pattern → List (Name × Skel) → List (Clause × Clause × Clause)
    deriveClauses k [] = []
    deriveClauses k (x ∷ xs) = deriveClause k x ∷ deriveClauses (con (quote Fin.suc) (k ⟨∷⟩ [])) xs

    deriveDef : List (Name × Skel) → List (Clause × Clause × Clause)
    deriveDef [] = [ cls , cls , cls ]
      where cls = absurd-clause (("PI" , hArg unknown) ∷ ("x" , vArg unknown) ∷ [])
                                (var 1 ⟨∷⟩ absurd 0 ⟨∷⟩ [] )
    deriveDef xs = deriveClauses (con (quote Fin.zero) []) xs

macro
  testing : Term → Term → TC ⊤
  testing t hole = do
    def nm gargs ← return t
      where _ → typeError [ strErr "Expected name with arguments" ]
    data-type nP cs ← getDefinition nm
      where _ → typeError (strErr "Given name is not a datatype." ∷ [])
    let n  = List.length cs
    names ← quoteTC (Vec.fromList (List.map showQName cs))
    ty ← getType nm >>= normalise <&> dropPis (length gargs) >>= normalise
    -- ttt ← quoteTC ty
    -- tErr ttt
    (P , I) ← getTels (nP - length gargs) ty
    contyp ← mapM (λ cn → getType cn >>= normalise <&> dropPis nP) cs
    descs&skels ← mapM (λ cn → getType cn >>= normalise >>= getDesc nm (nP - length gargs) 0 ∘ dropPis nP <&> λ (D , S) → (cn , S) , D) cs

    let descs = List.map proj₂ descs&skels
    let skels = List.map proj₁ descs&skels


    let D = foldr (λ C D → con (quote DataDesc._∷_) (C ⟨∷⟩ D ⟨∷⟩ []))
                  (con (quote DataDesc.[]) [])
                  descs

    qto        ← freshName "to"
    qsplit     ← freshName "split"
    qfrom      ← freshName "from"
    qconstr    ← freshName "constr"
    qconstrcoh ← freshName "constr-coh"
    qsplitcoh  ← freshName "split-coh"

    declareDef (vArg qto)
      (pi (vArg (def (quote ⟦_,_⟧xtel) (P ⟨∷⟩ I ⟨∷⟩ [])))
          (abs "PI" (pi (vArg unknown) (abs "x" unknown))))

    declareDef (vArg qsplit)
      (pi (vArg (def (quote ⟦_,_⟧xtel) (P ⟨∷⟩ I ⟨∷⟩ [])))
          (abs "PI" (pi (vArg unknown) (abs "x" unknown))))

    declareDef (vArg qfrom)
      (pi (vArg (def (quote ⟦_,_⟧xtel) (P ⟨∷⟩ I ⟨∷⟩ [])))
          (abs "PI" (pi (vArg unknown) (abs "x" unknown))))

    declareDef (vArg qconstr)
      (pi (vArg (def (quote ⟦_,_⟧xtel) (P ⟨∷⟩ I ⟨∷⟩ [])))
          (abs "PI" (pi (vArg unknown) (abs "x" unknown))))

    declareDef (vArg qconstrcoh)
      (pi (vArg (def (quote ⟦_,_⟧xtel) (P ⟨∷⟩ I ⟨∷⟩ [])))
          (abs "PI" (pi (vArg unknown) (abs "x" unknown))))

    declareDef (vArg qsplitcoh)
      (pi (vArg (def (quote ⟦_,_⟧xtel) (P ⟨∷⟩ I ⟨∷⟩ [])))
          (abs "PI" (pi (vArg unknown) (abs "x" unknown))))

    -- declareDef (vArg qconstr)
    --   (pi (vArg (def (quote ⟦_,_⟧xtel) (P ⟨∷⟩ I ⟨∷⟩ [])))
    --       (abs "PI" (pi (vArg unknown) (abs "x" unknown))))

    deriveToSplit qto qsplit skels
    deriveFromConstr nP qfrom qconstr qconstrcoh qsplitcoh skels

    unify hole (con (quote mkHD)
      (   P            -- P
      ⟅∷⟆ I            -- I
      ⟅∷⟆ unknown      -- ℓ
      ⟅∷⟆ def nm gargs -- A
      ⟅∷⟆ D            -- D
      ⟨∷⟩ names        -- names
      ⟨∷⟩ def qto        []
      ⟨∷⟩ def qsplit     []
      ⟨∷⟩ def qfrom      []
      ⟨∷⟩ def qconstr    []
      ⟨∷⟩ def qconstrcoh []
      ⟨∷⟩ def qsplitcoh  []
      ⟨∷⟩ []))

-- data W (A : Set) (B : A → Set) : Set where
--   sup : (x : A) (f : B x → W A B) → W A B
--
-- ok = testing W
