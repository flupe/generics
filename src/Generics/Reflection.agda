module Generics.Reflection where

open import Function.Base
open import Data.Nat.Base
open import Data.List.Base   as List hiding (_++_)
import Data.Vec.Base as Vec
open import Data.String using (String; _++_)
open import Data.Bool.Base
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Reflection hiding (var; return; _>>=_; _>>_)
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
        aux (Π[ s ∶ arg (arg-info _ (modality r _)) a ] b) n I = do
          r′ ← quoteTC r
          aux b (suc n) (con (quote _⊢<_>_)
              (I ⟨∷⟩ r′
                 ⟨∷⟩ vLam "PI" (telescopize nP n 0 a)
                 ⟨∷⟩ []))
        aux _ _ _ = typeError [ strErr "ill-formed type signature" ]

getTels : ℕ → Type → TC (Term × Term)
getTels nP ty = aux nP ty 0 (quoteTerm (ε {A = ⊤}))
  where aux : ℕ → Type → ℕ → Term → TC (Term × Term)
        aux zero ty _ P = (P ,_) <$> getIndexTel nP ty
        aux (suc nP) (Π[ s ∶ arg (arg-info _ (modality r _)) a ] b) n P = do
          r′ ← quoteTC r
          aux nP b (suc n) (con (quote _⊢<_>_)
              (P ⟨∷⟩ r′
                 ⟨∷⟩ vLam "PI" (telescopize 0 n 0 a)
                 ⟨∷⟩ []))
        aux _ _ _ _ = typeError [ strErr "ill-formed type signature" ]
  
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
        i′ ← quoteTC i
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
        i′    ← quoteTC i
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

  A′ : Σ[ P ⇒ I ] → Set ℓ
  A′ = uncurry P I A
  
  field
    {n}   : ℕ
    D     : DataDesc P I ℓ n
    names : Vec String n

    to     : (pi : Σ[ P ⇒ I ]) → A′ pi → μ D pi
    split  : (pi : Σ[ P ⇒ I ]) → A′ pi → ⟦ D ⟧Data ℓ A′ pi
    from   : (pi : Σ[ P ⇒ I ]) → μ D pi → A′ pi
    constr : (pi : Σ[ P ⇒ I ]) → ⟦ D ⟧Data ℓ A′ pi → A′ pi

    constr-coh  : (pi : Σ[ P ⇒ I ]) (x : ⟦ D ⟧Data _ (μ D) pi)
                → constr _ (mapData _ _ (λ {pi} → from pi) D x) ≡ from pi ⟨ x ⟩
    split-coh   : (pi : Σ[ P ⇒ I ]) (x : ⟦ D ⟧Data _ (μ D) pi)
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

--     constr-coh  : (pi : Σ[ P ⇒ I ]) (x : ⟦ D ⟧Data _ (μ D) pi)
--                 → constr (mapData _ _ from D x) ≡ from ⟨ x ⟩
--     split-coh   : (pi : Σ[ P ⇒ I ]) (x : ⟦ D ⟧Data _ (μ D) pi)
--                 → split (from ⟨ x ⟩) ≡ mapData _ _ from D x

deriveFromConstr : Name → Name → Name → Name → List (Name × Skel) → TC ⊤
deriveFromConstr qfrom qconstr qconstrcoh qsplitcoh cons = do
  let cls = deriveDef cons
  defineFun qfrom      (List.map proj₁ cls)
  defineFun qconstr    (List.map (proj₁ ∘ proj₂)  cls)
  defineFun qconstrcoh (List.map (proj₂ ∘ proj₂)  cls)
  defineFun qsplitcoh (List.map (proj₂ ∘ proj₂)  cls)
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
    deriveExtend (Cπ i C) =
      let (o , tel , pat , tfrom , tconstr) = deriveExtend C
      in suc o
       , ("x" , vArg unknown) ∷ tel
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
                (con n tfrom)
       , clause (("PI" , vArg unknown) ∷ tel)
                (var o ⟨∷⟩ con (quote _,_) (k ⟨∷⟩ pat ⟨∷⟩ []) ⟨∷⟩ [])
                (con n tsplit)
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
  testing : Name → Term → TC ⊤
  testing nm hole = do
    data-type nP cs ← getDefinition nm
      where _ → typeError (strErr "Given name is not a datatype." ∷ [])
    let n = List.length cs
    names ← quoteTC (Vec.fromList (List.map showQName cs))
    ty ← getType nm >>= normalise
    (P , I) ← getTels nP ty
    contyp ← mapM (λ cn → getType cn >>= normalise <&> dropPis nP) cs
    descs&skels ← mapM (λ cn → getType cn >>= normalise >>= getDesc nm nP 0 ∘ dropPis nP <&> λ (D , S) → (cn , S) , D) cs

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
      (pi (vArg (def (quote Σ[_⇒_]) (P ⟨∷⟩ I ⟨∷⟩ [])))
          (abs "PI" (pi (vArg unknown) (abs "x" unknown))))

    declareDef (vArg qsplit)
      (pi (vArg (def (quote Σ[_⇒_]) (P ⟨∷⟩ I ⟨∷⟩ [])))
          (abs "PI" (pi (vArg unknown) (abs "x" unknown))))

    declareDef (vArg qfrom)
      (pi (vArg (def (quote Σ[_⇒_]) (P ⟨∷⟩ I ⟨∷⟩ [])))
          (abs "PI" (pi (vArg unknown) (abs "x" unknown))))

    declareDef (vArg qconstr)
      (pi (vArg (def (quote Σ[_⇒_]) (P ⟨∷⟩ I ⟨∷⟩ [])))
          (abs "PI" (pi (vArg unknown) (abs "x" unknown))))

    declareDef (vArg qconstrcoh)
      (pi (vArg (def (quote Σ[_⇒_]) (P ⟨∷⟩ I ⟨∷⟩ [])))
          (abs "PI" (pi (vArg unknown) (abs "x" unknown))))

    declareDef (vArg qsplitcoh)
      (pi (vArg (def (quote Σ[_⇒_]) (P ⟨∷⟩ I ⟨∷⟩ [])))
          (abs "PI" (pi (vArg unknown) (abs "x" unknown))))

    -- declareDef (vArg qconstr)
    --   (pi (vArg (def (quote Σ[_⇒_]) (P ⟨∷⟩ I ⟨∷⟩ [])))
    --       (abs "PI" (pi (vArg unknown) (abs "x" unknown))))

    deriveToSplit    qto   qsplit  skels
    deriveFromConstr qfrom qconstr qconstrcoh qsplitcoh skels

    unify hole (con (quote mkHD)
      (   P          -- P
      ⟅∷⟆ I         -- I
      ⟅∷⟆ unknown   -- ℓ
      ⟅∷⟆ def nm [] -- A
      ⟅∷⟆ D         -- D
      ⟨∷⟩ names     -- names
      ⟨∷⟩ def qto     []
      ⟨∷⟩ def qsplit  []
      ⟨∷⟩ def qfrom   []
      ⟨∷⟩ def qconstr []
      ⟨∷⟩ def qconstrcoh []
      ⟨∷⟩ def qsplitcoh  []
      ⟨∷⟩ []))

-- data vec (A : Set) : ℕ → Set where
--   nil  : vec A 0
--   cons : ∀ n → A → vec A n → vec A (suc n)
-- 

data tree (A : Set) (B : A → Set) : Set where
  node : (x : A) (f : B x → tree A B) → tree A B

ok = testing tree

-- ok = testing vec

macro
  test : Name → Term → TC ⊤
  test nm hole = do
    getType nm >>= quoteTC >>= tErr

-- P : Telescope ⊤
-- P = ε ⊢< relevant > const Set
-- 
-- I : ExTele P
-- I = ε ⊢< relevant > const ℕ
-- 
-- D : DataDesc P I lzero 1
-- D = var (const (tt , 0)) ∷ []
-- 
-- to : ∀ {A n} (x : vec A n) → μ D ((tt , A) , tt , n)
-- to nil = ⟨ zero , lift refl ⟩

-- ok : HD bb
 
{-

-- data Tree (A : Set) : Set where
--   leaf : Tree A
--   node : .A → Tree A → Tree A
-- 
-- data W (A : Set) (B : A → Set) : Set where
--   node : (x : A) (f : B x → W A B) → W A B

-- ok = testing W

{-



-- ok = 
-- ok = testing ((a b : ℕ) → .(a ≡ b) → Set)

{-



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

-------------------------------
-- STEP 3: DERIVING CONVERSIONS
-------------------------------


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

-}

-}
