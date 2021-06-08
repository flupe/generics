{-# OPTIONS --rewriting #-}
open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc
open import Generics.HasDesc
open import Generics.Reflection

open import Agda.Builtin.Reflection

open import Generics.Constructions.Elim
open import Data.String hiding (show)

module Parametrized where


module DNat where

  natHasDesc : HasDesc ℕ
  natHasDesc = badconvert (testing ℕ)

  -- showℕ : ℕ → String
  -- showℕ = show natHasDesc (tt , tt , tt)

  postulate P : ℕ → Set

  t : ∀ x → P x
  t = elim″ natHasDesc P {!!} {!!}

module Vek where

  data vek (A : Set) : ℕ → Set where
    nil  : vek A 0
    cons : ∀ {n} → A → vek A n → vek A (suc n)

  vekHasDesc : HasDesc vek
  vekHasDesc = badconvert (testing vek)

  postulate P : {A : Set} {n : ℕ} → vek A n → Set

  t : ∀ {A} {n} (x : vek A n) → P x
  t = elim″ vekHasDesc P {!!} {!!}

module W where

  data W (A : Set) (B : A → Set) : Set where
    node : (x : A) (f : B x → W A B) → W A B

  roseHasDesc : HasDesc W
  roseHasDesc = badconvert (testing W)

  postulate P : {A : Set} {B : A → Set} → W A B → Set

  t : ∀ {A} {B} (x : W A B) → P x
  t = elim″ roseHasDesc P {!!}

{-

  elimℕ : ∀ {ℓ} (P : ℕ → Set ℓ) → P 0 → (∀ n → P n → P (suc n)) → ∀ n → P n
  elimℕ P H0 Hn n = elim″ natHasDesc P H0 Hn n

  -- noConfℕ : {x y : ℕ} (p : suc x ≡ suc y) → Confusion.NoConfusion natHasDesc (suc x) (suc y)
  -- noConfℕ p = {!!}

  -- _ : showℕ 0 ≡ "zero ()"
  -- _ = refl

module Vek {ℓ} where

  D : Desc (ε ⊢< relevant > const (Set ℓ)) (ε ⊢< relevant > const ℕ) ℓ 2
  D = var (const (tt , relv 0))
    ∷ π refl (arg-info hidden relevant) (const ℕ)
        (π refl (arg-info visible relevant) {!!}
          (var (λ pv → tt , proj₂ (proj₁ (proj₂ pv)))
            ⊗ var λ pv → tt , {!!}))
    ∷ []


module DList {a : Level} where

  P : Telescope ⊤
  P = ε ⊢ const (Set a)

  I : ExTele P
  I = ε

  listD : Desc P I a 2
  listD = var (const tt)
        ∷ π refl proj₁ ((var (const tt)) ⊗ var (const tt))
        ∷ []

  List′ : Σ[ P ⇒ I ] → Set a
  List′ = uncurry′ P I List

  to : {pi : Σ[ P ⇒ I ]} → List′ pi → μ listD pi
  to []       = ⟨ zero , lift refl ⟩
  to (x ∷ xs) = ⟨ suc zero , x , to xs , lift refl ⟩

  from : {pi : Σ[ P ⇒ I ]} → μ listD pi → List′ pi
  from ⟨ zero , lift refl ⟩ = []
  from ⟨ suc zero , x , xs , lift refl ⟩ = x ∷ from xs

  constr : ∀ {pi} → ⟦ listD ⟧ a List′ pi → List′ pi
  constr (zero , lift refl) = []
  constr (suc zero , x , xs , lift refl) = x ∷ xs

  split : ∀ {pi} → List′ pi → ⟦ listD ⟧ a List′ pi
  split [] = zero , lift refl
  split (x ∷ xs) = suc zero , x , xs , lift refl

  from∘to : ∀ {pi} (x : List′ pi) → from (to x) ≡ x
  from∘to [] = refl
  from∘to (x ∷ xs) = cong (x ∷_) (from∘to xs)

  to∘from : ∀ {pi} (x : μ listD pi) → to (from x) ≡ x
  to∘from ⟨ zero , lift refl ⟩ = refl
  to∘from ⟨ suc zero , x , xs , lift refl ⟩ =
    cong (⟨_⟩ ∘ (suc zero ,_)) (cong₂ _,_ refl (cong₂ _,_ (to∘from xs) refl))

  constr-coh : ∀ {pi} (x : ⟦ listD ⟧ lzero (μ listD) pi) → constr (mapD lzero a from listD x) ≡ from ⟨ x ⟩
  constr-coh (zero , lift refl) = refl
  constr-coh (suc zero , x , xs , lift refl) = cong₂ _∷_ refl refl

  split-coh : ∀ {pi} (x : ⟦ listD ⟧ lzero (μ listD) pi) → split (from ⟨ x ⟩) ≡ mapD lzero a from listD x
  split-coh (zero , lift refl) = refl
  split-coh (suc zero , x , xs , lift refl) = cong (suc zero ,_) (cong₂ _,_ refl (cong₂ _,_ refl refl))

  listHasDesc : HasDesc List
  listHasDesc = record
    { D      = listD
    ; names  = "[]" ∷ "_∷_" ∷ []
    ; to     = to
    ; from   = from
    ; constr = constr
    ; split  = split
    ; from∘to = from∘to
    ; to∘from = to∘from
    ; constr-coh = constr-coh
    ; split-coh  = split-coh
    }

  ∷-inj : {A : Set a} {x y : A} {xs ys : List A} → x List.∷ xs ≡ y ∷ ys → x ≡ y × xs ≡ ys
  ∷-inj p with  Confusion.noConfusion listHasDesc p
  ... | refl , xs≡ys , _ = refl , xs≡ys

  ∷-cong : {A : Set a} {x y : A} {xs ys : List A} → x ≡ y → xs ≡ ys → x List.∷ xs ≡ y ∷ ys
  ∷-cong x≡y xs≡ys = {!!}

-}
{-

module W {a b : Level} where

  WP : Telescope ⊤
  WP = ε ⊢< relevant > const (Set a) ⊢< relevant > λ (tt , (tt , (rA))) → rA → Set b

  data W (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
    sup : (x : A) (f : B x → W A B) → W A B

  wD : DataDesc WP ε (a ⊔ b) 1
  wD = π refl (arg-info visible (modality relevant quantity-0))
           (λ (((tt , rA) , rB) , tt) → rA)
         (π refl (arg-info visible (modality relevant quantity-0))
           (λ (((tt , rA) , rB) , (tt , rp)) → rB rp)
           (var (const tt)) ⊗ (var (const tt)))
     ∷ []


  to : ∀ {pi} → unindexed WP ε _ W pi → μ wD pi
  to {pi = ((tt , A) , B) , tt} (sup x f) =
    ⟨ zero , x , (λ s → to (f s)) , lift refl ⟩

  from : ∀ {pi} → μ wD pi → unindexed WP ε _ W pi
  from {pi = ((tt , A) , B) , tt} ⟨ zero , x , f , lift refl ⟩ =
    sup x λ s → from (f s)

  constr  : ∀ {pi} → ⟦ wD ⟧Data (a ⊔ b) (unindexed WP ε _ W) pi → unindexed WP ε _ W pi
  constr {((tt , A) , B) , tt} (zero , x , f , lift refl) =
    sup x f

  split : ∀ {pi} → unindexed WP ε _ W pi → ⟦ wD ⟧Data (a ⊔ b) (unindexed WP ε _ W) pi
  split {((tt , A) , B) , tt} (sup x f) =
    zero , x , (λ s → f s) , lift refl

  -- NEED FUNEXT???
  from∘to : ∀ {pi} (x : unindexed WP ε _ W pi) → from {pi} (to {pi} x) ≡ x
  from∘to {((tt , A) , B) , tt} (sup x f) =
    {!!}

  to∘from : ∀ {pi} (x : μ wD pi) → to {pi} (from {pi} x) ≡ x
  to∘from {((tt , A) , B) , tt} ⟨ zero , x , f , lift refl ⟩ =
    {!!}

  constr-coh : ∀ {pi} (x : ⟦ wD ⟧Data _ (μ wD) pi) → constr (mapData _ _ from wD x) ≡ from ⟨ x ⟩
  constr-coh {((tt , A) , B) , tt} (zero , x , f , lift refl) = refl

  split-coh : ∀ {pi} (x : ⟦ wD ⟧Data _ (μ wD) pi) → split (from {pi} ⟨ x ⟩) ≡ mapData _ _ from wD x
  split-coh {((tt , A) , B) , tt} (zero , x , f , lift refl) = refl

  WHasDesc : HasDesc W
  WHasDesc = record
    { D      = wD
    ; names  = "sup" ∷ []
    ; to     = to
    ; from   = from
    ; to∘from = {!!}
    ; from∘to = {!!}
    ; constr = constr
    ; split  = split
    ; constr-coh = constr-coh
    ; split-coh  = split-coh
    }

  postulate P : ∀ {A : Set a} {B : A → Set b} → W A B → Set

  elimW : ∀ {ℓ} (P : ∀ {A} {B : A → Set b} → W A B → Set ℓ)
        → (∀ {A} {B} a (f : B a → W A B) → (∀ x → P (f x) → P (sup a f)))
        → ∀ {A} {B} → (x : W A B) → P x
  elimW P H x = elim″ WHasDesc P {!H!} x




module Eq {a : Level} where
  data Id (A : Set a) (x : A) : A → Set a where
    refl : Id A x x

  P : Telescope ⊤
  P = ε ⊢ const (Set a) ⊢ proj₂

  I : ExTele P
  I = ε ⊢ proj₁ ∘ proj₁

  eqD : Desc P I a 1
  eqD = var (proj₂ ∘ proj₁) ∷ []

  to : ∀ {pi} → unroll {P} I Id pi → μ eqD pi
  to refl = ⟨ zero , lift refl ⟩

  from : ∀ {pi} → μ eqD pi → unroll {P} I Id pi
  from ⟨ zero , lift refl ⟩ = refl

  constr : ∀ {A} {x} {y} k
         → Extend {P} {I = I} {ℓ₂ = a} (lookup eqD k) (unroll {P} I Id) ((A , x) , tt , y)
         → unroll {P} I Id ((A , x) , y)
  constr zero (lift refl) = refl

  IdHasDesc : HasDesc Id
  IdHasDesc = record
    { D      = eqD
    ; names  = "refl" ∷ []
    ; to     = to
    ; from   = from
    ; constr = constr
    }



module DTree where

  data Tree : Set where
    leaf : Tree
    node : Tree → Tree → Tree

  treeD : DataDesc ε ε lzero 2
  treeD = var (const tt)
        ∷ var (const tt) ⊗ (var (const tt) ⊗ var (const tt))
        ∷ []

  T′ : Σ[ ε ⇒ ε ] → Set
  T′ = unindexed ε ε _ Tree

  -- all of this should be derived very soon
  to : Tree → μ treeD (tt , tt)
  to leaf = ⟨ zero , lift refl ⟩
  to (node a b) = ⟨ suc zero , to a , to b , lift refl ⟩

  from : μ treeD (tt , tt) → Tree
  from ⟨ zero , lift refl ⟩ = leaf
  from ⟨ suc zero , a , b , lift refl ⟩ = node (from a) (from b)

  from∘to : ∀ x → from (to x) ≡ x
  from∘to leaf = refl
  from∘to (node a b) rewrite from∘to a | from∘to b = refl


  -- from : μ natD (tt , tt) → ℕ
  -- from ⟨ zero , lift refl ⟩ = 0
  -- from ⟨ suc zero , x , lift refl ⟩ = suc (from x)

-}
