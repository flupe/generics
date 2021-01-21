module Simple where

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Data.Empty
open import Agda.Primitive

open import Data.Vec.Base hiding (map)
open import Data.Vec.Relation.Unary.All hiding (map)
open import Data.Fin.Base hiding (_≤_; _+_; lift)
open import Data.Nat.Base
open import Relation.Binary.PropositionalEquality
open import Function.Bundles
open import Data.Product.Properties
open import Level hiding (zero; suc)
open import Function.Base using (const)

open import Generics.Simple.Desc
open import Generics.Simple.HasDesc2
open import Generics.Simple.Constructions.Elim
open import Generics.Simple.Constructions.Case

module nat where

  natD : Desc ⊤ lzero 2
  natD = κ tt ∷ ι tt (κ tt) ∷ []
  
  to : ℕ → μ natD tt
  to zero    = ⟨ zero , lift refl ⟩
  to (suc n) = ⟨ suc zero , to n , lift refl ⟩
  
  from : μ natD tt → ℕ
  from ⟨ zero , lift refl ⟩ = 0
  from ⟨ suc zero , n , lift refl ⟩ = suc (from n)
  
  to∘from : ∀ x → to (from x) ≡ x
  to∘from ⟨ zero , lift refl ⟩ = refl
  to∘from ⟨ suc zero , n , lift refl ⟩ rewrite to∘from n = refl
  
  from∘to : ∀ x → from (to x) ≡ x
  from∘to zero = refl
  from∘to (suc n) = cong suc (from∘to n)
  
  constr : (x : ⟦ natD ⟧D (const ℕ) tt) → ℕ
  constr (zero , lift refl) = 0
  constr (suc zero , n , lift refl) = suc n
  
  constr-coh  : (x : μ natD tt) → constr (mapD from {natD} (unwrap x)) ≡ from x
  constr-coh ⟨ zero , lift refl ⟩ = refl
  constr-coh ⟨ suc zero , n , lift refl ⟩ = refl
  
  dissect : ℕ → ⟦ natD ⟧D (const ℕ) tt
  dissect zero = zero , lift refl
  dissect (suc n) = suc zero , n , lift refl
  
  dissect-coh : (x : μ natD tt) → dissect (from x) ≡ mapD from {natD} (unwrap x)
  dissect-coh ⟨ zero , lift refl ⟩ = refl
  dissect-coh ⟨ suc zero , n , lift refl ⟩ = refl
  
  instance
    natHasDesc : HasDesc {I = ⊤} (const ℕ)
    natHasDesc = record
      { D           = natD
      ; names       = "zero" ∷ "suc" ∷ []
      ; to          = to
      ; from        = from
      ; to∘from     = to∘from
      ; from∘to     = from∘to
      ; constr      = constr
      ; dissect     = dissect
      ; constr-coh  = constr-coh
      ; dissect-coh = dissect-coh
      }
  
  nat-elim : ∀ {i} (P : ℕ → Set i) → Elim (λ _ → ℕ) P
  nat-elim P = elim _ _
  
  pattern refl′ = lift refl
  
  thm : ∀ n → n ≤ n + 1
  thm = nat-elim (λ n → n ≤ n + 1)
          (λ where {tt} {refl′    } _          → z≤n     )
          (λ where {tt} {n , refl′} (n≤sn , _) → s≤s n≤sn)

module vec where

  private
    variable
      a : Level
      A : Set a

  vecD : ∀ {a} (A : Set a) → Desc ℕ a 2
  vecD {a} A = κ 0
             ∷ σ[ x ∈ A ] σ[ (lift n) ∈ Lift a ℕ ] ι n (κ (suc n))
             ∷ []

  to : ∀ {n} → Vec A n → μ (vecD A) n
  to [] = ⟨ zero , lift refl ⟩
  to (x ∷ xs) = ⟨ suc zero , x , _ , to xs , lift refl ⟩

  from : ∀ {n} → μ (vecD A) n → Vec A n
  from ⟨ zero , lift refl ⟩ = []
  from ⟨ suc zero , x , n , xs , lift refl ⟩ = x ∷ from xs

  from∘to : ∀ {n} (x : Vec A n) → from (to x) ≡ x
  from∘to [] = refl
  from∘to (x ∷ xs) rewrite from∘to xs = refl

  to∘from : ∀ {n} (x : μ (vecD A) n) → to (from x) ≡ x
  to∘from ⟨ zero , lift refl ⟩ = refl
  to∘from ⟨ suc zero , x , n , xs , lift refl ⟩
    rewrite to∘from xs = refl

  constr : ∀ {n} (x : ⟦ vecD A ⟧D (Vec A) n) → Vec A n
  constr (zero , lift refl) = []
  constr (suc zero , x , _ , xs , lift refl) = x ∷ xs
  
  constr-coh : ∀ {n} (x : μ (vecD A) n) → constr (mapD from {vecD A} (unwrap x)) ≡ from x
  constr-coh ⟨ zero , lift refl ⟩ = refl
  constr-coh ⟨ suc zero , x , _ , xs , lift refl ⟩ = refl
  
  dissect : ∀ {n} → Vec A n → ⟦ vecD A ⟧D (Vec A) n
  dissect [] = zero , lift refl
  dissect (x ∷ xs) = suc zero , x , _ , xs , lift refl

  dissect-coh : ∀ {n} (x : μ (vecD A) n) → dissect (from x) ≡ mapD from {vecD A} (unwrap x)
  dissect-coh ⟨ zero , lift refl ⟩ = refl
  dissect-coh ⟨ suc zero , x , _ , xs , lift refl ⟩ = refl


  instance
    vecHasD : ∀ {a} {A : Set a} → HasDesc (Vec A)
    vecHasD {A = A} = record
      { D           = vecD A
      ; names       = "[]" ∷ "_∷_" ∷ []
      ; to          = to
      ; from        = from
      ; to∘from     = to∘from
      ; from∘to     = from∘to
      ; constr      = constr
      ; dissect     = dissect
      ; constr-coh  = constr-coh
      ; dissect-coh = dissect-coh
      }

  vec-elim : ∀ {a} {A : Set a} {c} (P : ∀ {n} → Vec A n → Set c) → Elim (Vec A) P
  vec-elim P = elim _ _

  vec-case : ∀ {a} {A : Set a} {c} (P : ∀ {n} → Vec A n → Set c) → Case (Vec A) P
  vec-case {A = A} P = case (Vec A) P

  is-[] : ∀ {n} → Vec A n → Set
  is-[] = vec-case (const Set) (const ⊤) (const ⊥)

  map : ∀ {a b} {A : Set a} {B : Set b} (f : A → B)
      → ∀ {n} → Vec A n → Vec B n
  map {B = B} f = vec-elim (λ {n} _ → Vec B n)
                      (λ where .{0} {lift refl} (lift tt) → [])
                      (λ where  .{_} {x , _ , _ , lift refl} (xs′ , _) → f x ∷ xs′)

  t₁ : ∀ {a} {A : Set a}
     → is-[] ([] {A = A}) ≡ ⊤
  t₁ = refl

  t₂ : ∀ {a} {A : Set a} (x : A)
     → is-[] (x ∷ []) ≡ ⊥
  t₂ x = refl
