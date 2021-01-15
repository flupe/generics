module Generics.Parametrized.Desc where

open import Data.Unit.Base
open import Data.Product
open import Generics.Telescope
open import Agda.Primitive
open import Data.Fin.Base hiding (lift)
open import Agda.Builtin.Equality
open import Level hiding (zero; suc)
open import Data.Nat.Base using (ℕ; suc; zero)
open import Data.Vec.Base
open import Function.Base


data ConDesc {gs vs is} ℓ (P : Tel′ gs) (V : Tel ⟦ P ⟧′ vs) (I : Tel ⟦ P ⟧′ is)
           : Set (lsuc ℓ ⊔ telLevel is ⊔ telLevel vs ⊔ telLevel gs) where
  κ : (f : ((g , _) : Σ (⟦ P ⟧ tt) ⟦ V ⟧) → ⟦ I ⟧ g) → ConDesc ℓ P V I
  ι : (f : ((g , _) : Σ (⟦ P ⟧ tt) ⟦ V ⟧) → Σ ⟦ P ⟧′ ⟦ I ⟧) → ConDesc ℓ P V I → ConDesc ℓ P V I
  σ : (S : Σ (⟦ P ⟧ tt) ⟦ V ⟧ → Set ℓ) → ConDesc ℓ P (V ▷ S) I → ConDesc ℓ P V I

-- todo: add relevance & visibility to arguments

⟦_⟧C : ∀ {gs vs is ℓ}
       {P : Tel′ gs}
       {V : Tel ⟦ P ⟧′ vs}
       {I : Tel ⟦ P ⟧′ is}
     → ConDesc ℓ P V I
     → (Σ ⟦ P ⟧′ ⟦ I ⟧ → Set (lsuc (ℓ ⊔ telLevel is)))
     → (Σ[ p ∈ ⟦ P ⟧′ ] (⟦ V ⟧ p × ⟦ I ⟧ p) → Set (lsuc (ℓ ⊔ telLevel is)))

⟦ κ f   ⟧C X (p , v , i) = Lift _ (i ≡ f (p , v))
⟦ ι f C ⟧C X (p , v , i) = X (f (p , v)) × ⟦ C ⟧C X (p , v , i)
⟦ σ S C ⟧C X (p , v , i) = Σ[ s ∈ S (p , v) ] ⟦ C ⟧C X (p , (v , s) , i)


Desc : ∀ {ps is} ℓ (P : Tel′ ps) (I : Tel ⟦ P ⟧′ is) → ℕ → Set _
Desc ℓ P I = Vec (ConDesc ℓ P * I)

⟦_⟧D : ∀ {ps is ℓ n}
       {P : Tel′ ps}
       {I : Tel ⟦ P ⟧′ is}
     → Desc ℓ P I n
     → (Σ ⟦ P ⟧′ ⟦ I ⟧ → Set (lsuc (ℓ ⊔ telLevel is)))
     → (Σ ⟦ P ⟧′ ⟦ I ⟧ → Set (lsuc (ℓ ⊔ telLevel is)))

⟦_⟧D {n = n} D X (p , i) = Σ[ k ∈ Fin n ] ⟦ lookup D k ⟧C X (p , tt , i)


data μ {ps is ℓ n} {P : Tel′ ps} {I : Tel ⟦ P ⟧′ is} (D : Desc ℓ P I n) (gi : Σ ⟦ P ⟧′ ⟦ I ⟧) : Set _ where
  ⟨_⟩ : ⟦ D ⟧D (μ D) gi → μ D gi


private
  module Example where

    natD : Desc lzero * * 2
    natD = κ (const tt)
         ∷ ι (const (tt , tt)) (κ (const tt))
         ∷ []

    -- sadly it's in set₁
    nat : Set₁
    nat = μ natD (tt , tt)

    ze : nat
    ze = ⟨ zero , lift refl ⟩

    su : nat → nat
    su n = ⟨ suc zero , n , lift refl ⟩


    listD : Desc lzero (* ▷ const Set) * 2
    listD = κ (const tt)
          ∷ σ (λ ((_ , A) , _) → A) (ι (λ (p , v) → p , tt) (κ (const tt)))
          ∷ []

    list : Set → Set₁
    list A = μ listD ((tt , A) , tt)

    nil : ∀ {A} → list A
    nil = ⟨ zero , lift refl ⟩

    cons : ∀ {A} → A → list A → list A
    cons x xs = ⟨ suc zero , x , xs , lift refl ⟩


    finD : Desc lzero * (* ▷ const ℕ) 2
    finD = σ (const ℕ) (κ (λ (_ , (_ , n)) → tt , suc n))
         ∷ σ (const ℕ) (ι (λ (_ , (_ , n)) → tt , tt , n) (κ λ (_ , (_ , n)) → tt , suc n))
         ∷ []

    fin : ℕ → Set₁
    fin n = μ finD (tt , (tt , n))

    z : ∀ {n} → fin (suc n)
    z {n} = ⟨ zero , n , lift refl ⟩

    s : ∀ {n} → fin n → fin (suc n)
    s f = ⟨ suc zero , _ , f , lift refl ⟩


    vecD : Desc lzero (* ▷ const Set) (* ▷ const ℕ) 2
    vecD = κ (const (tt , zero))
         ∷ σ (λ ((_ , A) , _) → A) (σ (const ℕ) (ι (λ (p , _ , n) → p , tt , n) (κ λ (_ , _ , n) → tt , (suc n))))
         ∷ []

    vec : Set → ℕ → Set₁
    vec A n = μ vecD ((tt , A) , tt , n)

    vnil : ∀ {A} → vec A 0
    vnil = ⟨ zero , lift refl ⟩

    vcons : ∀ {A n} → A → vec A n → vec A (suc n)
    vcons x xs = ⟨ suc zero , x , _ , xs , lift refl ⟩
