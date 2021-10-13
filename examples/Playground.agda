
open import Generics.Prelude hiding (lookup)
open import Generics.Telescope
open import Generics.Desc
open import Generics.HasDesc

open import Agda.Primitive
open import Agda.Builtin.Nat

natD : HasDesc {ε} {ε} {lzero} Nat
natD = record { NatHasDesc } where
  module NatHasDesc where
    n = 2
    D = (var _) ∷ (var _ ⊗ var _) ∷ []
    names = "zero" ∷ "suc" ∷ []

    to : Nat → μ D _
    to zero    = ⟨ zero            , lift refl ⟩
    to (suc n) = ⟨ suc zero , to n , lift refl ⟩

    from : μ D _ → Nat
    from ⟨ zero         , _ ⟩ = zero
    from ⟨ suc zero , x , _ ⟩ = suc (from x)

    constr : ⟦ D ⟧Data lzero (λ _ → ℕ) _ → ℕ
    constr (zero     ,     _) = zero
    constr (suc zero , n , _) = suc n

    split : ℕ → ⟦ D ⟧Data lzero (λ _ → ℕ) _
    split zero    = zero           , (lift refl)
    split (suc n) = (suc zero) , n , (lift refl)

    from∘to : (x : ℕ) → from (to x) ≡ x
    from∘to zero    = refl
    from∘to (suc x) = cong suc (from∘to x)

    to∘from : (x : μ D _) → to (from x) ≡ x
    to∘from ⟨ zero         , lift refl ⟩ = refl
    to∘from ⟨ suc zero , x , lift refl ⟩ =
      cong (λ x → ⟨ suc zero , x , lift refl ⟩) (to∘from x)

    constr-coh : (x : ⟦ D ⟧Data lzero (μ D) _) →
                   constr (mapData lzero lzero from D x) ≡ from ⟨ x ⟩
    constr-coh (zero         , lift refl) = refl
    constr-coh (suc zero , x , lift refl) = cong suc refl

    split-coh : (x : ⟦ D ⟧Data lzero (μ D) _) →
                  split (from ⟨ x ⟩) ≡ mapData lzero lzero from D x
    split-coh (zero         , lift refl) = refl
    split-coh (suc zero , x , lift refl) = refl

open import Generics.Constructions.Case {ε} {ε} {lzero} {Nat} natD

caseNat = deriveCase

open import Generics.Constructions.Elim {ε} {ε} {lzero} {Nat} natD


elimNat : ∀ {ℓ} (P : ℕ → Set ℓ) → P 0 → (∀ n → P n → P (suc n))
        → ∀ n → P n
elimNat = deriveElim

plus : ℕ → ℕ → ℕ
plus x = elimNat (λ _ → ℕ) x (λ _ y → suc y)

plus-test₁ : plus 1 1 ≡ 2
plus-test₁ = refl

plus-test₂ : (λ x → plus x 1) ≡ suc
plus-test₂ = refl

plus-test₃ : ∀ x y → plus x (suc y) ≡ suc (plus x y)
plus-test₃ x y = {!refl!} -- does not hold definitionally (yet)

elim-test₁ : ∀ {ℓ} (P : ℕ → Set ℓ) (P0 : P 0) (PS : ∀ n → P n → P (suc n))
           → elimNat P P0 PS zero ≡ P0
elim-test₁ P P0 PS = refl

elim-test₂ : ∀ {ℓ} (P : ℕ → Set ℓ) (P0 : P 0) (PS : ∀ n → P n → P (suc n))
           → ∀ n → elimNat P P0 PS (suc n) ≡ PS n (elimNat P P0 PS n)
elim-test₂ P P0 PS n = {!refl!} -- does not hold definitionally (yet)
