open import Generics.Prelude
open import Generics.Parametrized.Telescope
open import Generics.Parametrized.Desc
open import Relation.Binary.PropositionalEquality


natD : DDesc ε ε 2
natD = var (const tt)
     ∷ ((var (const tt)) ⊗ var (const tt))
     ∷ []

nat : Set
nat = μ natD (tt , tt)

ze : nat
ze = ⟨ zero , lift refl ⟩

su : nat → nat
su n = ⟨ suc zero , n , lift refl ⟩



vecD : ∀ {a} → DDesc (ε ▷ const (Set a)) (ε ▷ const ℕ) 2
vecD = var (const 0)
     ∷ π (const ℕ) (π proj₁ (var (proj₁ ∘ proj₂) ⊗ var (suc ∘ proj₁ ∘ proj₂)))
     ∷ []

vec : ∀ {a} → Set a → ℕ → Set a
vec A n = μ vecD (A , n)


nil : ∀ {a} {A : Set a} → vec A 0
nil = ⟨ zero , lift refl ⟩

cons : ∀ {a} {A : Set a} {n} → A → vec A n → vec A (suc n)
cons x xs = ⟨ suc zero , _ , x , xs , lift refl ⟩



wD : ∀ {a} {b} → DDesc (ε ▷ const (Set a) ▷ λ p → proj₂ p → Set b) ε 1
wD = π (proj₁ ∘ proj₁) (π (λ p → proj₂ (proj₁ p) (proj₂ p)) (var (const tt)) ⊗ (var (const tt)))
   ∷ []

W : ∀ {a b} (A : Set a) (B : A → Set b) → Set (a ⊔ b)
W A B = μ wD ((A , B) , tt)

sup : ∀ {a b} {A : Set a} {B : A → Set b} (x : A) → (B x → W A B) → W A B
sup x g = ⟨ zero , x , g , lift refl ⟩



roseD : ∀ {a} → DDesc (ε ▷ const (Set a)) ε 1
roseD = π proj₁ (π (const ℕ) (π (Fin ∘ proj₂ ∘ proj₂) (var (const tt)) ⊗ (var (const tt))))
      ∷ []

rose : ∀ {a} → Set a → Set a
rose A = μ roseD (A , tt)

node : ∀ {a} {A : Set a} {n} → A → (Fin n → rose A) → rose A
node x xs = ⟨ zero , x , _ , xs , lift refl ⟩
