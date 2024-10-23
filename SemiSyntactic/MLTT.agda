module MLTT where

open import Level
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

variable 
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ' ℓ₁' ℓ₂' ℓ₃' : Level

variable
  A A₁ A₂ A₃ A' A₁' A₂' A₃' : Set ℓ
  a a₁ a₂ a₃ a' a₁' a₂' a₃' : A
  
data Term : {ℓ : Level} → Set ℓ → Setω
variable
  T T₁ T₂ T₃ T' T₁' T₂' T₃' : Term A

⟦_⟧ : Term A → A

data Term where
  `zero : Term Level
  `suc  : Term Level →  Term Level 
  `Set  : (ℓ : Term Level) → Term (Set (suc ⟦ ℓ ⟧))

  `⊤  : Term Set
  `tt : Term ⟦ `⊤ ⟧

  `∀_∶_ : 
    (A : Term (Set ℓ)) → 
    ({a : ⟦ A ⟧} → (Term (Set ℓ'))) → 
    Term (Set (ℓ ⊔ ℓ'))
  `λ : 
    {A : Term (Set ℓ)} 
    {B : ({a : ⟦ A ⟧} → (Term (Set ℓ')))} →
    ({a : ⟦ A ⟧} → Term (⟦ B {a} ⟧)) → 
    Term ((a : ⟦ A ⟧) → ⟦ B {a} ⟧)
  
  _·_ :   
    {A : Term (Set ℓ)} 
    {B : ({a : ⟦ A ⟧} → (Term (Set ℓ')))} →
    Term (∀ (a : ⟦ A ⟧) → ⟦ B {a} ⟧) →
    (T : Term (⟦ A ⟧)) →
    Term ⟦ B {⟦ T ⟧} ⟧


⟦ `zero ⟧    = zero
⟦ `suc ℓ ⟧   = suc ⟦ ℓ ⟧
⟦ `Set ℓ ⟧   = Set ⟦ ℓ ⟧
⟦ `⊤ ⟧       = ⊤
⟦ `tt ⟧      = tt
⟦ `∀ A ∶ B ⟧ = ∀ (a : ⟦ A ⟧) → ⟦ B {a} ⟧
⟦ `λ e ⟧     = λ x → ⟦ e ⟧
⟦ e₁ · e₂ ⟧  = ⟦ e₁ ⟧ ⟦ e₂ ⟧

data _⟶_ : Term A → Term A → Setω where 
  β : ∀ {A : Term (Set ℓ)} {B : ({a : ⟦ A ⟧} → (Term (Set ℓ')))} 
        {e : {a : ⟦ A ⟧} → Term (⟦ B {a} ⟧)} 
        {e' : Term (⟦ A ⟧)} → 
    (_·_ {A = A} {B = B {a = ⟦ e' ⟧}} (`λ {A = A} {B = B {a = ⟦ e' ⟧}} e) e') ⟶ e {⟦ e' ⟧}

-- Ren : Ctx → Ctx → Setω
-- Ren₁₂ = ∀ {ℓ} {A : Term₁ (Set ℓ)} → ⟦ A ⟧ ∈₁ → ⟦ A ⟧ ∈₂
-- 
-- variable
--   ρ ρ₁ ρ₂ ρ₃ ρ' ρ₁' ρ₂' ρ₃' : Ren₁₂ 
-- 
-- idᵣ : Ren
-- idᵣ x = x
-- 
-- wkᵣ : Ren (Γ , a)
-- wkᵣ = there 
-- 
-- dropᵣ : Ren (Γ₁ , a)₂ → Ren₁₂
-- dropᵣ ρ x = ρ (there x)
-- 
-- _∷ᵣ_ : a ∈₂ → Ren₁₂ → Ren (Γ₁ , a)₂
-- (x ∷ᵣ ρ) here      = x 
-- (_ ∷ᵣ ρ) (there x) = ρ x 
-- 
-- _≫ᵣᵣ_ : Ren₁₂ → Ren₂₃ → Ren₁₃
-- (ρ₁ ≫ᵣᵣ ρ₂) x = ρ₂ (ρ₁ x)
-- 
-- _↑ᵣ_ : Ren₁₂ → (a : A) → Ren (Γ₁ , a) (Γ₂ , a)
-- ρ ↑ᵣ _ = here ∷ᵣ (ρ ≫ᵣᵣ wkᵣ)
-- -- 
-- _⋯ᵣ_ : Term₁ A → (ρ : Ren₁₂) → Term₂ A
-- (` x)      ⋯ᵣ ρ = ` ρ {A = {! A  !}} x
-- `zero      ⋯ᵣ ρ  = `zero
-- `suc ℓ     ⋯ᵣ ρ = `suc (ℓ ⋯ᵣ ρ)
-- `Set ℓ     ⋯ᵣ ρ = {! `Set (ℓ ⋯ᵣ ρ)  !}
-- `⊤         ⋯ᵣ ρ = `⊤
-- `tt        ⋯ᵣ ρ = `tt
-- (`∀ A ∶ B) ⋯ᵣ ρ = `∀ A ⋯ᵣ ρ ∶ (B ⋯ᵣ {! ρ ↑ᵣ ?  !})
-- `λ e       ⋯ᵣ ρ = {!   !}
-- (e₁ · e₂)  ⋯ᵣ ρ = {!   !}

  