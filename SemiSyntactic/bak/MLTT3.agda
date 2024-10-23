module MLTT3 where

open import Level
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

variable 
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ' ℓ₁' ℓ₂' ℓ₃' : Level

variable
  A A₁ A₂ A₃ A' A₁' A₂' A₃' : Set ℓ
  a a₁ a₂ a₃ a' a₁' a₂' a₃' : A
  
data Ctx : Setω
variable 
  Γ Γ₁ Γ₂ Γ₃ Γ' Γ₁' Γ₂' Γ₃' : Ctx

data Term (Γ : Ctx) : {ℓ : Level} → Set ℓ → Setω
variable
  T T₁ T₂ T₃ T' T₁' T₂' T₃' : Term Γ A

⟦_⟧ : Term Γ A → A

data Ctx where
  ∅    : Ctx
  _,_  : (Γ : Ctx) {A : Term Γ (Set ℓ)} → 
         ⟦ A ⟧ → Ctx

data _∈_ : Set ℓ → Ctx → Setω where
  here  : {A : Term Γ (Set ℓ)} {a : ⟦ A ⟧} → 
          ⟦ A ⟧ ∈ (Γ , a)
  there : {A : Term Γ (Set ℓ)} {A' : Term Γ (Set ℓ')} {a' : ⟦ A' ⟧} →  
          (⟦ A ⟧) ∈ Γ → 
          (⟦ A ⟧) ∈ (Γ , a')

lookup : A ∈ Γ → A 
lookup {Γ = .(_ , a)} (here {a = a})    = a
lookup {Γ = .(Γ , _)} (there {Γ = Γ} x) = lookup x

data Term Γ where
  `_ : {A : Term Γ (Set ℓ)} → ⟦ A ⟧ ∈ Γ → Term Γ ⟦ A ⟧

  `zero : Term Γ Level
  `suc  : Term Γ Level →  Term Γ Level 
  `Set  : (ℓ : Term Γ Level) → Term Γ (Set (suc ⟦ ℓ ⟧))

  `⊤  : Term Γ Set
  `tt : Term Γ ⟦ `⊤ {Γ} ⟧

  `∀_∶_ : 
    (A : Term Γ (Set ℓ)) → 
    ({a : ⟦ A ⟧} → (Term Γ (Set ℓ'))) → 
    Term Γ (Set (ℓ ⊔ ℓ'))
  `λ : 
    {A : Term Γ (Set ℓ)} 
    {B : ({a : ⟦ A ⟧} → (Term Γ (Set ℓ')))} →
    ({a : ⟦ A ⟧} → Term Γ (⟦ B {a} ⟧)) → 
    Term Γ ((a : ⟦ A ⟧) → ⟦ B {a} ⟧)
  
  _·_ :   
    {A : Term Γ (Set ℓ)} 
    {B : ({a : ⟦ A ⟧} → (Term Γ (Set ℓ')))} →
    Term Γ (∀ (a : ⟦ A ⟧) → ⟦ B {a} ⟧) →
    (T : Term Γ (⟦ A ⟧)) →
    Term Γ ⟦ B {⟦ T ⟧} ⟧


⟦ ` x ⟧      = lookup x
⟦ `zero ⟧    = zero
⟦ `suc ℓ ⟧   = suc ⟦ ℓ ⟧
⟦ `Set ℓ ⟧   = Set ⟦ ℓ ⟧
⟦ `⊤ ⟧       = ⊤
⟦ `tt ⟧      = tt
⟦ `∀ A ∶ B ⟧ = ∀ (a : ⟦ A ⟧) → ⟦ B {a} ⟧
⟦ `λ e ⟧     = λ x → ⟦ e ⟧
⟦ e₁ · e₂ ⟧  = ⟦ e₁ ⟧ ⟦ e₂ ⟧

data _⟶_ : Term Γ A → Term Γ A → Setω where 
  β : ∀ {A : Term Γ (Set ℓ)} {B : ({a : ⟦ A ⟧} → (Term Γ (Set ℓ')))} 
        {e : {a : ⟦ A ⟧} → Term Γ (⟦ B {a} ⟧)} 
        {e' : Term Γ (⟦ A ⟧)} → 
    (_·_ {A = A} {B = B {a = ⟦ e' ⟧}} (`λ {A = A} {B = B {a = ⟦ e' ⟧}} e) e') ⟶ e {⟦ e' ⟧}
-- Ren : Ctx → Ctx → Setω
-- Ren Γ₁ Γ₂ = ∀ {ℓ} {A : Term Γ₁ (Set ℓ)} → ⟦ A ⟧ ∈ Γ₁ → ⟦ A ⟧ ∈ Γ₂
-- 
-- variable
--   ρ ρ₁ ρ₂ ρ₃ ρ' ρ₁' ρ₂' ρ₃' : Ren Γ₁ Γ₂ 
-- 
-- idᵣ : Ren Γ Γ
-- idᵣ x = x
-- 
-- wkᵣ : Ren Γ (Γ , a)
-- wkᵣ = there 
-- 
-- dropᵣ : Ren (Γ₁ , a) Γ₂ → Ren Γ₁ Γ₂
-- dropᵣ ρ x = ρ (there x)
-- 
-- _∷ᵣ_ : a ∈ Γ₂ → Ren Γ₁ Γ₂ → Ren (Γ₁ , a) Γ₂
-- (x ∷ᵣ ρ) here      = x 
-- (_ ∷ᵣ ρ) (there x) = ρ x 
-- 
-- _≫ᵣᵣ_ : Ren Γ₁ Γ₂ → Ren Γ₂ Γ₃ → Ren Γ₁ Γ₃
-- (ρ₁ ≫ᵣᵣ ρ₂) x = ρ₂ (ρ₁ x)
-- 
-- _↑ᵣ_ : Ren Γ₁ Γ₂ → (a : A) → Ren (Γ₁ , a) (Γ₂ , a)
-- ρ ↑ᵣ _ = here ∷ᵣ (ρ ≫ᵣᵣ wkᵣ)
-- -- 
-- _⋯ᵣ_ : Term Γ₁ A → (ρ : Ren Γ₁ Γ₂) → Term Γ₂ A
-- (` x)      ⋯ᵣ ρ = ` ρ {A = {! A  !}} x
-- `zero      ⋯ᵣ ρ  = `zero
-- `suc ℓ     ⋯ᵣ ρ = `suc (ℓ ⋯ᵣ ρ)
-- `Set ℓ     ⋯ᵣ ρ = {! `Set (ℓ ⋯ᵣ ρ)  !}
-- `⊤         ⋯ᵣ ρ = `⊤
-- `tt        ⋯ᵣ ρ = `tt
-- (`∀ A ∶ B) ⋯ᵣ ρ = `∀ A ⋯ᵣ ρ ∶ (B ⋯ᵣ {! ρ ↑ᵣ ?  !})
-- `λ e       ⋯ᵣ ρ = {!   !}
-- (e₁ · e₂)  ⋯ᵣ ρ = {!   !}

  