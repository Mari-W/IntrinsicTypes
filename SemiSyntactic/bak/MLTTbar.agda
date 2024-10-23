module MLTTbar where

open import Level
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

variable 
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ' ℓ₁' ℓ₂' ℓ₃' : Level

variable
  ⟦A⟧ ⟦A⟧₁ ⟦A⟧₂ ⟦A⟧₃ ⟦A⟧' ⟦A⟧₁' ⟦A⟧₂' ⟦A⟧₃' : Set ℓ
  
data Ctx : Setω
variable 
  Γ Γ₁ Γ₂ Γ₃ Γ' Γ₁' Γ₂' Γ₃' : Ctx

data Term : (Γ : Ctx) → {ℓ : Level} → Set ℓ → Setω
variable
  T T₁ T₂ T₃ T' T₁' T₂' T₃' : Term Γ ⟦A⟧

_⟦_⟧ : (Γ : Ctx) → Term Γ ⟦A⟧ → ⟦A⟧

data Ctx where
  ∅    : Ctx
  _,_  : (Γ : Ctx) {A : Term Γ (Set ℓ)} → 
         Γ ⟦ A ⟧ → Ctx

data _∈_ : Set ℓ → Ctx → Setω where
  here  : {A : Term Γ (Set ℓ)} {⟦A⟧ : Γ ⟦ A ⟧} → 
          (Γ ⟦ A ⟧) ∈ (Γ , ⟦A⟧)
  there : {A : Term Γ (Set ℓ)} {A' : Term Γ (Set ℓ')} {⟦A⟧' : Γ ⟦ A' ⟧} →  
          (Γ ⟦ A ⟧) ∈ Γ → 
          (Γ ⟦ A ⟧) ∈ (Γ , ⟦A⟧')

lookup : (Γ : Ctx) → ⟦A⟧ ∈ Γ → ⟦A⟧ 
lookup .(_ , ⟦A⟧) (here {⟦A⟧ = ⟦A⟧}) = ⟦A⟧
lookup .(Γ , _) (there {Γ} x) = lookup Γ x

data Term where
  `_ : ⟦A⟧ ∈ Γ → Term Γ ⟦A⟧ 

  `⊤  : Term Γ Set
  `tt : Term Γ ⊤

  `∀_∶_ : 
    (A : Term Γ (Set ℓ)) → 
    ({⟦A⟧ : Γ ⟦ A ⟧} → (Term (Γ , ⟦A⟧) (Set ℓ'))) → 
    Term Γ (Set (ℓ ⊔ ℓ'))
  `λ : 
    {A : Term Γ (Set ℓ)} 
    {B : ({⟦A⟧ : _ ⟦ A ⟧} → (Term (Γ , ⟦A⟧) (Set ℓ')))} →
    ({⟦A⟧ : _ ⟦ A ⟧} → Term (Γ , ⟦A⟧) ((Γ , ⟦A⟧) ⟦ B ⟧)) → 
    Term Γ (∀ (⟦A⟧ : (_ ⟦ A ⟧)) → (Γ , ⟦A⟧) ⟦ B ⟧)
  
  _·_ :   
    {A : Term Γ (Set ℓ)} 
    {B : ({⟦A⟧ : Γ ⟦ A ⟧} → (Term (Γ , ⟦A⟧) (Set ℓ')))} →
    Term Γ (∀ (⟦A⟧ : (Γ ⟦ A ⟧)) → (Γ , ⟦A⟧) ⟦ B ⟧) →
    (T : Term Γ (Γ ⟦ A ⟧)) →
    Term Γ ((Γ , (Γ ⟦ T ⟧)) ⟦ B {Γ ⟦ T ⟧} ⟧)

  _`≡_ : 
    {A : Term Γ (Set ℓ)} →
    Term Γ (Γ ⟦ A ⟧) → 
    Term Γ (Γ ⟦ A ⟧) →
    Term Γ (Set ℓ)
  `refl : 
    {A : Term Γ (Set ℓ)} →
    {x : Term Γ (Γ ⟦ A ⟧)} →
    Term Γ ((Γ ⟦ x ⟧) ≡ (Γ ⟦ x ⟧))
    
  `zero : Term Γ Level
  `suc  : Term Γ Level →  Term Γ Level 
  `Set  : (ℓ : Term Γ Level) → Term Γ (Set (Γ ⟦ `suc ℓ ⟧))

Γ ⟦ ` x ⟧      = lookup Γ x 
Γ ⟦ `⊤ ⟧       = ⊤
Γ ⟦ `tt ⟧      = tt
Γ ⟦ `∀ A ∶ B ⟧ = ∀ (⟦A⟧ : (Γ ⟦ A ⟧)) → (Γ , ⟦A⟧) ⟦ B ⟧ 
Γ ⟦ `λ e ⟧     = λ ⟦e⟧ → (Γ , ⟦e⟧) ⟦ e ⟧
Γ ⟦ e₁ · e₂ ⟧  = (Γ ⟦ e₁ ⟧) (Γ ⟦ e₂ ⟧)
Γ ⟦ e₁ `≡ e₂ ⟧ = (Γ ⟦ e₁ ⟧) ≡ (Γ ⟦ e₂ ⟧)
Γ ⟦ `refl ⟧    = refl
Γ ⟦ `zero ⟧    = zero
Γ ⟦ `suc ℓ ⟧   = suc (Γ ⟦ ℓ ⟧)
Γ ⟦ `Set ℓ ⟧   = Set (Γ ⟦ ℓ ⟧)

-- Ren : Ctx → Ctx → Setω
-- Ren Γ₁ Γ₂ = ∀ {ℓ} {⟦A⟧ : Set ℓ} → ⟦A⟧ ∈ Γ₁ → ⟦A⟧ ∈ Γ₂
-- 
-- variable
--   ρ ρ₁ ρ₂ ρ₃ ρ' ρ₁' ρ₂' ρ₃' : Ren Γ₁ Γ₂ 
-- 
-- idᵣ : Ren Γ Γ
-- idᵣ x = x
-- 
-- wkᵣ : {A : Term Γ (Set ℓ)} → {⟦A⟧ : Γ ⟦ A ⟧} → Ren Γ (_,_ Γ {A = A} ⟦A⟧)
-- wkᵣ {A = A} {⟦A⟧ = ⟦A⟧} {⟦A⟧ = ⟦A⟧₁} = there {A = {!   !}}
-- 
-- -- dropᵣ : Ren (Γ₁ , ⟦A⟧) Γ₂ → Ren Γ₁ Γ₂
-- -- dropᵣ ρ x = ρ (there x)
-- 
-- _⟪_⟫ : Ctx → Ren Γ₁ Γ₂ → Ctx
-- _⟪_⟫ {Γ₁ = ∅}      Γ ρ   = ∅
-- _⟪_⟫ {Γ₁ = Γ₁ , ⟦A⟧} Γ ρ = {!   !}
  