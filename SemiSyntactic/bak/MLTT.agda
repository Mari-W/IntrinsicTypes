module MLTT where

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

lookup : {Γ : Ctx} → A ∈ Γ → A 
lookup {Γ = .(_ , a)} (here {a = a}) = a
lookup {Γ = .(Γ , _)} (there {Γ} x) = lookup x

data Term Γ where
  `_ : A ∈ Γ → Term Γ A 

  `zero : Term Γ Level
  `suc  : Term Γ Level →  Term Γ Level 
  `Set  : (ℓ : Term Γ Level) → Term Γ (Set (⟦ `suc ℓ ⟧))

  `⊤  : Term Γ Set
  `tt : Term Γ ⟦ `⊤ {Γ} ⟧

  `∀_∶_ : 
    (A : Term Γ (Set ℓ)) → 
    ({a : ⟦ A ⟧} → (Term (Γ , a) (Set ℓ'))) → 
    Term Γ (Set (ℓ ⊔ ℓ'))
  `λ : 
    {A : Term Γ (Set ℓ)} 
    {B : ({A : ⟦ A ⟧} → (Term (Γ , A) (Set ℓ')))} →
    ({a : ⟦ A ⟧} → Term (Γ , a) (⟦ B {a} ⟧)) → 
    Term Γ ⟦ `∀ A ∶ B ⟧
  
  _·_ :   
    {A : Term Γ (Set ℓ)} 
    {B : ({a : ⟦ A ⟧} → (Term (Γ , a) (Set ℓ')))} →
    Term Γ (∀ (a : ⟦ A ⟧) → ⟦ B {a} ⟧) →
    (T : Term Γ (⟦ A ⟧)) →
    Term Γ ⟦ B {⟦ T ⟧} ⟧

  _`≡_ : 
    {A : Term Γ (Set ℓ)} →
    Term Γ ⟦ A ⟧ → 
    Term Γ ⟦ A ⟧ →
    Term Γ (Set ℓ)
  `refl : 
    {A : Term Γ (Set ℓ)} →
    {a : Term Γ ⟦ A ⟧} →
    Term Γ (⟦ a ⟧ ≡ ⟦ a ⟧)
  
⟦ ` x ⟧      = lookup x
⟦ `zero ⟧    = zero
⟦ `suc ℓ ⟧   = suc ⟦ ℓ ⟧
⟦ `Set ℓ ⟧   = Set ⟦ ℓ ⟧
⟦ `⊤ ⟧       = ⊤
⟦ `tt ⟧      = tt
⟦ `∀ A ∶ B ⟧ = ∀ (a : ⟦ A ⟧) → ⟦ B {a} ⟧
⟦ `λ e ⟧     = λ x → ⟦ e ⟧ 
⟦ e₁ · e₂ ⟧  = ⟦ e₁ ⟧ ⟦ e₂ ⟧
⟦ e₁ `≡ e₂ ⟧ = ⟦ e₁ ⟧ ≡ ⟦ e₂ ⟧
⟦ `refl ⟧    = refl

--Ren : Ctx → Ctx → Setω
--Ren Γ₁ Γ₂ = ∀ {ℓ} {A : Set ℓ} → A ∈ Γ₁ → A ∈ Γ₂
--
--variable
--  ρ ρ₁ ρ₂ ρ₃ ρ' ρ₁' ρ₂' ρ₃' : Ren Γ₁ Γ₂ 
--
--idᵣ : Ren Γ Γ
--idᵣ x = x
--
--wkᵣ : {A : Term Γ (Set ℓ)} → {A : Γ ⟦ A ⟧} → Ren Γ (_,_ Γ {A = A} A)
--wkᵣ {A = A} {A = A} {A = A₁} = there {A = {!   !}}
--
---- dropᵣ : Ren (Γ₁ , A) Γ₂ → Ren Γ₁ Γ₂
---- dropᵣ ρ x = ρ (there x)
--
--_⟪_⟫ : Ctx → Ren Γ₁ Γ₂ → Ctx
--_⟪_⟫ {Γ₁ = ∅}      Γ ρ   = ∅
--_⟪_⟫ {Γ₁ = Γ₁ , A} Γ ρ = {!   !}
   