module MLTTbaz where

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

data Term : (Γ : Ctx) → {ℓ : Level} → Set ℓ → Setω
variable
  T T₁ T₂ T₃ T' T₁' T₂' T₃' : Term Γ A

data Ctx where
  ∅   : Ctx
  _,_ : Ctx → A → Ctx

data _∈_ : A → Ctx → Setω where
  here  : a ∈ (Γ , a)
  there : a ∈ Γ → a ∈ (Γ , a') 

lookup : {A : Set ℓ} {a : A} (Γ : Ctx) → a ∈ Γ → A 
lookup {a = a} .(_ , a) here = a
lookup .(Γ , _) (there {Γ = Γ} x) = lookup Γ x

data Term where
  `_ : a ∈ Γ → Term Γ A 

  `⊤  : Term Γ Set
  `tt : Term Γ ⊤

  `∀_∶_ : 
    (A : Set ℓ) → 
    ((a : A) → (Term (Γ , a) (Set ℓ')))→ 
    Term Γ (Set (ℓ ⊔ ℓ'))
  `λ : 
    {A : Set ℓ} 
    {B : ((a : A) → Set ℓ')} →
    ((a : A) → Term (Γ , a) (B a)) → 
    Term Γ (∀ (a : A) → B a)
  
  _·_ :   
    {A : Set ℓ} 
    {B : ((a : A) → (Set ℓ'))} →
    Term Γ (∀ (a : A) → B a) →
    (a : A) →
    Term Γ (B a)

  _`≡_ : 
    {A : Set ℓ} →
    Term Γ A → 
    Term Γ A →
    Term Γ (Set ℓ)
  `refl : 
    {A : Set ℓ} →
    {x : A} →
    Term Γ (x ≡ x)
    
  `zero : Term Γ Level
  `suc  : Term Γ Level →  Term Γ Level 
  `Set  : (ℓ : Level) → Term Γ (Set (suc ℓ))