module TT where

open import Level
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

variable 
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ' ℓ₁' ℓ₂' ℓ₃' : Level

variable
  ⟦T⟧ ⟦T⟧₁ ⟦T⟧₂ ⟦T⟧₃ ⟦T⟧' ⟦T⟧₁' ⟦T⟧₂' ⟦T⟧₃' : Set ℓ

data Ctx : Setω
variable 
  Γ Γ₁ Γ₂ Γ₃ Γ' Γ₁' Γ₂' Γ₃' : Ctx 

data Ctx✦ : Ctx → Setω
variable 
  Γ✦ Γ✦₁ Γ✦₂ Γ✦₃ Γ✦' Γ✦₁' Γ✦₂' Γ✦₃' : Ctx✦ Γ

data Sub : (Γ : Ctx) → Ctx✦ Γ → Ctx → Setω
variable
  σ σ₁ σ₂ σ₃ σ' σ₁' σ₂' σ₃' : Sub Γ₂ Γ✦ Γ₁

data Term : (Γ : Ctx) → (Γ✦ : Ctx✦ Γ) → {ℓ : Level} → Set ℓ → Setω
variable
  T T₁ T₂ T₃ T' T₁' T₂' T₃' : Term Γ Γ✦ ⟦T⟧

_⟦_⟧ : {ℓ : Level} {⟦T⟧ : Set ℓ} → (Γ✦ : Ctx✦ Γ) → Term Γ Γ✦ ⟦T⟧ → ⟦T⟧
_⟨_⟩ : (Γ✦ : Ctx✦ Γ₂) → Sub Γ₂ Γ✦ Γ₁ → Ctx✦ Γ₁
_[_] : {!   !}

data Ctx where
  ∅     : Ctx
  _,_   : Ctx → Set ℓ → Ctx

data _∈_ : Set ℓ → Ctx → Setω where
  here   : ⟦T⟧ ∈ (Γ , ⟦T⟧)
  there  : ⟦T⟧ ∈ Γ → ⟦T⟧ ∈ (Γ , ⟦T⟧')

data Ctx✦ where
  ∅    : Ctx✦ ∅
  _,_  : Ctx✦ Γ → Γ✦ ⟦ T ⟧ → Ctx✦ (Γ , (Γ✦ ⟦ T ⟧))

lookup : Ctx✦ Γ → ⟦T⟧ ∈ Γ → ⟦T⟧
lookup (_ , x)  here      = x
lookup (Γ✦ , _) (there x) = lookup Γ✦ x

data Sub where
  id  : Sub Γ Γ✦ Γ
  _∷_ : {A : Term Γ₂ Γ✦ (Set ℓ)} → 
    Term Γ₂ Γ✦ (Γ✦ ⟦ A ⟧) → 
    Sub Γ₂ Γ✦ Γ₁ → 
    Sub Γ₂ Γ✦ (Γ₁ , (Γ✦ ⟦ A ⟧))

data Term where
  `_  : ⟦T⟧ ∈ Γ → Term Γ Γ✦ ⟦T⟧ 
  
  `⊤  : Term Γ Γ✦ Set
  `tt : Term Γ Γ✦ ⊤

  `∀_∶_ : 
    (A : Term Γ Γ✦ (Set ℓ)) → 
    ({⟦A⟧ : Γ✦ ⟦ A ⟧} → (Term (Γ , (Γ✦ ⟦ A ⟧)) (Γ✦ , ⟦A⟧) (Set ℓ'))) → 
    Term Γ Γ✦ (Set (ℓ ⊔ ℓ'))
  `λ : 
    {A : Term Γ Γ✦ (Set ℓ)} 
    {B : ({⟦A⟧ : Γ✦ ⟦ A ⟧} → (Term (Γ , (Γ✦ ⟦ A ⟧)) (Γ✦ , ⟦A⟧) (Set ℓ')))} →
    ({⟦A⟧ : Γ✦ ⟦ A ⟧} → Term (Γ , (Γ✦ ⟦ A ⟧)) (Γ✦ , ⟦A⟧) ((Γ✦ , ⟦A⟧) ⟦ B ⟧)) → 
    Term Γ Γ✦ (∀ (⟦A⟧ : (Γ✦ ⟦ A ⟧)) → (Γ✦ , ⟦A⟧) ⟦ B ⟧ )
  
  _`≡_ : 
    {A : Term Γ Γ✦ (Set ℓ)} →
    Term Γ Γ✦ (Γ✦ ⟦ A ⟧) → 
    Term Γ Γ✦ (Γ✦ ⟦ A ⟧) →
    Term Γ Γ✦ (Set ℓ)
  `refl : 
    {A : Term Γ Γ✦ (Set ℓ)} →
    {x : Term Γ Γ✦ (Γ✦ ⟦ A ⟧)} →
    Term Γ Γ✦ ((Γ✦ ⟦ x ⟧) ≡ (Γ✦ ⟦ x ⟧))
    
  `zero : Term Γ Γ✦ Level
  `suc  : Term Γ Γ✦ Level →  Term Γ Γ✦ Level 
  `Set  : (ℓ : Term Γ Γ✦ Level) → Term Γ Γ✦ (Set (Γ✦ ⟦ `suc ℓ ⟧))

  _⋯_   : 
    {A : Term Γ₁ Γ✦ (Set ℓ)} →
    Term Γ₁ Γ✦ (Γ✦ ⟦ A ⟧) → 
    (σ : Sub Γ₁ Γ✦ Γ₂) → 
    Term Γ₂ (Γ✦ ⟨ σ ⟩) {!   !}

T [ T' ] = {!   !} -- T T⋯ₛ (T' T∷ₛ Tidₛ) 

  
Γ✦ ⟦ ` x ⟧      = lookup Γ✦ x 
Γ✦ ⟦ `⊤ ⟧       = ⊤
Γ✦ ⟦ `tt ⟧      = tt
Γ✦ ⟦ `∀ A ∶ B ⟧ = ∀ (⟦A⟧ : (Γ✦ ⟦ A ⟧)) → (Γ✦ , ⟦A⟧) ⟦ B ⟧ 
Γ✦ ⟦ `λ e ⟧     = λ ⟦e⟧ → (Γ✦ , ⟦e⟧) ⟦ e ⟧
Γ✦ ⟦ e₁ `≡ e₂ ⟧ = (Γ✦ ⟦ e₁ ⟧) ≡ (Γ✦ ⟦ e₂ ⟧)
Γ✦ ⟦ `refl ⟧    = refl
Γ✦ ⟦ `zero ⟧    = zero
Γ✦ ⟦ `suc ℓ ⟧   = suc (Γ✦ ⟦ ℓ ⟧)
Γ✦ ⟦ `Set ℓ ⟧   = Set (Γ✦ ⟦ ℓ ⟧)
Γ✦ ⟦ T ⋯ σ ⟧    = {!   !} ⟦ T ⟧

Γ✦ ⟨ id ⟩    = Γ✦
Γ✦ ⟨ _∷_ {A = A} T σ ⟩ = _,_ {T = A} (Γ✦ ⟨ σ ⟩) (Γ✦ ⟦ T ⟧)

--ex₁ : Term ∅ ∅ (∅ ⟦ ∀A `Set `zero ∶ (∀A ` here ∶ ` (there here)) ⟧)
--ex₁ = λx {A = `Set `zero} {B = ∀A ` here ∶ ` (there here)} 
--        (λx {A = ` here} {B = ` (there here)} 
--          (` here))