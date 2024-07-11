{-# OPTIONS --rewriting #-}
module SystemF where

open import Level
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl)

open import Agda.Builtin.Equality.Rewrite

variable 
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ' ℓ₁' ℓ₂' ℓ₃' : Level

Env = List Level

variable 
  Δ Δ₁ Δ₂ Δ₃ Δ' Δ₁' Δ₂' Δ₃' : Env

data _∈_ : Level → Env → Set where
  here  : ℓ ∈ (ℓ ∷ Δ)
  there : ℓ ∈ Δ → ℓ ∈ (ℓ' ∷ Δ)

data Type : Env → Level → Set where
  •     : Type (ℓ ∷ Δ) ℓ
  ↑_    : Type Δ ℓ → Type (ℓ' ∷ Δ) ℓ  
  `ℕ    : Type Δ zero
  _⇒_   : Type Δ ℓ → Type Δ ℓ' → Type Δ (ℓ ⊔ ℓ')
  ∀α_,_ : ∀ ℓ → Type (ℓ ∷ Δ) ℓ' → Type Δ (suc ℓ ⊔ ℓ')

variable
  T T₁ T₂ T₃ T' T₁' T₂' T₃' : Type Δ ℓ

data _⇛ₜ_ : Env → Env → Set where
  id  : Δ ⇛ₜ Δ 
  wk  : (ℓ : Level) → Δ₁ ⇛ₜ Δ₂ → Δ₁ ⇛ₜ (ℓ ∷ Δ₂)
  _∷_ : Type Δ₂ ℓ → Δ₁ ⇛ₜ Δ₂ → (ℓ ∷ Δ₁) ⇛ₜ Δ₂

variable
  σₜ σₜ₁ σₜ₂ σₜ₃ σₜ' σₜ₁' σₜ₂' σₜ₃' : Δ₁ ⇛ₜ Δ₂

_↑ₜ_ : Δ₁ ⇛ₜ Δ₂ → (ℓ : Level) → (ℓ ∷ Δ₁) ⇛ₜ (ℓ ∷ Δ₂)
σ ↑ₜ _ = • ∷ (wk _ σ)

_⋯ₜ_ : Type Δ₁ ℓ → Δ₁ ⇛ₜ Δ₂ → Type Δ₂ ℓ
T          ⋯ₜ id        = T
T          ⋯ₜ (wk _ σ)  = ↑ (T ⋯ₜ σ)
•          ⋯ₜ (T ∷ _)   = T
(↑ T)      ⋯ₜ (_ ∷ σ)   = T ⋯ₜ σ
`ℕ         ⋯ₜ (_ ∷ _)   = `ℕ
(T₁ ⇒ T₂)  ⋯ₜ σ@(_ ∷ _) = (T₁ ⋯ₜ σ) ⇒ (T₂ ⋯ₜ σ)
(∀α ℓ , T) ⋯ₜ σ@(_ ∷ _) = ∀α ℓ , (T ⋯ₜ (σ ↑ₜ ℓ))

_[_]ₜ : Type (ℓ' ∷ Δ) ℓ → Type Δ ℓ' → Type Δ ℓ 
T [ T' ]ₜ = T ⋯ₜ (T' ∷ id) 

_∘_ : Δ₂ ⇛ₜ Δ₃ → Δ₁ ⇛ₜ Δ₂ → Δ₁ ⇛ₜ Δ₃
id         ∘ σ₂        = σ₂
wk _ σ₁    ∘ σ₂        = wk _ (σ₁ ∘ σ₂)
σ₁@(_ ∷ _) ∘ id        = σ₁
(_ ∷ σ₁)   ∘ wk _ σ₂   = σ₁ ∘ σ₂
σ₁@(_ ∷ _) ∘ (T ∷ σ₂)  = (T ⋯ₜ σ₁) ∷ (σ₁ ∘ σ₂)

∘idₜ : (σ : Δ₁ ⇛ₜ Δ₂) → σ ∘ id ≡ σ 
∘idₜ id       = refl
∘idₜ (wk _ σ) = cong (wk _) (∘idₜ σ)
∘idₜ (_ ∷ _)  = refl 

fusionₜ : (T : Type Δ₁ ℓ) → (σ₁ : Δ₁ ⇛ₜ Δ₂) → (σ₂ : Δ₂ ⇛ₜ Δ₃) → (T ⋯ₜ σ₁) ⋯ₜ σ₂ ≡ T ⋯ₜ (σ₂ ∘ σ₁)
fusionₜ T σ₁        id                    = refl
fusionₜ T σ₁        (wk _ σ₂)             = cong ↑_ (fusionₜ T σ₁ σ₂)
fusionₜ T id        (_ ∷ _)               = refl
fusionₜ T (wk _ σ₁) (_ ∷ σ₂)              = fusionₜ T σ₁ σ₂
fusionₜ •           σ₁@(_ ∷ _) σ₂@(_ ∷ _) = refl
fusionₜ (↑ T)       (_ ∷ σ₁)   σ₂@(_ ∷ _) = fusionₜ T σ₁ σ₂
fusionₜ `ℕ          σ₁@(_ ∷ _) σ₂@(_ ∷ _) = refl
fusionₜ (T₁ ⇒ T₂)   σ₁@(_ ∷ _) σ₂@(_ ∷ _) = cong₂ _⇒_ (fusionₜ T₁ σ₁ σ₂) (fusionₜ T₂ σ₁ σ₂)
fusionₜ (∀α ℓ , T)  σ₁@(_ ∷ _) σ₂@(_ ∷ _) = cong (∀α ℓ ,_) (fusionₜ T (σ₁ ↑ₜ ℓ) (σ₂ ↑ₜ ℓ))

{-# REWRITE fusionₜ #-}

data Ctx : Env → Set where
  ∅     : Ctx []
  _,_   : Ctx Δ → Type Δ ℓ → Ctx Δ          
  _,★_  : Ctx Δ → (ℓ : Level) → Ctx (ℓ ∷ Δ) 

variable 
  Γ Γ₁ Γ₂ Γ₃ Γ' Γ₁' Γ₂' Γ₃' : Ctx Δ

data Expr : {Δ : Env} → Ctx Δ → Type Δ ℓ → Set where
  •     : Expr (Γ , T) T 
  ↑_    : Expr Γ T → Expr (Γ , T') T
  ↑★_   : Expr Γ T → Expr (Γ ,★ ℓ) (↑ T)
  λx_   : Expr (Γ , T') T → Expr Γ T 
  Λα_,_ : (ℓ : Level) → {T : Type (ℓ ∷ Δ) ℓ'} → Expr (Γ ,★ ℓ) T → Expr Γ (∀α ℓ , T)
  _·_   : Expr Γ (T₁ ⇒ T₂) → Expr Γ T₁ → Expr Γ T₂
  _∙_   : {T : Type (ℓ ∷ Δ) ℓ'} → Expr Γ (∀α ℓ , T) → (T' : Type Δ ℓ) → Expr Γ (T [ T' ]ₜ)

variable 
  e e₁ e₂ e₃ e' e₁' e₂' e₃' : Expr Γ T 

data _⇛[_]ₑ_ : Ctx Δ₁ → (Δ₁ ⇛ₜ Δ₂) → Ctx Δ₂ → Set where
  id   : Γ ⇛[ id ]ₑ Γ
  wk   : (T : Type Δ₁ ℓ) → Γ₁ ⇛[ σₜ ]ₑ Γ₂ → Γ₁ ⇛[ σₜ ]ₑ (Γ₂ , (T ⋯ₜ σₜ))
  wk★  : (ℓ : Level) → Γ₁ ⇛[ σₜ ]ₑ Γ₂ → Γ₁ ⇛[ wk ℓ σₜ ]ₑ (Γ₂ ,★ ℓ)
  _∷_  : Expr Γ₂ (T ⋯ₜ σₜ) → Γ₁ ⇛[ σₜ ]ₑ Γ₂ → (Γ₁ , T) ⇛[ σₜ ]ₑ Γ₂
  _∷★_ : {Γ₂ : Ctx Δ₂} → (T : Type Δ₂ ℓ) → Γ₁ ⇛[ σₜ ]ₑ Γ₂ → (Γ₁ ,★ ℓ) ⇛[ T ∷ σₜ ]ₑ Γ₂
  
_↑ₑ_ : ∀ {σₜ : Δ₁ ⇛ₜ Δ₂} {Γ₁ : Ctx Δ₁} {Γ₂ : Ctx Δ₂} →
  Γ₁ ⇛[ σₜ ]ₑ Γ₂ → (T : Type Δ₁ ℓ) → (Γ₁ , T) ⇛[ σₜ ]ₑ (Γ₂ , (T ⋯ₜ σₜ))
_↑ₑ_ {σₜ = σₜ} σ T = • ∷ wk T σ

_↑★ₑ_ : ∀ {σₜ : Δ₁ ⇛ₜ Δ₂} {Γ₁ : Ctx Δ₁} {Γ₂ : Ctx Δ₂} →
  Γ₁ ⇛[ σₜ ]ₑ Γ₂ → (ℓ : Level) → (Γ₁ ,★ ℓ) ⇛[ σₜ ↑ₜ ℓ ]ₑ (Γ₂ ,★ ℓ)
_↑★ₑ_ {σₜ = σₜ} σ ℓ = • ∷★ wk★ ℓ σ

_⋯ₑ_,_ : Expr Γ₁ T → (σₜ : Δ₁ ⇛ₜ Δ₂) → Γ₁ ⇛[ σₜ ]ₑ Γ₂ → Expr Γ₂ (T ⋯ₜ σₜ)
e          ⋯ₑ σₜ         , id         = e
e          ⋯ₑ σₜ         , (wk _ σ)   = ↑ (e ⋯ₑ σₜ , σ)
e          ⋯ₑ (wk ℓ σₜ)  , (wk★ _ σ)  = ↑★ (e ⋯ₑ σₜ , σ)
•          ⋯ₑ σₜ         , σ@(e ∷ _)  = e
(↑ T)      ⋯ₑ σₜ         , (_ ∷ σ)    = T ⋯ₑ σₜ , σ
(λx e)     ⋯ₑ σₜ         , σ@(_ ∷ _)  = λx (e ⋯ₑ σₜ , (σ ↑ₑ _))
(Λα ℓ , e) ⋯ₑ σₜ         , σ@(_ ∷ _)  = {! e ⋯ₑ (σ ↑★ₑ _)  !}
(e₁ · e₂)  ⋯ₑ id         , σ@(_ ∷ _)  = (e₁ ⋯ₑ id , σ) · (e₂ ⋯ₑ id , σ)
(e₁ · e₂)  ⋯ₑ wk ℓ σₜ    , σ@(_ ∷ _)  = {! (e₁ ⋯ₑ wk ℓ σₜ , σ)  !} · (e₂ ⋯ₑ wk ℓ σₜ , σ)
(e₁ · e₂)  ⋯ₑ T ∷ σₜ     , σ@(_ ∷ _)  = (e₁ ⋯ₑ T ∷ σₜ , σ) · (e₂ ⋯ₑ T ∷ σₜ , σ) 
(e ∙ T')   ⋯ₑ σₜ         , σ@(_ ∷ _)  = {! e ⋯ₑ _ , σ !} ∙ (T' ⋯ₜ σₜ)
(↑★ e)     ⋯ₑ (_ ∷ σₜ)   , (_ ∷★ σ)   = e ⋯ₑ σₜ , σ  
(λx e)     ⋯ₑ σₜ@(_ ∷ _) , σ@(_ ∷★ _) = λx (e ⋯ₑ σₜ , (σ ↑ₑ _))
(Λα ℓ , e) ⋯ₑ σₜ@(_ ∷ _) , σ@(_ ∷★ _) = Λα ℓ , (e ⋯ₑ σₜ ↑ₜ ℓ , (σ ↑★ₑ ℓ))
(e₁ · e₂)  ⋯ₑ σₜ@(_ ∷ _) , σ@(_ ∷★ _) = (e₁ ⋯ₑ σₜ , σ) · (e₂ ⋯ₑ σₜ , σ)
(e ∙ T')   ⋯ₑ σₜ@(_ ∷ _) , σ@(_ ∷★ _) = (e ⋯ₑ σₜ , σ) ∙ (T' ⋯ₜ σₜ)   