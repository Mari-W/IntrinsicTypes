{-# OPTIONS --rewriting #-}
module SystemF where

open import Axiom.Extensionality.Propositional using (∀-extensionality; Extensionality)
open import Level
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional public using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; trans; sym; module ≡-Reasoning)
open ≡-Reasoning

open import Agda.Builtin.Equality.Rewrite

variable 
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ' ℓ₁' ℓ₂' ℓ₃' : Level

postulate
  fun-ext : Extensionality ℓ₁ ℓ₂
    
dep-ext : {A : Set ℓ₁} {F G : (α : A) → Set ℓ₂} → ((α : A) → F α ≡ G α) → ((α : A) → F α) ≡ ((α : A) → G α) 
dep-ext = ∀-extensionality fun-ext _ _

Env = List Level

variable 
  Δ Δ₁ Δ₂ Δ₃ Δ' Δ₁' Δ₂' Δ₃' : Env

data Type (Δ : Env) : Level → Set where
  `_    : ℓ ∈ Δ → Type Δ ℓ
  _⇒_   : Type Δ ℓ → Type Δ ℓ' → Type Δ (ℓ ⊔ ℓ')
  ∀α_,_ : ∀ ℓ → Type (ℓ ∷ Δ) ℓ' → Type Δ (suc ℓ ⊔ ℓ')

variable
  T T₁ T₂ T₃ T' T₁' T₂' T₃' : Type Δ ℓ


_T⇛ᵣ_ : Env → Env → Set
Δ₁ T⇛ᵣ Δ₂ = ∀ ℓ → ℓ ∈ Δ₁ → ℓ ∈ Δ₂

Tidᵣ : Δ T⇛ᵣ Δ
Tidᵣ _ x = x

Twkᵣ : Δ T⇛ᵣ (ℓ ∷ Δ)
Twkᵣ _ x = there x

_T∷ᵣ_ : ℓ ∈ Δ₂ → Δ₁ T⇛ᵣ Δ₂ → (ℓ ∷ Δ₁) T⇛ᵣ Δ₂
(x T∷ᵣ _) _ (here refl) = x
(_ T∷ᵣ ρ) _ (there x)   = ρ _ x

_T≫ᵣᵣ_ : Δ₁ T⇛ᵣ Δ₂ → Δ₂ T⇛ᵣ Δ₃ → Δ₁ T⇛ᵣ Δ₃
abstract 
  (ρ₁ T≫ᵣᵣ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)
  T≫ᵣᵣ-def : (ρ₁ : Δ₁ T⇛ᵣ Δ₂) (ρ₂ : Δ₂ T⇛ᵣ Δ₃) (x : ℓ ∈ Δ₁) → (ρ₁ T≫ᵣᵣ ρ₂) _ x ≡ ρ₂ _ (ρ₁ _ x)
  T≫ᵣᵣ-def _ _ _ = refl

_T↑ᵣ_ : Δ₁ T⇛ᵣ Δ₂ → (ℓ : Level) → (ℓ ∷ Δ₁) T⇛ᵣ (ℓ ∷ Δ₂)
ρ T↑ᵣ _ = (here refl) T∷ᵣ (ρ T≫ᵣᵣ Twkᵣ)

_T⋯ᵣ_ : Type Δ₁ ℓ → Δ₁ T⇛ᵣ Δ₂ → Type Δ₂ ℓ
(` x)      T⋯ᵣ ρ = ` (ρ _ x)
(T₁ ⇒ T₂)  T⋯ᵣ ρ = (T₁ T⋯ᵣ ρ) ⇒ (T₂ T⋯ᵣ ρ)
(∀α ℓ , T) T⋯ᵣ ρ = ∀α ℓ , (T T⋯ᵣ (ρ T↑ᵣ ℓ))

Twk : Type Δ ℓ → Type (ℓ' ∷ Δ) ℓ
Twk T = T T⋯ᵣ Twkᵣ

_T⇛ₛ_ : Env → Env → Set
Δ₁ T⇛ₛ Δ₂ = ∀ ℓ → ℓ ∈ Δ₁ → Type Δ₂ ℓ

Tidₛ : Δ T⇛ₛ Δ
Tidₛ _ = `_

_T∷ₛ_ : Type Δ₂ ℓ → Δ₁ T⇛ₛ Δ₂ → (ℓ ∷ Δ₁) T⇛ₛ Δ₂
(T T∷ₛ _) _ (here refl) = T
(_ T∷ₛ ρ) _ (there x) = ρ _ x

_T≫ᵣₛ_ : Δ₁ T⇛ᵣ Δ₂ → Δ₂ T⇛ₛ Δ₃ → Δ₁ T⇛ₛ Δ₃
abstract 
  (ρ₁ T≫ᵣₛ σ₂) _ x = σ₂ _ (ρ₁ _ x)
  T≫ᵣₛ-def : (ρ₁ : Δ₁ T⇛ᵣ Δ₂) (σ₂ : Δ₂ T⇛ₛ Δ₃) (x : ℓ ∈ Δ₁) → (ρ₁ T≫ᵣₛ σ₂) _ x ≡ σ₂ _ (ρ₁ _ x)
  T≫ᵣₛ-def _ _ _ = refl

_T≫ₛᵣ_ : Δ₁ T⇛ₛ Δ₂ → Δ₂ T⇛ᵣ Δ₃ → Δ₁ T⇛ₛ Δ₃
abstract 
  (σ₁ T≫ₛᵣ ρ₂) _ x = (σ₁ _ x) T⋯ᵣ ρ₂
  T≫ₛᵣ-def : (σ₁ : Δ₁ T⇛ₛ Δ₂) (ρ₂ : Δ₂ T⇛ᵣ Δ₃) (x : ℓ ∈ Δ₁) → (σ₁ T≫ₛᵣ ρ₂) _ x ≡ (σ₁ _ x) T⋯ᵣ ρ₂
  T≫ₛᵣ-def _ _ _ = refl

_T↑ₛ_ : Δ₁ T⇛ₛ Δ₂ → (ℓ : Level) → (ℓ ∷ Δ₁) T⇛ₛ (ℓ ∷ Δ₂)
σ T↑ₛ _ = (` (here refl)) T∷ₛ (σ T≫ₛᵣ Twkᵣ)

_T⋯ₛ_ : Type Δ₁ ℓ → Δ₁ T⇛ₛ Δ₂ → Type Δ₂ ℓ
(` x)      T⋯ₛ σ = (σ _ x)
(T₁ ⇒ T₂)  T⋯ₛ σ = (T₁ T⋯ₛ σ) ⇒ (T₂ T⋯ₛ σ)
(∀α ℓ , T) T⋯ₛ σ = ∀α ℓ , (T T⋯ₛ (σ T↑ₛ ℓ))

_T≫ₛₛ_ : Δ₁ T⇛ₛ Δ₂ → Δ₂ T⇛ₛ Δ₃ → Δ₁ T⇛ₛ Δ₃
abstract 
  (σ₁ T≫ₛₛ σ₂) _ x = (σ₁ _ x) T⋯ₛ σ₂
  T≫ₛₛ-def : (σ₁ : Δ₁ T⇛ₛ Δ₂) (σ₂ : Δ₂ T⇛ₛ Δ₃) (x : ℓ ∈ Δ₁) → (σ₁ T≫ₛₛ σ₂) _ x ≡ (σ₁ _ x) T⋯ₛ σ₂
  T≫ₛₛ-def _ _ _ = refl

_T[_] : Type (ℓ' ∷ Δ) ℓ → Type Δ ℓ' → Type Δ ℓ
T T[ T' ] = T T⋯ₛ (T' T∷ₛ Tidₛ) 

{-# REWRITE T≫ᵣᵣ-def T≫ᵣₛ-def T≫ₛᵣ-def T≫ₛₛ-def #-}

Tη-idᵣ : _T∷ᵣ_ {ℓ = ℓ} {Δ₁ = Δ} (here refl) Twkᵣ ≡ Tidᵣ 
Tη-idᵣ = fun-ext (λ _ → fun-ext λ { (here refl) → refl ; (there x) → refl })

Tη-idₛ : _T∷ₛ_ {ℓ = ℓ} {Δ₁ = Δ} (` (here refl)) (Twkᵣ T≫ᵣₛ Tidₛ) ≡ Tidₛ
Tη-idₛ = fun-ext λ _ → fun-ext λ { (here refl) → refl ; (there x) → refl }

postulate
  Tη-lawᵣ : (ρ : (ℓ ∷ Δ₁) T⇛ᵣ Δ₂) → _T∷ᵣ_ (ρ _ (here refl)) (Twkᵣ T≫ᵣᵣ ρ) ≡ ρ 
  Tη-lawₛ : (σ : (ℓ ∷ Δ₁) T⇛ₛ Δ₂) → _T∷ₛ_ (σ _ (here refl)) (Twkᵣ T≫ᵣₛ σ) ≡ σ 
      
{-# REWRITE Tη-idᵣ Tη-idₛ #-}

⋯Tidᵣ : (T : Type Δ ℓ) → T T⋯ᵣ Tidᵣ ≡ T 
⋯Tidᵣ (` x)        = refl
⋯Tidᵣ (T₁ ⇒ T₂)    = cong₂ _⇒_ (⋯Tidᵣ T₁) (⋯Tidᵣ T₂)
⋯Tidᵣ (∀α ℓ , T)   = cong (∀α ℓ ,_) (⋯Tidᵣ T)

⋯Tidₛ : (T : Type Δ ℓ) → T T⋯ₛ Tidₛ ≡ T 
⋯Tidₛ (` x)        = refl
⋯Tidₛ (T₁ ⇒ T₂)    = cong₂ _⇒_ (⋯Tidₛ T₁) (⋯Tidₛ T₂)
⋯Tidₛ (∀α ℓ , T)   = cong (∀α ℓ ,_) (⋯Tidₛ T)

{-# REWRITE ⋯Tidᵣ ⋯Tidₛ #-}

Tdistributivityᵣᵣ : (x : ℓ ∈ Δ₂) (ρ₁ : Δ₁ T⇛ᵣ Δ₂) (ρ₂ : Δ₂ T⇛ᵣ Δ₃) → (x T∷ᵣ ρ₁) T≫ᵣᵣ ρ₂ ≡ ρ₂ _ x T∷ᵣ (ρ₁ T≫ᵣᵣ ρ₂)
Tdistributivityᵣᵣ _ _ _ = fun-ext (λ _ → fun-ext λ { (here refl) → refl ; (there x) → refl })

Tdistributivityᵣₛ : (x : ℓ ∈ Δ₂) (ρ₁ : Δ₁ T⇛ᵣ Δ₂) (σ₂ : Δ₂ T⇛ₛ Δ₃) → (x T∷ᵣ ρ₁) T≫ᵣₛ σ₂ ≡ σ₂ _ x T∷ₛ (ρ₁ T≫ᵣₛ σ₂)
Tdistributivityᵣₛ _ _ _ = fun-ext (λ _ → fun-ext λ { (here refl) → refl ; (there x) → refl })

Tdistributivityₛᵣ : (T : Type Δ₂ ℓ) (σ₁ : Δ₁ T⇛ₛ Δ₂) (ρ₂ : Δ₂ T⇛ᵣ Δ₃) → (T T∷ₛ σ₁) T≫ₛᵣ ρ₂ ≡ (T T⋯ᵣ ρ₂) T∷ₛ (σ₁ T≫ₛᵣ ρ₂)
Tdistributivityₛᵣ _ _ _ = fun-ext (λ _ → fun-ext λ { (here refl) → refl ; (there x) → refl })

Tdistributivityₛₛ : (T : Type Δ₂ ℓ) (σ₁ : Δ₁ T⇛ₛ Δ₂) (σ₂ : Δ₂ T⇛ₛ Δ₃) → (T T∷ₛ σ₁) T≫ₛₛ σ₂ ≡ (T T⋯ₛ σ₂) T∷ₛ (σ₁ T≫ₛₛ σ₂)
Tdistributivityₛₛ _ _ _ = fun-ext (λ _ → fun-ext λ { (here refl) → refl ; (there x) → refl })

{-# REWRITE Tdistributivityᵣᵣ Tdistributivityᵣₛ Tdistributivityₛᵣ Tdistributivityₛₛ #-}


Tcompositionalityᵣᵣ : (ρ₁ : Δ₁ T⇛ᵣ Δ₂) (ρ₂ : Δ₂ T⇛ᵣ Δ₃) (T : Type Δ₁ ℓ) → (T T⋯ᵣ ρ₁) T⋯ᵣ ρ₂ ≡ T T⋯ᵣ (ρ₁ T≫ᵣᵣ ρ₂)
Tcompositionalityᵣᵣ ρ₁ ρ₂ (` x)      = refl
Tcompositionalityᵣᵣ ρ₁ ρ₂ (T₁ ⇒ T₂)  = cong₂ _⇒_ (Tcompositionalityᵣᵣ ρ₁ ρ₂ T₁) (Tcompositionalityᵣᵣ ρ₁ ρ₂ T₂)
Tcompositionalityᵣᵣ ρ₁ ρ₂ (∀α ℓ , T) = cong (∀α ℓ ,_) (Tcompositionalityᵣᵣ (ρ₁ T↑ᵣ ℓ) (ρ₂ T↑ᵣ ℓ) T)

{-# REWRITE Tcompositionalityᵣᵣ #-}

Tcompositionalityᵣₛ : (ρ₁ : Δ₁ T⇛ᵣ Δ₂) (σ₂ : Δ₂ T⇛ₛ Δ₃)  (T : Type Δ₁ ℓ) → (T T⋯ᵣ ρ₁) T⋯ₛ σ₂ ≡ T T⋯ₛ (ρ₁ T≫ᵣₛ σ₂)
Tcompositionalityᵣₛ ρ₁ σ₂ (` x)      = refl
Tcompositionalityᵣₛ ρ₁ σ₂ (T₁ ⇒ T₂)  = cong₂ _⇒_ (Tcompositionalityᵣₛ ρ₁ σ₂ T₁) (Tcompositionalityᵣₛ ρ₁ σ₂ T₂)
Tcompositionalityᵣₛ ρ₁ σ₂ (∀α ℓ , T) = cong (∀α ℓ ,_) (Tcompositionalityᵣₛ (ρ₁ T↑ᵣ ℓ) (σ₂ T↑ₛ ℓ) T)

{-# REWRITE Tcompositionalityᵣₛ #-}

Tcompositionalityₛᵣ : (σ₁ : Δ₁ T⇛ₛ Δ₂) (ρ₂ : Δ₂ T⇛ᵣ Δ₃)  (T : Type Δ₁ ℓ) → (T T⋯ₛ σ₁) T⋯ᵣ ρ₂ ≡ T T⋯ₛ (σ₁ T≫ₛᵣ ρ₂)
Tcompositionalityₛᵣ σ₁ ρ₂ (` x)      = refl
Tcompositionalityₛᵣ σ₁ ρ₂ (T₁ ⇒ T₂)  = cong₂ _⇒_ (Tcompositionalityₛᵣ σ₁ ρ₂ T₁) (Tcompositionalityₛᵣ σ₁ ρ₂ T₂)
Tcompositionalityₛᵣ σ₁ ρ₂ (∀α ℓ , T) = cong (∀α ℓ ,_) (Tcompositionalityₛᵣ (σ₁ T↑ₛ ℓ) (ρ₂ T↑ᵣ ℓ) T)

{-# REWRITE Tcompositionalityₛᵣ #-}

Tcompositionalityₛₛ : (σ₁ : Δ₁ T⇛ₛ Δ₂) (σ₂ : Δ₂ T⇛ₛ Δ₃)  (T : Type Δ₁ ℓ) → (T T⋯ₛ σ₁) T⋯ₛ σ₂ ≡ T T⋯ₛ (σ₁ T≫ₛₛ σ₂)
Tcompositionalityₛₛ σ₁ σ₂ (` x)      = refl
Tcompositionalityₛₛ σ₁ σ₂ (T₁ ⇒ T₂)  = cong₂ _⇒_ (Tcompositionalityₛₛ σ₁ σ₂ T₁) (Tcompositionalityₛₛ σ₁ σ₂ T₂)
Tcompositionalityₛₛ σ₁ σ₂ (∀α ℓ , T) = cong (∀α ℓ ,_) (Tcompositionalityₛₛ (σ₁ T↑ₛ ℓ) (σ₂ T↑ₛ ℓ) T)

{-# REWRITE Tcompositionalityₛₛ #-}

T↑coincidence : (ρ : Δ₁ T⇛ᵣ Δ₂) (ℓ : Level) → (` here refl) T∷ₛ ((ρ T≫ᵣᵣ Twkᵣ) T≫ᵣₛ Tidₛ) ≡ (ρ T≫ᵣₛ Tidₛ) T↑ₛ ℓ
T↑coincidence _ _ = fun-ext (λ _ → fun-ext λ { (here refl) → refl ; (there x) → refl })

Tcoincidence : (ρ : Δ₁ T⇛ᵣ Δ₂) (T : Type Δ₁ ℓ) → T T⋯ₛ (ρ T≫ᵣₛ Tidₛ) ≡ T T⋯ᵣ ρ
Tcoincidence ρ (` x)                                = refl
Tcoincidence ρ (T₁ ⇒ T₂)                            = cong₂ _⇒_ (Tcoincidence ρ T₁) (Tcoincidence ρ T₂)
Tcoincidence ρ (∀α ℓ , T) rewrite T↑coincidence ρ ℓ = cong (∀α ℓ ,_) (Tcoincidence (ρ T↑ᵣ ℓ) T)

{-# REWRITE Tcoincidence #-}

variable
  ρ★ ρ★₁ ρ★₂ ρ★₃ ρ★₄ ρ★' ρ★₁' ρ★₂' ρ★₃' ρ★₄' : Δ₁ T⇛ᵣ Δ₂
  σ★ σ★₁ σ★₂ σ★₃ σ★₄ σ★' σ★₁' σ★₂' σ★₃' σ★₄' : Δ₁ T⇛ₛ Δ₂

data Ctx : Env → Set where
  ∅     : Ctx []
  _،_   : Ctx Δ → Type Δ ℓ → Ctx Δ          
  _،★_  : Ctx Δ → (ℓ : Level) → Ctx (ℓ ∷ Δ) 

variable 
  Γ Γ₁ Γ₂ Γ₃ Γ' Γ₁' Γ₂' Γ₃' : Ctx Δ

data _∈#_ : Type Δ ℓ → Ctx Δ → Set where
  here   : T ∈# (Γ ، T)
  there  : T ∈# Γ → T ∈# (Γ ، T')
  tskip  : T ∈# Γ → (Twk T) ∈# (Γ ،★ ℓ)

data Expr {Δ : Env} (Γ : Ctx Δ) : Type Δ ℓ → Set where
  `_    : T ∈# Γ → Expr Γ T
  λx_   : Expr (Γ ، T₁) T₂ → Expr Γ (T₁ ⇒ T₂) 
  Λα_,_ : (ℓ : Level) → {T : Type (ℓ ∷ Δ) ℓ'} → Expr (Γ ،★ ℓ) T → Expr Γ (∀α ℓ , T)
  _·_   : Expr Γ (T₁ ⇒ T₂) → Expr Γ T₁ → Expr Γ T₂
  _∙_   : {T : Type (ℓ ∷ Δ) ℓ'} → Expr Γ (∀α ℓ , T) → (T' : Type Δ ℓ) → Expr Γ (T T[ T' ])

variable 
  e e₁ e₂ e₃ e' e₁' e₂' e₃' : Expr Γ T 

_E⇛ᵣ[_]_ : Ctx Δ₁ → Δ₁ T⇛ᵣ Δ₂ → Ctx Δ₂ → Set
_E⇛ᵣ[_]_ {Δ₁}{Δ₂} Γ₁ ρ★ Γ₂ = ∀ ℓ (T : Type Δ₁ ℓ) → T ∈# Γ₁ → (T T⋯ᵣ ρ★) ∈# Γ₂

Eidᵣ : Γ E⇛ᵣ[ Tidᵣ ] Γ
Eidᵣ _ _ x = x

Ewkᵣ : Γ E⇛ᵣ[ Tidᵣ ] (Γ ، T) 
Ewkᵣ _ _ x = there x 

Eℓwkᵣ : Γ E⇛ᵣ[ Twkᵣ ] (Γ ،★ ℓ) 
Eℓwkᵣ _ _ x = tskip x

[_]_E∷ᵣ_ : (ρ★ : Δ₁ T⇛ᵣ Δ₂) → (T T⋯ᵣ ρ★) ∈# Γ₂ → Γ₁ E⇛ᵣ[ ρ★ ] Γ₂ → (Γ₁ ، T) E⇛ᵣ[ ρ★ ] Γ₂
([ _ ] x E∷ᵣ _) _ _ here      = x
([ _ ] _ E∷ᵣ ρ) _ _ (there x) = ρ _ _ x

[_]_Eℓ∷ᵣ_ : (ρ★ : Δ₁ T⇛ᵣ Δ₂) → (x : ℓ ∈ Δ₂) → Γ₁ E⇛ᵣ[ ρ★ ] Γ₂ → (Γ₁ ،★ ℓ) E⇛ᵣ[ x T∷ᵣ ρ★ ] Γ₂
([ _ ] _ Eℓ∷ᵣ ρ) _ _ (tskip x) = ρ _ _ x 

[_،_]_E≫ᵣᵣ_ : (ρ★₁ : Δ₁ T⇛ᵣ Δ₂) → (ρ★₂ : Δ₂ T⇛ᵣ Δ₃) → Γ₁ E⇛ᵣ[ ρ★₁ ] Γ₂ → Γ₂ E⇛ᵣ[ ρ★₂ ] Γ₃ → Γ₁ E⇛ᵣ[ ρ★₁ T≫ᵣᵣ ρ★₂ ] Γ₃
abstract 
  ([ _ ، _ ] ρ₁ E≫ᵣᵣ ρ₂) _ _ x = ρ₂ _ _ (ρ₁ _ _ x)
  E≫ᵣᵣ-def : (ρ★₁ : Δ₁ T⇛ᵣ Δ₂) (ρ★₂ :  Δ₂ T⇛ᵣ Δ₃) (ρ₁ : Γ₁ E⇛ᵣ[ ρ★₁ ] Γ₂) (ρ₂ : Γ₂ E⇛ᵣ[ ρ★₂ ] Γ₃) (T : Type Δ₁ ℓ) (x : T ∈# Γ₁) → 
    ([ ρ★₁ ، ρ★₂ ] ρ₁ E≫ᵣᵣ ρ₂) _ _ x ≡ ρ₂ _ _ (ρ₁ _ _ x)
  E≫ᵣᵣ-def _ _ _ _ _ _ = refl

[_]_E↑ᵣ_ : (ρ★ : Δ₁ T⇛ᵣ Δ₂) → Γ₁ E⇛ᵣ[ ρ★ ] Γ₂ → (T : Type Δ₁ ℓ) → (Γ₁ ، T) E⇛ᵣ[ ρ★ ] (Γ₂ ، (T T⋯ᵣ ρ★))
([ _ ] ρ E↑ᵣ _) = [ _ ] here E∷ᵣ ([ _ ، Tidᵣ ] ρ E≫ᵣᵣ Ewkᵣ)

[_]_Eℓ↑ᵣ_ : (ρ★ : Δ₁ T⇛ᵣ Δ₂) → Γ₁ E⇛ᵣ[ ρ★ ] Γ₂ → (ℓ : Level) → (Γ₁ ،★ ℓ) E⇛ᵣ[ ρ★ T↑ᵣ ℓ ] (Γ₂ ،★ ℓ)
([ _ ] ρ Eℓ↑ᵣ _) = [ _ ] here refl Eℓ∷ᵣ ([ _ ، _ ] ρ E≫ᵣᵣ Eℓwkᵣ)

_E⋯ᵣ[_]_ : Expr Γ₁ T → (ρ★ : Δ₁ T⇛ᵣ Δ₂) → Γ₁ E⇛ᵣ[ ρ★ ] Γ₂ → Expr Γ₂ (T T⋯ᵣ ρ★)
(` x)      E⋯ᵣ[ _ ]  ρ = ` (ρ _ _ x)
(λx e)     E⋯ᵣ[ _ ]  ρ = λx (e E⋯ᵣ[ _ ] ([ _ ] ρ E↑ᵣ _))
(Λα ℓ , e) E⋯ᵣ[ _ ]  ρ = Λα ℓ , (e E⋯ᵣ[ _ ] ([ _ ] ρ Eℓ↑ᵣ ℓ))
(e₁ · e₂)  E⋯ᵣ[ _ ]  ρ = (e₁ E⋯ᵣ[ _ ] ρ) · (e₂ E⋯ᵣ[ _ ] ρ)
(e ∙ T)    E⋯ᵣ[ ρ★ ] ρ = (e E⋯ᵣ[ _ ] ρ) ∙ (T T⋯ᵣ ρ★)

Ewk : Expr Γ T → Expr (Γ ، T') T 
Ewk e = e E⋯ᵣ[ Tidᵣ ] Ewkᵣ

Eℓwk : Expr Γ T → Expr (Γ ،★ ℓ) (Twk T)
Eℓwk e = e E⋯ᵣ[ Twkᵣ ] Eℓwkᵣ

_E⇛ₛ[_]_ : Ctx Δ₁ → Δ₁ T⇛ₛ Δ₂ → Ctx Δ₂ → Set
_E⇛ₛ[_]_ {Δ₁}{Δ₂} Γ₁ σ★ Γ₂ = ∀ ℓ (T : Type Δ₁ ℓ) → T ∈# Γ₁ →  Expr Γ₂ (T T⋯ₛ σ★)

Eidₛ : Γ E⇛ₛ[ Tidₛ ] Γ
Eidₛ _ _ = `_

[_]_E∷ₛ_ : (σ★ : Δ₁ T⇛ₛ Δ₂) → Expr Γ₂ (T T⋯ₛ σ★) → Γ₁ E⇛ₛ[ σ★ ] Γ₂ → (Γ₁ ، T) E⇛ₛ[ σ★ ] Γ₂
([ _ ] T E∷ₛ _) _ _ here      = T
([ _ ] _ E∷ₛ σ) _ _ (there x) = σ _ _ x

[_]_Eℓ∷ₛ_ : (σ★ : Δ₁ T⇛ₛ Δ₂) → (T : Type Δ₂ ℓ) → Γ₁ E⇛ₛ[ σ★ ] Γ₂ → (Γ₁ ،★ ℓ) E⇛ₛ[ T T∷ₛ σ★ ] Γ₂
([ _ ] _ Eℓ∷ₛ σ) _ _ (tskip x) = σ _ _ x 

[_،_]_E≫ᵣₛ_ : (ρ★₁ : Δ₁ T⇛ᵣ Δ₂) → (σ★₂ : Δ₂ T⇛ₛ Δ₃) → Γ₁ E⇛ᵣ[ ρ★₁ ] Γ₂ → Γ₂ E⇛ₛ[ σ★₂ ] Γ₃ → Γ₁ E⇛ₛ[ ρ★₁ T≫ᵣₛ σ★₂ ] Γ₃
abstract 
  ([ _ ، _ ] ρ₁ E≫ᵣₛ σ₂) _ _ x = σ₂ _ _ (ρ₁ _ _ x)
  E≫ᵣₛ-def : (ρ★₁ : Δ₁ T⇛ᵣ Δ₂) (σ★₂ : Δ₂ T⇛ₛ Δ₃) (ρ₁ : Γ₁ E⇛ᵣ[ ρ★₁ ] Γ₂) (σ₂ : Γ₂ E⇛ₛ[ σ★₂ ] Γ₃) (T : Type Δ₁ ℓ) (x : T ∈# Γ₁) → 
    ([ _ ، σ★₂ ] ρ₁ E≫ᵣₛ σ₂) _ _ x ≡ σ₂ _ _ (ρ₁ _ _ x)
  E≫ᵣₛ-def _ _ _ _ _ _ = refl

[_،_]_E≫ₛᵣ_ : (σ★₁ : Δ₁ T⇛ₛ Δ₂) → (ρ★₂ : Δ₂ T⇛ᵣ Δ₃) → Γ₁ E⇛ₛ[ σ★₁ ] Γ₂ → Γ₂ E⇛ᵣ[ ρ★₂ ] Γ₃ → Γ₁ E⇛ₛ[ σ★₁ T≫ₛᵣ ρ★₂ ] Γ₃
abstract 
  ([ _ ، _ ] σ₁ E≫ₛᵣ ρ₂) _ _ x = (σ₁ _ _ x) E⋯ᵣ[ _ ] ρ₂
  E≫ₛᵣ-def : (σ★₁ : Δ₁ T⇛ₛ Δ₂) (ρ★₂ : Δ₂ T⇛ᵣ Δ₃) (σ₁ : Γ₁ E⇛ₛ[ σ★₁ ] Γ₂) (ρ₂ : Γ₂ E⇛ᵣ[ ρ★₂ ] Γ₃) (T : Type Δ₁ ℓ) (x : T ∈# Γ₁) → 
    ([ σ★₁ ، _ ] σ₁ E≫ₛᵣ ρ₂) _ _ x ≡ (σ₁ _ _ x) E⋯ᵣ[ _ ] ρ₂
  E≫ₛᵣ-def _ _ _ _ _ _ = refl
 
[_]_E↑ₛ_ : (σ★ : Δ₁ T⇛ₛ Δ₂) → Γ₁ E⇛ₛ[ σ★ ] Γ₂ → (T : Type Δ₁ ℓ) → (Γ₁ ، T) E⇛ₛ[ σ★ ] (Γ₂ ، (T T⋯ₛ σ★))
[ σ★ ] σ E↑ₛ _ = [ σ★ ] (` here) E∷ₛ ([ σ★ ، Tidᵣ ] σ E≫ₛᵣ Ewkᵣ)

[_]_Eℓ↑ₛ_ : (σ★ : Δ₁ T⇛ₛ Δ₂) → Γ₁ E⇛ₛ[ σ★ ] Γ₂ → (ℓ : Level) → (Γ₁ ،★ ℓ) E⇛ₛ[ σ★ T↑ₛ ℓ ] (Γ₂ ،★ ℓ)
[ σ★ ]  σ Eℓ↑ₛ _ = [ σ★ T≫ₛᵣ Twkᵣ ] (` here refl) Eℓ∷ₛ ([ σ★ ، Twkᵣ ] σ E≫ₛᵣ Eℓwkᵣ)

_E⋯ₛ[_]_ : Expr Γ₁ T → (σ★ : Δ₁ T⇛ₛ Δ₂) → Γ₁ E⇛ₛ[ σ★ ] Γ₂ → Expr Γ₂ (T T⋯ₛ σ★)
(` x)      E⋯ₛ[ _ ]  σ = σ _ _ x 
(λx e)     E⋯ₛ[ σ★ ] σ = λx (e  E⋯ₛ[ σ★ ] ([ σ★ ] σ E↑ₛ _))
(Λα ℓ , e) E⋯ₛ[ σ★ ] σ = Λα ℓ , (e E⋯ₛ[ σ★ T↑ₛ _ ] ([ σ★ ] σ Eℓ↑ₛ ℓ))
(e₁ · e₂)  E⋯ₛ[ σ★ ] σ = (e₁ E⋯ₛ[ σ★ ] σ) · (e₂ E⋯ₛ[ σ★ ] σ)
(e ∙ T)    E⋯ₛ[ σ★ ] σ = (e E⋯ₛ[ σ★ ] σ) ∙ (T T⋯ₛ σ★)

[_،_]_E≫ₛₛ_ : (σ★₁ : Δ₁ T⇛ₛ Δ₂) → (σ★₂ : Δ₂ T⇛ₛ Δ₃) → Γ₁ E⇛ₛ[ σ★₁ ] Γ₂ → Γ₂ E⇛ₛ[ σ★₂ ] Γ₃ → Γ₁ E⇛ₛ[ σ★₁ T≫ₛₛ σ★₂ ] Γ₃
abstract 
  ([ σ★₁ ، σ★₂ ] σ₁ E≫ₛₛ σ₂) _ _ x = (σ₁ _ _ x) E⋯ₛ[ σ★₂ ] σ₂
  E≫ₛₛ-def : (σ★₁ : Δ₁ T⇛ₛ Δ₂) (σ★₂ : Δ₂ T⇛ₛ Δ₃) (σ₁ : Γ₁ E⇛ₛ[ σ★₁ ] Γ₂) (σ₂ : Γ₂ E⇛ₛ[ σ★₂ ] Γ₃) (T : Type Δ₁ ℓ) (x : T ∈# Γ₁) → 
     ([ σ★₁ ، σ★₂ ] σ₁ E≫ₛₛ σ₂) _ _ x ≡ (σ₁ _ _ x) E⋯ₛ[ σ★₂ ] σ₂
  E≫ₛₛ-def _ _ _ _ _ _ = refl

_E[_] : Expr (Γ ، T') T → Expr Γ T' →  Expr Γ T
e E[ e' ] = e E⋯ₛ[ Tidₛ ] ([ Tidₛ ] e' E∷ₛ Eidₛ) 

_ET[_] : Expr (Γ ،★ ℓ) T → (T' : Type Δ ℓ) →  Expr Γ (T T[ T' ])
e ET[ T ] = e E⋯ₛ[ T T∷ₛ Tidₛ ] ([ Tidₛ ] T Eℓ∷ₛ Eidₛ)

{-# REWRITE E≫ᵣᵣ-def E≫ᵣₛ-def E≫ₛᵣ-def E≫ₛₛ-def #-}

Eη-idᵣ : [_]_E∷ᵣ_ {Γ₁ = Γ} Tidᵣ here (Ewkᵣ {T = T}) ≡ Eidᵣ 
Eη-idᵣ = fun-ext (λ _ → fun-ext λ _ → fun-ext λ { here → refl ; (there x) → refl })

Eη-idₛ : [_]_E∷ₛ_ {Γ₁ = Γ} Tidₛ (` here) ([ Tidᵣ ، Tidₛ ] Ewkᵣ {T = T} E≫ᵣₛ Eidₛ) ≡ Eidₛ
Eη-idₛ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { (here) → refl ; (there x) → refl }

Eℓη-idᵣ : [_]_Eℓ∷ᵣ_ {ℓ = ℓ} {Γ₁ = Γ} Twkᵣ (here refl) (Eℓwkᵣ) ≡ Eidᵣ 
Eℓη-idᵣ = fun-ext (λ _ → fun-ext λ _ → fun-ext λ { (tskip x) → refl })

Eℓη-idₛ : [_]_Eℓ∷ₛ_ {Γ₁ = Γ} (Tidₛ T≫ₛᵣ Twkᵣ) (` here refl) ([ Twkᵣ ، Tidₛ ] Eℓwkᵣ {ℓ = ℓ} E≫ᵣₛ Eidₛ) ≡ Eidₛ
Eℓη-idₛ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { (tskip x) → refl }

{-# REWRITE Eη-idᵣ Eη-idₛ #-}
{-# REWRITE Eℓη-idᵣ Eℓη-idₛ #-}

⋯Eidᵣ : (e : Expr Γ T) →  e E⋯ᵣ[ Tidᵣ ] Eidᵣ ≡ e
⋯Eidᵣ (` x)      = refl
⋯Eidᵣ (λx e)     = cong λx_ (⋯Eidᵣ e)
⋯Eidᵣ (Λα ℓ , e) = cong (Λα ℓ ,_) (⋯Eidᵣ e)
⋯Eidᵣ (e₁ · e₂)  = cong₂ _·_ (⋯Eidᵣ e₁) (⋯Eidᵣ e₂)
⋯Eidᵣ (e ∙ T)    = cong (_∙ T) (⋯Eidᵣ e)

⋯Eidₛ : (e : Expr Γ T) → e E⋯ₛ[ Tidₛ ] Eidₛ ≡ e
⋯Eidₛ (` x)      = refl
⋯Eidₛ (λx e)     = cong λx_ (⋯Eidₛ e)
⋯Eidₛ (Λα ℓ , e) = cong (Λα ℓ ,_) (⋯Eidₛ e)
⋯Eidₛ (e₁ · e₂)  = cong₂ _·_ (⋯Eidₛ e₁) (⋯Eidₛ e₂)
⋯Eidₛ (e ∙ T)    = cong (_∙ T) (⋯Eidₛ e) 

{-# REWRITE ⋯Eidₛ #-}

E↑coincidence : (T : Type Δ₁ ℓ) (ρ★ : Δ₁ T⇛ᵣ Δ₂) (ρ : Γ₁ E⇛ᵣ[ ρ★ ] Γ₂) → 
  [ _ ، Tidₛ ] ([ ρ★ ] ρ E↑ᵣ T) E≫ᵣₛ Eidₛ ≡ [ ρ★ T≫ᵣₛ Tidₛ ] ([ _ ، Tidₛ ] ρ E≫ᵣₛ Eidₛ) E↑ₛ T
E↑coincidence _ _ _ = fun-ext (λ _ → fun-ext (λ _ → fun-ext λ { here → refl ; (there x) → refl }))

Tassocᵣₛᵣ : ∀{Δ₄} (ρ₁ : Δ₁ T⇛ᵣ Δ₂) (σ₂ : Δ₂ T⇛ₛ Δ₃) (ρ₃ : Δ₃ T⇛ᵣ Δ₄) → (ρ₁ T≫ᵣₛ σ₂) T≫ₛᵣ ρ₃ ≡ ρ₁ T≫ᵣₛ (σ₂ T≫ₛᵣ ρ₃) 
Tassocᵣₛᵣ _ _ _ = refl

-- E↑ℓcoincidence : (ℓ : Level) (ρ★ : Δ₁ T⇛ᵣ Δ₂) (ρ : Γ₁ E⇛ᵣ[ ρ★ ] Γ₂) → 
--   [ _ ، Tidₛ T↑ₛ ℓ ] ([ _ ] ρ Eℓ↑ᵣ ℓ) E≫ᵣₛ Eidₛ ≡ 
--     subst (λ σ★ → (Γ₁ ،★ ℓ) E⇛ₛ[ {! (ρ★ T≫ᵣₛ Tidₛ) T↑ₛ ℓ!} ] (Γ₂ ،★ ℓ)) (T↑coincidence ρ★ ℓ) ([ ρ★ T≫ᵣₛ Tidₛ ] ([ ρ★ ، Tidₛ ] ρ E≫ᵣₛ Eidₛ) Eℓ↑ₛ ℓ)
-- E↑ℓcoincidence _ _ _ = {!   !} --fun-ext (λ _ → fun-ext (λ _ → fun-ext λ { (tskip x) → {!   !} }))

-- (T T⋯ₛ ((ρ★ T≫ᵣₛ Tidₛ) T↑ₛ ℓ)) != (T T⋯ᵣ (ρ★ T↑ᵣ ℓ))
-- T T⋯ₛ (ρ★ T≫ᵣₛ Tidₛ) T↑ₛ ℓ
-- T T⋯ₛ (` (here refl)) T∷ₛ ((ρ★ T≫ᵣₛ Tidₛ) T≫ₛᵣ Twkᵣ)
-- T T⋯ₛ (` (here refl)) T∷ₛ (ρ★ T≫ᵣₛ (Tidₛ T≫ₛᵣ Twkᵣ))
--
-- postulate  
--   Ecoincidence : (T : Type Δ₁ ℓ) (ρ★ : Δ₁ T⇛ᵣ Δ₂) (ρ : Γ₁ E⇛ᵣ[ ρ★ ] Γ₂) (e : Expr Γ₁ T) → 
--      e E⋯ₛ[ ρ★ T≫ᵣₛ Tidₛ ] ([ _ ، Tidₛ ] ρ E≫ᵣₛ Eidₛ) ≡ e E⋯ᵣ[ ρ★ ] ρ
-- Ecoincidence _ _  ρ (` x)      = refl
-- Ecoincidence _ ρ★ ρ (λx e)     = cong λx_ ((subst (λ σ → (e E⋯ₛ[ ρ★ T≫ᵣₛ Tidₛ ] σ) ≡ (e E⋯ᵣ[ ρ★ ] ([ ρ★ ] ρ E↑ᵣ _))) (E↑coincidence _ _ ρ) (Ecoincidence _ _ ([ ρ★ ] ρ E↑ᵣ _) e)))
-- Ecoincidence _ _  ρ (Λα ℓ , e) = {!   !}
-- Ecoincidence _ _  ρ (e₁ · e₂)  = cong₂ _·_ (Ecoincidence _ _ _ e₁) (Ecoincidence _ _ _ e₂)
-- -- ((e E⋯ₛ[ ρ★ T≫ᵣₛ Tidₛ ] ([ ρ★ ، Tidₛ ] ρ E≫ᵣₛ Eidₛ)) ∙ (T' T⋯ᵣ Tidᵣ))
-- --  ≡ ((e E⋯ᵣ[ ρ★ ] ρ) ∙ (T' T⋯ᵣ ρ★))
-- Ecoincidence _ ρ★ ρ (e ∙ T')   = {!   !}
--  
Edistributivityᵣᵣ : (ρ★₁ : Δ₁ T⇛ᵣ Δ₂) (ρ★₂ :  Δ₂ T⇛ᵣ Δ₃) (T : Type Δ₁ ℓ) (x : (T T⋯ᵣ ρ★₁) ∈# Γ₂)
  (ρ₁ : Γ₁ E⇛ᵣ[ ρ★₁ ] Γ₂) (ρ₂ : Γ₂ E⇛ᵣ[ ρ★₂ ] Γ₃) → ([ ρ★₁ ، ρ★₂ ] ([_]_E∷ᵣ_ {T = T} ρ★₁ x ρ₁) E≫ᵣᵣ ρ₂) ≡ [ ρ★₁ T≫ᵣᵣ ρ★₂ ] ρ₂ _ _ x E∷ᵣ ([ ρ★₁ ، ρ★₂ ] ρ₁ E≫ᵣᵣ ρ₂)  
Edistributivityᵣᵣ _ _ _ _ _ _ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { here → refl ; (there x) → refl }

Edistributivityᵣₛ : (ρ★₁ : Δ₁ T⇛ᵣ Δ₂) (σ★₂ :  Δ₂ T⇛ₛ Δ₃) (T : Type Δ₁ ℓ) (x : (T T⋯ᵣ ρ★₁) ∈# Γ₂)
  (ρ₁ : Γ₁ E⇛ᵣ[ ρ★₁ ] Γ₂) (σ₂ : Γ₂ E⇛ₛ[ σ★₂ ] Γ₃) → [ ρ★₁ ، σ★₂ ] ([_]_E∷ᵣ_ {T = T} ρ★₁ x ρ₁) E≫ᵣₛ σ₂ ≡ [ ρ★₁ T≫ᵣₛ σ★₂ ] (σ₂ _ _ x) E∷ₛ ([ ρ★₁ ، σ★₂ ] ρ₁ E≫ᵣₛ σ₂)  
Edistributivityᵣₛ _ _ _ _ _ _ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { here → refl ; (there x) → refl }

Edistributivityₛᵣ : (σ★₁ : Δ₁ T⇛ₛ Δ₂) (ρ★₂ : Δ₂ T⇛ᵣ Δ₃) (T : Type Δ₁ ℓ) (e : Expr Γ₂ (T T⋯ₛ σ★₁))
  (σ₁ : Γ₁ E⇛ₛ[ σ★₁ ] Γ₂) (ρ₂ : Γ₂ E⇛ᵣ[ ρ★₂ ] Γ₃) → [ σ★₁ ، ρ★₂ ] ([_]_E∷ₛ_ {T = T} σ★₁ e σ₁) E≫ₛᵣ ρ₂ ≡ [ σ★₁ T≫ₛᵣ ρ★₂ ] (e E⋯ᵣ[ ρ★₂ ] ρ₂) E∷ₛ ([ σ★₁ ، ρ★₂ ] σ₁ E≫ₛᵣ ρ₂)  
Edistributivityₛᵣ _ _ _ _ _ _ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { here → refl ; (there x) → refl }

Edistributivityₛₛ : (σ★₁ : Δ₁ T⇛ₛ Δ₂) (σ★₂ : Δ₂ T⇛ₛ Δ₃) (T : Type Δ₁ ℓ) (e : Expr Γ₂ (T T⋯ₛ σ★₁))
  (σ₁ : Γ₁ E⇛ₛ[ σ★₁ ] Γ₂) (σ₂ : Γ₂ E⇛ₛ[ σ★₂ ] Γ₃) → [ σ★₁ ، σ★₂ ] ([_]_E∷ₛ_ {T = T} σ★₁ e σ₁) E≫ₛₛ σ₂ ≡ [ σ★₁ T≫ₛₛ σ★₂ ] (e E⋯ₛ[ σ★₂ ] σ₂) E∷ₛ ([ σ★₁ ، σ★₂ ] σ₁ E≫ₛₛ σ₂)  
Edistributivityₛₛ _ _ _ _ _ _ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { here → refl ; (there x) → refl }

Eℓdistributivityᵣᵣ : (ρ★₁ : Δ₁ T⇛ᵣ Δ₂) (ρ★₂ :  Δ₂ T⇛ᵣ Δ₃) (x : ℓ ∈ Δ₂) (ρ₁ : Γ₁ E⇛ᵣ[ ρ★₁ ] Γ₂) (ρ₂ : Γ₂ E⇛ᵣ[ ρ★₂ ] Γ₃) → 
  [ x T∷ᵣ ρ★₁ ، ρ★₂ ] ([ ρ★₁ ] x Eℓ∷ᵣ ρ₁) E≫ᵣᵣ ρ₂ ≡ [ ρ★₁ T≫ᵣᵣ ρ★₂ ] ρ★₂ _ x Eℓ∷ᵣ ([ ρ★₁ ، ρ★₂ ] ρ₁ E≫ᵣᵣ ρ₂)  
Eℓdistributivityᵣᵣ _ _ _ _ _ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { (tskip x) → refl }

Eℓdistributivityᵣₛ : (ρ★₁ : Δ₁ T⇛ᵣ Δ₂) (σ★₂ :  Δ₂ T⇛ₛ Δ₃) (x : ℓ ∈ Δ₂) (ρ₁ : Γ₁ E⇛ᵣ[ ρ★₁ ] Γ₂) (σ₂ : Γ₂ E⇛ₛ[ σ★₂ ] Γ₃) → 
  [ x T∷ᵣ ρ★₁ ، σ★₂ ] ([ ρ★₁ ] x Eℓ∷ᵣ ρ₁) E≫ᵣₛ σ₂ ≡ [ ρ★₁ T≫ᵣₛ σ★₂ ] (σ★₂ _ x) Eℓ∷ₛ ([ ρ★₁ ، σ★₂ ] ρ₁ E≫ᵣₛ σ₂)
Eℓdistributivityᵣₛ _ _ _ _ _ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { (tskip x) → refl }

Eℓdistributivityₛᵣ : (σ★₁ : Δ₁ T⇛ₛ Δ₂) (ρ★₂ : Δ₂ T⇛ᵣ Δ₃) (T : Type Δ₂ ℓ) (σ₁ : Γ₁ E⇛ₛ[ σ★₁ ] Γ₂) (ρ₂ : Γ₂ E⇛ᵣ[ ρ★₂ ] Γ₃) → 
  [ T T∷ₛ σ★₁ ، ρ★₂ ] ([ σ★₁ ] T Eℓ∷ₛ σ₁) E≫ₛᵣ ρ₂ ≡ [ σ★₁ T≫ₛᵣ ρ★₂ ] (T T⋯ᵣ ρ★₂) Eℓ∷ₛ ([ σ★₁ ، ρ★₂ ] σ₁ E≫ₛᵣ ρ₂)
Eℓdistributivityₛᵣ _ _ _ _ _ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { (tskip x) → refl }

Eℓdistributivityₛₛ : (σ★₁ : Δ₁ T⇛ₛ Δ₂) (σ★₂ : Δ₂ T⇛ₛ Δ₃) (T : Type Δ₂ ℓ) (σ₁ : Γ₁ E⇛ₛ[ σ★₁ ] Γ₂) (σ₂ : Γ₂ E⇛ₛ[ σ★₂ ] Γ₃) → 
 [ T T∷ₛ σ★₁ ، σ★₂ ] ([ σ★₁ ] T Eℓ∷ₛ σ₁) E≫ₛₛ σ₂ ≡ ([ σ★₁ T≫ₛₛ σ★₂ ] (T T⋯ₛ σ★₂) Eℓ∷ₛ ([ σ★₁ ، σ★₂ ] σ₁ E≫ₛₛ σ₂))
Eℓdistributivityₛₛ _ _ _ _ _ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { (tskip x) → refl }

{-# REWRITE Edistributivityᵣᵣ Edistributivityᵣₛ Edistributivityₛᵣ Edistributivityₛₛ #-}
{-# REWRITE Eℓdistributivityᵣᵣ Eℓdistributivityᵣₛ Eℓdistributivityₛᵣ Eℓdistributivityₛₛ #-}

Ecompositionalityᵣᵣ : (ρ★₁ : Δ₁ T⇛ᵣ Δ₂) (ρ★₂ :  Δ₂ T⇛ᵣ Δ₃) (ρ₁ : Γ₁ E⇛ᵣ[ ρ★₁ ] Γ₂) (ρ₂ : Γ₂ E⇛ᵣ[ ρ★₂ ] Γ₃) (e : Expr Γ₁ T) → 
  (e E⋯ᵣ[ ρ★₁ ] ρ₁) E⋯ᵣ[ ρ★₂ ] ρ₂ ≡ e E⋯ᵣ[ ρ★₁ T≫ᵣᵣ ρ★₂ ] ([ ρ★₁ ، ρ★₂ ] ρ₁ E≫ᵣᵣ ρ₂)
Ecompositionalityᵣᵣ ρ★₁ ρ★₂ ρ₁ ρ₂ (` x)      = refl
Ecompositionalityᵣᵣ ρ★₁ ρ★₂ ρ₁ ρ₂ (λx e)     = cong λx_ (Ecompositionalityᵣᵣ _ _ ([ ρ★₁ ] ρ₁ E↑ᵣ _) ([ ρ★₂ ] ρ₂ E↑ᵣ _) e) 
Ecompositionalityᵣᵣ ρ★₁ ρ★₂ ρ₁ ρ₂ (Λα ℓ , e) = cong (Λα ℓ ,_) (Ecompositionalityᵣᵣ _ _ ([ ρ★₁ ] ρ₁ Eℓ↑ᵣ ℓ) ([ ρ★₂ ] ρ₂ Eℓ↑ᵣ ℓ) e)
Ecompositionalityᵣᵣ ρ★₁ ρ★₂ ρ₁ ρ₂ (e₁ · e₂)  = cong₂ _·_ (Ecompositionalityᵣᵣ _ _ ρ₁ ρ₂ e₁) (Ecompositionalityᵣᵣ _ _ ρ₁ ρ₂ e₂)
Ecompositionalityᵣᵣ ρ★₁ ρ★₂ ρ₁ ρ₂ (_∙_ e T') = cong (_∙ _) (Ecompositionalityᵣᵣ _ _ ρ₁ ρ₂ e)

{-# REWRITE Ecompositionalityᵣᵣ #-}

Ecompositionalityᵣₛ : (ρ★₁ : Δ₁ T⇛ᵣ Δ₂) (σ★₂ : Δ₂ T⇛ₛ Δ₃) (ρ₁ : Γ₁ E⇛ᵣ[ ρ★₁ ] Γ₂) (σ₂ : Γ₂ E⇛ₛ[ σ★₂ ] Γ₃) (e : Expr Γ₁ T) → 
  (e E⋯ᵣ[ ρ★₁ ] ρ₁) E⋯ₛ[ σ★₂ ] σ₂ ≡  e E⋯ₛ[ ρ★₁ T≫ᵣₛ σ★₂ ] ([ ρ★₁ ، σ★₂ ] ρ₁ E≫ᵣₛ σ₂)
Ecompositionalityᵣₛ ρ★₁ σ★₂ ρ₁ σ₂ (` x)      = refl
Ecompositionalityᵣₛ ρ★₁ σ★₂ ρ₁ σ₂ (λx e)     = cong λx_ (Ecompositionalityᵣₛ _ _ ([ ρ★₁ ] ρ₁ E↑ᵣ _) ([ σ★₂ ] σ₂ E↑ₛ _) e) 
Ecompositionalityᵣₛ ρ★₁ σ★₂ ρ₁ σ₂ (Λα ℓ , e) = cong (Λα ℓ ,_) (Ecompositionalityᵣₛ _ _ ([ ρ★₁ ] ρ₁ Eℓ↑ᵣ _) ([ σ★₂ ] σ₂ Eℓ↑ₛ _) e)
Ecompositionalityᵣₛ ρ★₁ σ★₂ ρ₁ σ₂ (e₁ · e₂)  = cong₂ _·_ (Ecompositionalityᵣₛ _ _ ρ₁ σ₂ e₁) (Ecompositionalityᵣₛ _ _ ρ₁ σ₂ e₂)
Ecompositionalityᵣₛ ρ★₁ σ★₂ ρ₁ σ₂ (_∙_ {T = T} e T') = cong (_∙ (T' T⋯ₛ (ρ★₁ T≫ᵣₛ σ★₂))) (Ecompositionalityᵣₛ _ _ ρ₁ σ₂ e)

{-# REWRITE Ecompositionalityᵣₛ #-}
-- -- 
-- -- 
-- -- --((σ₁ x₁ T x E⋯ᵣ (λ z T₁ → there)) E⋯ᵣ (λ z T₁ ℓ₁ → (here E∷ᵣ (ρ₂ E≫ᵣᵣ Ewkᵣ)) z T₁ ℓ₁))  ≡ ((σ₁ E≫ₛᵣ ρ₂) E↑ₛ T') x₁ T (there --x)
-- -- mutual 
-- --   E↑compositionalityₛᵣ : (T : Type Δ₁ ℓ) (T' : Type Δ₁ ℓ') (e : Expr (Γ₁ ، T') T)  (σ★₁ : Δ₁ T⇛ₛ Δ₂) (ρ★₂ : Δ₂ T⇛ᵣ Δ₃) (σ₁ : Γ₁ E⇛ₛ[ σ★₁ ] Γ₂) (ρ₂ : Γ₂ E⇛ᵣ[ ρ★₂ ] Γ₃) → 
-- --       _E⋯ᵣ_ (_E⋯ₛ_ {σ★ = σ★₁} e (_E↑ₛ_ {σ★ = σ★₁} σ₁ T')) (ρ₂ E↑ᵣ (T' T⋯ₛ σ★₁)) ≡ _E⋯ₛ_ {σ★ = σ★₁ T≫ₛᵣ ρ★₂} e ((_E↑ₛ_ {σ★ = σ★₁ T≫ₛᵣ ρ★₂} (_E≫ₛᵣ_ {σ★₁ = σ★₁} σ₁ ρ₂)) T')
--   E↑compositionalityₛᵣ T T' e σ★₁ ρ★₂ σ₁ ρ₂ = begin 
--                                       (_E⋯ᵣ_ (_E⋯ₛ_ {σ★ = σ★₁} e (_E↑ₛ_ {σ★ = σ★₁} σ₁ T')) (ρ₂ E↑ᵣ (T' T⋯ₛ σ★₁)))
--                                     ≡⟨ Ecompositionalityₛᵣ T σ★₁ ρ★₂ (_E↑ₛ_ {σ★ = σ★₁} σ₁ T') (ρ₂ E↑ᵣ (T' T⋯ₛ σ★₁)) e ⟩
--                                       _
--                                     ≡⟨ {! refl  !} ⟩
--                                       _E⋯ₛ_ {σ★ = σ★₁ T≫ₛᵣ ρ★₂} e ((_E↑ₛ_ {σ★ = σ★₁ T≫ₛᵣ ρ★₂} (_E≫ₛᵣ_ {σ★₁ = σ★₁} σ₁ ρ₂)) T')
--                                     ∎ 
--    
--   Ecompositionalityₛᵣ : (T : Type Δ₁ ℓ) (σ★₁ : Δ₁ T⇛ₛ Δ₂) (ρ★₂ : Δ₂ T⇛ᵣ Δ₃) (σ₁ : Γ₁ E⇛ₛ[ σ★₁ ] Γ₂) (ρ₂ : Γ₂ E⇛ᵣ[ ρ★₂ ] Γ₃) (e : Expr Γ₁ T) → 
--     _E⋯ᵣ_ (_E⋯ₛ_ {σ★ = σ★₁} e σ₁) ρ₂ ≡ _E⋯ₛ_ {σ★ = σ★₁ T≫ₛᵣ ρ★₂} e (_E≫ₛᵣ_ {σ★₁ = σ★₁} σ₁ ρ₂)
--   Ecompositionalityₛᵣ _ σ★₁ ρ★₂ σ₁ ρ₂ (` x)             = refl
--   Ecompositionalityₛᵣ T σ★₁ ρ★₂ σ₁ ρ₂ (λx_ {T' = T'} e) = cong λx_ (E↑compositionalityₛᵣ T T' e σ★₁ ρ★₂ σ₁ ρ₂)
--   Ecompositionalityₛᵣ _ σ★₁ ρ★₂ σ₁ ρ₂ (Λα ℓ , e)        = cong (Λα ℓ ,_) {!   !}
--   Ecompositionalityₛᵣ _ σ★₁ ρ★₂ σ₁ ρ₂ (e₁ · e₂)         = cong₂ _·_ (Ecompositionalityₛᵣ _ σ★₁ _ σ₁ ρ₂ e₁) (Ecompositionalityₛᵣ _ σ★₁ _ σ₁ ρ₂ e₂)
--   Ecompositionalityₛᵣ .(T T[ T' ]) σ★₁ ρ★₂ σ₁ ρ₂ (_∙_ {T = T} e T') = cong (_∙ (T' T⋯ₛ (σ★₁ T≫ₛᵣ ρ★₂))) (Ecompositionalityₛᵣ _ σ★₁ _ σ₁ ρ₂ e)
-- 
postulate
  Ecompositionalityₛᵣ : (T : Type Δ₁ ℓ) (σ★₁ : Δ₁ T⇛ₛ Δ₂) (ρ★₂ : Δ₂ T⇛ᵣ Δ₃) (σ₁ : Γ₁ E⇛ₛ[ σ★₁ ] Γ₂) (ρ₂ : Γ₂ E⇛ᵣ[ ρ★₂ ] Γ₃) (e : Expr Γ₁ T) → 
    (e E⋯ₛ[ σ★₁ ] σ₁) E⋯ᵣ[ _ ] ρ₂ ≡ e E⋯ₛ[ σ★₁ T≫ₛᵣ ρ★₂ ]  ([ σ★₁ ، _ ] σ₁ E≫ₛᵣ ρ₂)

  Ecompositionalityₛₛ : (T : Type Δ₁ ℓ) (σ★₁ : Δ₁ T⇛ₛ Δ₂) (σ★₂ : Δ₂ T⇛ₛ Δ₃) (σ₁ : Γ₁ E⇛ₛ[ σ★₁ ] Γ₂) (σ₂ : Γ₂ E⇛ₛ[ σ★₂ ] Γ₃) (e : Expr Γ₁ T) → 
     (e E⋯ₛ[ σ★₁ ] σ₁) E⋯ₛ[ σ★₂ ] σ₂ ≡ e E⋯ₛ[ σ★₁ T≫ₛₛ σ★₂ ] ([ σ★₁ ، σ★₂ ] σ₁ E≫ₛₛ σ₂) 
      
{-# REWRITE Ecompositionalityₛᵣ Ecompositionalityₛₛ #-}

data _≡ω_ {A : Setω} (x : A) : A → Setω where
  refl : x ≡ω x

{-# BUILTIN REWRITE _≡ω_ #-}

data Env✦ : Env → Setω where
  []   : Env✦ []
  _∷_  : Set ℓ → Env✦ Δ → Env✦ (ℓ ∷ Δ)

variable
  η✦ η✦₁ η✦₂ η✦₃ η✦' η✦₁' η✦₂'η✦₃' : Env✦ Δ  
  ⟦T⟧ ⟦T⟧₁ ⟦T⟧₂ ⟦T⟧₃ ⟦T⟧' ⟦T⟧₁' ⟦T⟧₂' ⟦T⟧₃' : Set ℓ

lookup : Env✦ Δ → ℓ ∈ Δ → Set ℓ
lookup (x ∷ _) (here refl) = x
lookup (_ ∷ η) (there x)   = lookup η x 

T⟦_⟧ : (T : Type Δ ℓ) → Env✦ Δ → Set ℓ
T⟦ ` x ⟧      η✦ = lookup η✦ x
T⟦ T₁ ⇒ T₂ ⟧  η✦ = T⟦ T₁ ⟧ η✦ → T⟦ T₂ ⟧ η✦
T⟦ ∀α ℓ , T ⟧ η✦ = (α : Set ℓ) → T⟦ T ⟧ (α ∷ η✦)

Tdropᵣ : (ℓ ∷ Δ₁) T⇛ᵣ Δ₂ → Δ₁ T⇛ᵣ Δ₂
Tdropᵣ ρ★ _ x = ρ★ _ (there x)

ρ★⟦_⟧_ : Δ₁ T⇛ᵣ Δ₂ → Env✦ Δ₂ → Env✦ Δ₁
ρ★⟦_⟧_ {Δ₁ = []}    ρ★ η✦₂ = []
ρ★⟦_⟧_ {Δ₁ = _ ∷ _} ρ★ η✦₂ = T⟦ ` ρ★ _ (here refl) ⟧ η✦₂ ∷ ρ★⟦ Tdropᵣ ρ★ ⟧ η✦₂

cong-ωω : ∀ {A : Setω} {B : Setω} (f : A → B) {x y : A} → x ≡ω y → f x ≡ω f y
cong-ωω f refl = refl

⟦ρ★⟧-preserves-wk : (ρ★ : Δ₁ T⇛ᵣ Δ₂) → (⟦T⟧ : Set ℓ) → (η✦₂ : Env✦ Δ₂) → 
  (ρ★⟦ ρ★ T≫ᵣᵣ Twkᵣ ⟧ (⟦T⟧ ∷ η✦₂)) ≡ω (ρ★⟦ ρ★ ⟧ η✦₂)
⟦ρ★⟧-preserves-wk {Δ₁ = []}     ρ★ ⟦T⟧ η✦₂ = refl
⟦ρ★⟧-preserves-wk {Δ₁ = l ∷ Δ₁} ρ★ ⟦T⟧ η✦₂ = cong-ωω (lookup η✦₂ (ρ★ l (here refl)) ∷_) (⟦ρ★⟧-preserves-wk (Tdropᵣ ρ★) ⟦T⟧ η✦₂)

{-# REWRITE ⟦ρ★⟧-preserves-wk #-}

⟦ρ★⟧-preserves-id : (η✦ : Env✦ Δ) → (ρ★⟦ Tidᵣ ⟧ η✦) ≡ω η✦
⟦ρ★⟧-preserves-id []       = refl
⟦ρ★⟧-preserves-id (x ∷ η✦) = cong-ωω (x ∷_) (⟦ρ★⟧-preserves-id η✦)

{-# REWRITE ⟦ρ★⟧-preserves-id #-}

⟦ρ★⟧-preserves-lookup : (x : ℓ ∈ Δ₁) (ρ★ : Δ₁ T⇛ᵣ Δ₂) (η✦₂ : Env✦ Δ₂) → lookup η✦₂ (ρ★ _ x) ≡ lookup (ρ★⟦ ρ★ ⟧ η✦₂) x
⟦ρ★⟧-preserves-lookup (here refl) ρ★ η✦ = refl
⟦ρ★⟧-preserves-lookup (there x) ρ★ η✦   rewrite ⟦ρ★⟧-preserves-lookup x (Tdropᵣ ρ★) η✦ = refl

T⇛ᵣ-preserves-⟦T⟧ : (ρ★ : Δ₁ T⇛ᵣ Δ₂) (η✦₂ : Env✦ Δ₂) (T : Type Δ₁ ℓ) → 
  T⟦ T T⋯ᵣ ρ★ ⟧ η✦₂ ≡ T⟦ T ⟧ (ρ★⟦ ρ★ ⟧ η✦₂)
T⇛ᵣ-preserves-⟦T⟧ ρ★ η✦₂ (` x)      = ⟦ρ★⟧-preserves-lookup x ρ★ η✦₂
T⇛ᵣ-preserves-⟦T⟧ ρ★ η✦₂ (T₁ ⇒ T₂)  rewrite T⇛ᵣ-preserves-⟦T⟧ ρ★ η✦₂ T₁ | T⇛ᵣ-preserves-⟦T⟧ ρ★ η✦₂ T₂ = refl
T⇛ᵣ-preserves-⟦T⟧ ρ★ η✦₂ (∀α ℓ , T) = dep-ext λ ⟦α⟧ → T⇛ᵣ-preserves-⟦T⟧ (ρ★ T↑ᵣ _) (⟦α⟧ ∷ η✦₂) T

{-# REWRITE T⇛ᵣ-preserves-⟦T⟧ #-}

Tdropₛ : (ℓ ∷ Δ₁) T⇛ₛ Δ₂ → Δ₁ T⇛ₛ Δ₂
Tdropₛ σ★ _ x = σ★ _ (there x)

σ★⟦_⟧_ : Δ₁ T⇛ₛ Δ₂ → Env✦ Δ₂ → Env✦ Δ₁
σ★⟦_⟧_ {Δ₁ = []}    σ★ η✦₂ = []
σ★⟦_⟧_ {Δ₁ = _ ∷ _} σ★ η✦₂ = T⟦ σ★ _ (here refl) ⟧ η✦₂ ∷ σ★⟦ (Tdropₛ σ★) ⟧ η✦₂

Tsemantic-coincidence : (ρ★ : Δ₁ T⇛ᵣ Δ₂) (η✦₂ : Env✦ Δ₂) → (σ★⟦ ρ★ T≫ᵣₛ Tidₛ ⟧ η✦₂) ≡ω (ρ★⟦ ρ★ ⟧ η✦₂)
Tsemantic-coincidence {[]}     ρ★ η✦₂ = refl
Tsemantic-coincidence {x ∷ Δ₁} ρ★ η✦₂ = cong-ωω (lookup η✦₂ (ρ★ x (here refl)) ∷_) (Tsemantic-coincidence {Δ₁ = Δ₁} (Tdropᵣ ρ★) η✦₂)

{-# REWRITE Tsemantic-coincidence #-}

⟦σ★⟧-preserves-wk : (σ★ : Δ₁ T⇛ₛ Δ₂) → (⟦T⟧ : Set ℓ) → (η✦₂ : Env✦ Δ₂) → 
  (σ★⟦ σ★ T≫ₛᵣ Twkᵣ ⟧ (⟦T⟧ ∷ η✦₂)) ≡ω (σ★⟦ σ★ ⟧ η✦₂)
⟦σ★⟧-preserves-wk {Δ₁ = []}     σ★ ⟦T⟧ η✦₂ = refl
⟦σ★⟧-preserves-wk {Δ₁ = l ∷ Δ₁} σ★ ⟦T⟧ η✦₂ = cong-ωω ((T⟦ (σ★ _ (here refl)) ⟧ η✦₂) ∷_) (⟦σ★⟧-preserves-wk (Tdropₛ σ★) ⟦T⟧ η✦₂)

{-# REWRITE ⟦σ★⟧-preserves-wk #-}

⟦σ★⟧-preserves-lookup : (x : ℓ ∈ Δ₁) (σ★ : Δ₁ T⇛ₛ Δ₂) (η✦₂ : Env✦ Δ₂) → lookup (σ★⟦ σ★ ⟧ η✦₂) x ≡ T⟦ σ★ ℓ x ⟧ η✦₂
⟦σ★⟧-preserves-lookup (here refl) σ★ η₂ = refl
⟦σ★⟧-preserves-lookup (there x)   σ★ η₂ = ⟦σ★⟧-preserves-lookup x (Tdropₛ σ★) η₂

{-# REWRITE ⟦σ★⟧-preserves-lookup #-}

T⇛ₛ-preserves-⟦T⟧ : (σ★ : Δ₁ T⇛ₛ Δ₂) (η✦₂ : Env✦ Δ₂) (T : Type Δ₁ ℓ) → 
  T⟦ T T⋯ₛ σ★ ⟧ η✦₂ ≡ T⟦ T ⟧ (σ★⟦ σ★ ⟧ η✦₂)
T⇛ₛ-preserves-⟦T⟧ σ★ η✦₂ (` x)      = refl
T⇛ₛ-preserves-⟦T⟧ σ★ η✦₂ (T₁ ⇒ T₂)  rewrite T⇛ₛ-preserves-⟦T⟧ σ★ η✦₂ T₁ | T⇛ₛ-preserves-⟦T⟧ σ★ η✦₂ T₂ = refl
T⇛ₛ-preserves-⟦T⟧ σ★ η✦₂ (∀α ℓ , T) = dep-ext λ ⟦α⟧ → T⇛ₛ-preserves-⟦T⟧ (σ★ T↑ₛ _) (⟦α⟧ ∷ η✦₂) T

{-# REWRITE T⇛ₛ-preserves-⟦T⟧ #-}

Ctx✦ : Ctx Δ → Env✦ Δ → Setω
Ctx✦ Γ η✦ = ∀ ℓ (T : Type _ ℓ) → (x : T ∈# Γ) → T⟦ T ⟧ η✦

_،✦_ : Ctx✦ Γ η✦ → T⟦ T ⟧ η✦ → Ctx✦ (Γ ، T) η✦
(Γ✦ ،✦ ⟦T⟧) _ _ here = ⟦T⟧
(Γ✦ ،✦ ⟦T⟧) _ _ (there x) = Γ✦ _ _ x

_،★✦_ : Ctx✦ Γ η✦ → (⟦T⟧ : Set ℓ) → Ctx✦ (Γ ،★ ℓ) (⟦T⟧ ∷ η✦)
_،★✦_ {η✦ = η✦} Γ✦ ⟦T⟧ _ _ (tskip {T = T} x) = Γ✦ _ _ x

E⟦_⟧ : Expr Γ T → Ctx✦ Γ η✦ → T⟦ T ⟧ η✦
E⟦ ` x      ⟧ Γ✦ = Γ✦ _ _ x
E⟦ λx e     ⟧ Γ✦ = λ ⟦x⟧ → E⟦ e ⟧ (Γ✦ ،✦ ⟦x⟧)
E⟦ Λα ℓ , e ⟧ Γ✦ = λ ⟦α⟧ → E⟦ e ⟧ (Γ✦ ،★✦ ⟦α⟧)
E⟦ e₁ · e₂  ⟧ Γ✦ = E⟦ e₁ ⟧ Γ✦ (E⟦ e₂ ⟧ Γ✦)
E⟦ e ∙ T    ⟧ Γ✦ = E⟦ e ⟧ Γ✦ (T⟦ T ⟧ _) 

Edropᵣ : (Γ₁ ، T) E⇛ᵣ[ ρ★ ] Γ₂ → Γ₁ E⇛ᵣ[ ρ★ ] Γ₂
Edropᵣ ρ _ _ x = ρ _ _ (there x)

Eℓdropᵣ : (Γ₁ ،★ ℓ) E⇛ᵣ[ ρ★ ] Γ₂ → Γ₁ E⇛ᵣ[ Tdropᵣ ρ★ ] Γ₂
Eℓdropᵣ ρ _ _ x = ρ _ _ (tskip x)

ρ⟦_⟧_ : {η✦₂ : Env✦ Δ₂} {ρ★ : Δ₁ T⇛ᵣ Δ₂} →
  Γ₁ E⇛ᵣ[ ρ★ ] Γ₂ → Ctx✦ Γ₂ η✦₂ → Ctx✦ Γ₁ (ρ★⟦ ρ★ ⟧ η✦₂)
ρ⟦_⟧_ {Γ₁ = ∅}        ρ Γ✦₂ = λ ℓ T ()
ρ⟦_⟧_ {Γ₁ = Γ₁ ، T}   ρ Γ✦₂ = (ρ⟦ Edropᵣ ρ ⟧ Γ✦₂) ،✦ E⟦ ` ρ _ _ here ⟧ Γ✦₂
ρ⟦_⟧_ {Γ₁ = Γ₁ ،★ ℓ} {η✦₂ = η✦₂} {ρ★ = ρ★} ρ Γ✦₂ = (ρ⟦ Eℓdropᵣ ρ ⟧ Γ✦₂) ،★✦ T⟦ ` ρ★ _ (here refl) ⟧ η✦₂

⟦ρ⟧-preserves-wk : {η✦₂ : Env✦ Δ₂} {ρ★ : Δ₁ T⇛ᵣ Δ₂} {T : Type Δ₂ ℓ} → 
  (ρ : Γ₁ E⇛ᵣ[ ρ★ ] Γ₂) (Γ✦₂ : Ctx✦ Γ₂ η✦₂) (⟦e⟧ : T⟦ T ⟧ η✦₂)  →
  (ρ⟦ [ ρ★ ، Tidᵣ ] ρ E≫ᵣᵣ Ewkᵣ {T = T} ⟧ (Γ✦₂ ،✦ ⟦e⟧)) ≡ω (ρ⟦ ρ ⟧ Γ✦₂)
⟦ρ⟧-preserves-wk {Γ₁ = ∅}       ρ Γ✦₂ ⟦e⟧ = refl
⟦ρ⟧-preserves-wk {Γ₁ = _،_ {ℓ = ℓ} Γ₁ T} {ρ★ = ρ★} ρ Γ✦₂ ⟦e⟧ = cong-ωω (_،✦ Γ✦₂ ℓ (T T⋯ᵣ ρ★) (ρ ℓ T here)) (⟦ρ⟧-preserves-wk (Edropᵣ ρ) Γ✦₂ ⟦e⟧)
⟦ρ⟧-preserves-wk {Γ₁ = Γ₁ ،★ ℓ} {η✦₂ = η✦₂} {ρ★ = ρ★} ρ Γ✦₂ ⟦e⟧ = cong-ωω (_،★✦ lookup η✦₂ (ρ★ ℓ (here refl))) (⟦ρ⟧-preserves-wk (Eℓdropᵣ ρ) Γ✦₂ ⟦e⟧)

{-# REWRITE ⟦ρ⟧-preserves-wk #-}

data Value : Expr Γ T → Set where
  Val-λ  : Value (λx e)
  Val-Λ  : Value (Λα ℓ , e)

data _↪_ : Expr Γ T → Expr Γ T → Set where
  β-λ : 
    Value e₂ →
    ((λx e₁) · e₂) ↪ (e₁ E[ e₂ ])
  β-Λ : ∀ {T : Type Δ ℓ} {T' : Type (ℓ ∷ Δ) ℓ'} {e : Expr (Γ ،★ ℓ) T'} →
    ((Λα ℓ , e) ∙ T) ↪ (e ET[ T ])
  ξ-·₁ :
    e₁ ↪ e →
    (e₁ · e₂) ↪ (e · e₂)
  ξ-·₂ : 
    e₂ ↪ e → 
    Value e₁ →
    (e₁ · e₂) ↪ (e₁ · e)
  ξ-∙ : ∀ {T : Type Δ ℓ} {T' : Type (ℓ ∷ Δ) ℓ'} {e₁ e₂ : Expr Γ (∀α ℓ , T')} →
    e₁ ↪ e₂ →
    (e₁ ∙ T) ↪ (e₂ ∙ T)

soundness : ∀ {e₁ e₂ : Expr Γ T} →
  e₁ ↪ e₂ → (Γ✦ : Ctx✦ Γ η✦) → E⟦ e₁ ⟧ Γ✦ ≡ E⟦ e₂ ⟧ Γ✦
soundness (β-λ x)        Γ✦ = {! refl  !}
soundness β-Λ            Γ✦ = {!       !}
soundness (ξ-·₁ e₁↪e₂)   Γ✦ = {!       !}
soundness (ξ-·₂ e₁↪e₂ x) Γ✦ = {!       !} 
soundness (ξ-∙ e₁↪e₂)    Γ✦ = {!       !}       