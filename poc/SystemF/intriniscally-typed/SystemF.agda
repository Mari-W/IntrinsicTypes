{-# OPTIONS --rewriting #-}
module SystemF where

open import Level
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional public using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; trans; sym; module ≡-Reasoning)
open ≡-Reasoning

open import Agda.Builtin.Equality.Rewrite

postulate
  fun-ext : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} {f g : (x : A) → B x} →
    (∀ (x : A) → f x ≡ g x) →
    f ≡ g

variable 
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ' ℓ₁' ℓ₂' ℓ₃' : Level

Env = List Level

variable 
  Δ Δ₁ Δ₂ Δ₃ Δ' Δ₁' Δ₂' Δ₃' : Env

data Type : Env → Level → Set where
  `_    : ℓ ∈ Δ → Type Δ ℓ
  `ℕ    : Type Δ zero
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
`ℕ         T⋯ᵣ ρ = `ℕ
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

_T⋯ₛ_ : Type Δ₁ ℓ → Δ₁ T⇛ₛ Δ₂ → Type Δ₂ ℓ
_T≫ₛᵣ_ : Δ₁ T⇛ₛ Δ₂ → Δ₂ T⇛ᵣ Δ₃ → Δ₁ T⇛ₛ Δ₃

abstract 
  (σ₁ T≫ₛᵣ ρ₂) _ x = (σ₁ _ x) T⋯ᵣ ρ₂
  T≫ₛᵣ-def : (σ₁ : Δ₁ T⇛ₛ Δ₂) (ρ₂ : Δ₂ T⇛ᵣ Δ₃) (x : ℓ ∈ Δ₁) → (σ₁ T≫ₛᵣ ρ₂) _ x ≡ (σ₁ _ x) T⋯ᵣ ρ₂
  T≫ₛᵣ-def _ _ _ = refl

_T↑ₛ_ : Δ₁ T⇛ₛ Δ₂ → (ℓ : Level) → (ℓ ∷ Δ₁) T⇛ₛ (ℓ ∷ Δ₂)
ρ T↑ₛ _ = (` (here refl)) T∷ₛ (ρ T≫ₛᵣ Twkᵣ)

(` x)      T⋯ₛ σ = (σ _ x)
`ℕ         T⋯ₛ σ = `ℕ
(T₁ ⇒ T₂)  T⋯ₛ σ = (T₁ T⋯ₛ σ) ⇒ (T₂ T⋯ₛ σ)
(∀α ℓ , T) T⋯ₛ σ = ∀α ℓ , (T T⋯ₛ (σ T↑ₛ ℓ))

_T≫ₛₛ_ : Δ₁ T⇛ₛ Δ₂ → Δ₂ T⇛ₛ Δ₃ → Δ₁ T⇛ₛ Δ₃
abstract 
  (σ₁ T≫ₛₛ σ₂) _ x = (σ₁ _ x) T⋯ₛ σ₂
  T≫ₛₛ-def : (σ₁ : Δ₁ T⇛ₛ Δ₂) (σ₂ : Δ₂ T⇛ₛ Δ₃) (x : ℓ ∈ Δ₁) → (σ₁ T≫ₛₛ σ₂) _ x ≡ (σ₁ _ x) T⋯ₛ σ₂
  T≫ₛₛ-def _ _ _ = refl

_T[_] : Type (ℓ' ∷ Δ) ℓ → Type Δ ℓ' → Type Δ ℓ
T T[ T' ] = T T⋯ₛ (T' T∷ₛ Tidₛ) 

Tdistributivityᵣᵣ : (x : ℓ ∈ Δ₂) (ρ₁ : Δ₁ T⇛ᵣ Δ₂) (ρ₂ : Δ₂ T⇛ᵣ Δ₃) → (x T∷ᵣ ρ₁) T≫ᵣᵣ ρ₂ ≡ ρ₂ _ x T∷ᵣ (ρ₁ T≫ᵣᵣ ρ₂)
Tdistributivityᵣᵣ _ _ _ = fun-ext (λ _ → fun-ext λ { (here refl) → T≫ᵣᵣ-def _ _ _ ; (there x) → trans (T≫ᵣᵣ-def _ _ _) (sym (T≫ᵣᵣ-def _ _ _)) })

Tdistributivityᵣₛ : (x : ℓ ∈ Δ₂) (ρ₁ : Δ₁ T⇛ᵣ Δ₂) (σ₂ : Δ₂ T⇛ₛ Δ₃) → (x T∷ᵣ ρ₁) T≫ᵣₛ σ₂ ≡ σ₂ _ x T∷ₛ (ρ₁ T≫ᵣₛ σ₂)
Tdistributivityᵣₛ _ _ _ = fun-ext (λ _ → fun-ext λ { (here refl) → T≫ᵣₛ-def _ _ _ ; (there x) → trans (T≫ᵣₛ-def _ _ _) (sym (T≫ᵣₛ-def _ _ _)) })

Tdistributivityₛᵣ : (T : Type Δ₂ ℓ) (σ₁ : Δ₁ T⇛ₛ Δ₂) (ρ₂ : Δ₂ T⇛ᵣ Δ₃) → (T T∷ₛ σ₁) T≫ₛᵣ ρ₂ ≡ (T T⋯ᵣ ρ₂) T∷ₛ (σ₁ T≫ₛᵣ ρ₂)
Tdistributivityₛᵣ _ _ _ = fun-ext (λ _ → fun-ext λ { (here refl) → T≫ₛᵣ-def _ _ _ ; (there x) → trans (T≫ₛᵣ-def _ _ _) (sym (T≫ₛᵣ-def _ _ _)) })

Tdistributivityₛₛ : (T : Type Δ₂ ℓ) (σ₁ : Δ₁ T⇛ₛ Δ₂) (σ₂ : Δ₂ T⇛ₛ Δ₃) → (T T∷ₛ σ₁) T≫ₛₛ σ₂ ≡ (T T⋯ₛ σ₂) T∷ₛ (σ₁ T≫ₛₛ σ₂)
Tdistributivityₛₛ _ _ _ = fun-ext (λ _ → fun-ext λ { (here refl) → T≫ₛₛ-def _ _ _ ; (there x) → trans (T≫ₛₛ-def _ _ _) (sym (T≫ₛₛ-def _ _ _)) })

Tη-id : _T∷ᵣ_ {ℓ = ℓ} {Δ₁ = Δ} (here refl) Twkᵣ ≡ Tidᵣ 
Tη-id = fun-ext (λ _ → fun-ext λ { (here refl) → refl ; (there x) → refl })

Tη-law : (σ : (ℓ ∷ Δ₁) T⇛ₛ Δ₂) → (σ _ (here refl)) T∷ₛ (Twkᵣ T≫ᵣₛ σ) ≡ σ
Tη-law _ = fun-ext λ _ → fun-ext λ { (here refl) → refl ; (there x) → T≫ᵣₛ-def Twkᵣ _ x }

{-# REWRITE Tη-id Tη-law #-}

{-# REWRITE T≫ᵣᵣ-def T≫ᵣₛ-def T≫ₛᵣ-def T≫ₛₛ-def #-}

{-# REWRITE Tdistributivityᵣᵣ Tdistributivityᵣₛ Tdistributivityₛᵣ Tdistributivityₛₛ #-}

Tfusionᵣᵣ : (ρ₁ : Δ₁ T⇛ᵣ Δ₂) (ρ₂ : Δ₂ T⇛ᵣ Δ₃) (T : Type Δ₁ ℓ) → (T T⋯ᵣ ρ₁) T⋯ᵣ ρ₂ ≡ T T⋯ᵣ (ρ₁ T≫ᵣᵣ ρ₂)
Tfusionᵣᵣ ρ₁ ρ₂ (` x)      = refl
Tfusionᵣᵣ ρ₁ ρ₂ `ℕ         = refl
Tfusionᵣᵣ ρ₁ ρ₂ (T₁ ⇒ T₂)  = cong₂ _⇒_ (Tfusionᵣᵣ ρ₁ ρ₂ T₁) (Tfusionᵣᵣ ρ₁ ρ₂ T₂)
Tfusionᵣᵣ ρ₁ ρ₂ (∀α ℓ , T) = cong (∀α ℓ ,_) (Tfusionᵣᵣ (ρ₁ T↑ᵣ ℓ) (ρ₂ T↑ᵣ ℓ) T)

{-# REWRITE Tfusionᵣᵣ #-}

Tfusionᵣₛ : (ρ₁ : Δ₁ T⇛ᵣ Δ₂) (σ₂ : Δ₂ T⇛ₛ Δ₃)  (T : Type Δ₁ ℓ) → (T T⋯ᵣ ρ₁) T⋯ₛ σ₂ ≡ T T⋯ₛ (ρ₁ T≫ᵣₛ σ₂)
Tfusionᵣₛ ρ₁ σ₂ (` x)      = refl
Tfusionᵣₛ ρ₁ σ₂ `ℕ         = refl
Tfusionᵣₛ ρ₁ σ₂ (T₁ ⇒ T₂)  = cong₂ _⇒_ (Tfusionᵣₛ ρ₁ σ₂ T₁) (Tfusionᵣₛ ρ₁ σ₂ T₂)
Tfusionᵣₛ ρ₁ σ₂ (∀α ℓ , T) = cong (∀α ℓ ,_) (Tfusionᵣₛ (ρ₁ T↑ᵣ ℓ) (σ₂ T↑ₛ ℓ) T)

{-# REWRITE Tfusionᵣₛ #-}

Tfusionₛᵣ : (σ₁ : Δ₁ T⇛ₛ Δ₂) (ρ₂ : Δ₂ T⇛ᵣ Δ₃)  (T : Type Δ₁ ℓ) → (T T⋯ₛ σ₁) T⋯ᵣ ρ₂ ≡ T T⋯ₛ (σ₁ T≫ₛᵣ ρ₂)
Tfusionₛᵣ σ₁ ρ₂ (` x)      = refl
Tfusionₛᵣ σ₁ ρ₂ `ℕ         = refl
Tfusionₛᵣ σ₁ ρ₂ (T₁ ⇒ T₂)  = cong₂ _⇒_ (Tfusionₛᵣ σ₁ ρ₂ T₁) (Tfusionₛᵣ σ₁ ρ₂ T₂)
Tfusionₛᵣ σ₁ ρ₂ (∀α ℓ , T) = cong (∀α ℓ ,_) (Tfusionₛᵣ (σ₁ T↑ₛ ℓ) (ρ₂ T↑ᵣ ℓ) T)

{-# REWRITE Tfusionₛᵣ #-}

Tfusionₛₛ : (σ₁ : Δ₁ T⇛ₛ Δ₂) (σ₂ : Δ₂ T⇛ₛ Δ₃)  (T : Type Δ₁ ℓ) → (T T⋯ₛ σ₁) T⋯ₛ σ₂ ≡ T T⋯ₛ (σ₁ T≫ₛₛ σ₂)
Tfusionₛₛ σ₁ σ₂ (` x)      = refl
Tfusionₛₛ σ₁ σ₂ `ℕ         = refl
Tfusionₛₛ σ₁ σ₂ (T₁ ⇒ T₂)  = cong₂ _⇒_ (Tfusionₛₛ σ₁ σ₂ T₁) (Tfusionₛₛ σ₁ σ₂ T₂)
Tfusionₛₛ σ₁ σ₂ (∀α ℓ , T) = cong (∀α ℓ ,_) (Tfusionₛₛ (σ₁ T↑ₛ ℓ) (σ₂ T↑ₛ ℓ) T)

{-# REWRITE Tfusionₛₛ #-}

⋯Tidᵣ : (T : Type Δ ℓ) → T T⋯ᵣ Tidᵣ ≡ T 
⋯Tidᵣ (` x)        = refl
⋯Tidᵣ (`ℕ)         = refl
⋯Tidᵣ (T₁ ⇒ T₂)    = cong₂ _⇒_ (⋯Tidᵣ T₁) (⋯Tidᵣ T₂)
⋯Tidᵣ (∀α ℓ , T)   = cong (∀α ℓ ,_) (⋯Tidᵣ T)

↑Tidₛ : _T∷ₛ_ {ℓ = ℓ} {Δ₁ = Δ} (` here refl) (Tidₛ T≫ₛᵣ Twkᵣ) ≡ Tidₛ 
↑Tidₛ = fun-ext (λ _ → fun-ext λ { (here refl) → refl ; (there x) → refl })

⋯Tidₛ : (T : Type Δ ℓ) → T T⋯ₛ Tidₛ ≡ T 
⋯Tidₛ (` x)        = refl
⋯Tidₛ (`ℕ)         = refl
⋯Tidₛ (T₁ ⇒ T₂)    = cong₂ _⇒_ (⋯Tidₛ T₁) (⋯Tidₛ T₂)
⋯Tidₛ (∀α ℓ , T)   = cong (∀α ℓ ,_) (subst (λ σ → (T T⋯ₛ σ ) ≡ T) (sym ↑Tidₛ) (⋯Tidₛ T))

{-# REWRITE ↑Tidₛ ⋯Tidᵣ ⋯Tidₛ #-}

T↑coincidence : {ρ : Δ₁ T⇛ᵣ Δ₂} → ((ρ T↑ᵣ ℓ) T≫ᵣₛ Tidₛ) ≡ (ρ T≫ᵣₛ Tidₛ) T↑ₛ ℓ
T↑coincidence = fun-ext (λ _ → fun-ext λ { (here refl) → refl ; (there x) → refl })

Tcoincidence : (ρ : Δ₁ T⇛ᵣ Δ₂) (T : Type Δ₁ ℓ) → T T⋯ₛ (ρ T≫ᵣₛ Tidₛ) ≡ T T⋯ᵣ ρ
Tcoincidence ρ (` x)        = refl
Tcoincidence ρ (`ℕ)         = refl
Tcoincidence ρ (T₁ ⇒ T₂)    = cong₂ _⇒_ (Tcoincidence ρ T₁) (Tcoincidence ρ T₂)
Tcoincidence ρ (∀α ℓ , T)   = cong (∀α ℓ ,_) (subst (λ σ → T T⋯ₛ σ ≡ (T T⋯ᵣ (ρ T↑ᵣ ℓ))) T↑coincidence (Tcoincidence (ρ T↑ᵣ ℓ) T))

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

data Expr : {Δ : Env} → Ctx Δ → Type Δ ℓ → Set where
  `_    : T ∈# Γ → Expr Γ T
  λx_   : Expr (Γ ، T') T → Expr Γ T 
  Λα_,_ : (ℓ : Level) → {T : Type (ℓ ∷ Δ) ℓ'} → Expr (Γ ،★ ℓ) T → Expr Γ (∀α ℓ , T)
  _·_   : Expr Γ (T₁ ⇒ T₂) → Expr Γ T₁ → Expr Γ T₂
  _∙_   : {T : Type (ℓ ∷ Δ) ℓ'} → Expr Γ (∀α ℓ , T) → (T' : Type Δ ℓ) → Expr Γ (T T[ T' ])

variable 
  e e₁ e₂ e₃ e' e₁' e₂' e₃' : Expr Γ T 

_E⇛ᵣ[_]_ : Ctx Δ₁ → Δ₁ T⇛ᵣ Δ₂ → Ctx Δ₂ → Set
_E⇛ᵣ[_]_ {Δ₁}{Δ₂} Γ₁ ρ★ Γ₂ = ∀ ℓ (T : Type Δ₁ ℓ) → T ∈# Γ₁ →  (T T⋯ᵣ ρ★) ∈# Γ₂

Eidᵣ : Γ E⇛ᵣ[ Tidᵣ ] Γ
Eidᵣ _ _ x = x

Ewkᵣ : Γ E⇛ᵣ[ Tidᵣ ] (Γ ، T) 
Ewkᵣ _ _ x = there x 

Eℓwkᵣ : Γ E⇛ᵣ[ Twkᵣ ] (Γ ،★ ℓ) 
Eℓwkᵣ _ _ x = tskip x

_E∷ᵣ_ : (T T⋯ᵣ ρ★) ∈# Γ₂ → Γ₁ E⇛ᵣ[ ρ★ ] Γ₂ → (Γ₁ ، T) E⇛ᵣ[ ρ★ ] Γ₂
(x E∷ᵣ _) _ _ here      = x
(_ E∷ᵣ ρ) _ _ (there x) = ρ _ _ x

_Eℓ∷ᵣ_ : (x : ℓ ∈ Δ₂) → Γ₁ E⇛ᵣ[ ρ★ ] Γ₂ → (Γ₁ ،★ ℓ) E⇛ᵣ[ x T∷ᵣ ρ★ ] Γ₂
(_ Eℓ∷ᵣ ρ) _ _ (tskip x) = ρ _ _ x 

_E≫ᵣᵣ_ : Γ₁ E⇛ᵣ[ ρ★₁ ] Γ₂ → Γ₂ E⇛ᵣ[ ρ★₂ ] Γ₃ → Γ₁ E⇛ᵣ[ ρ★₁ T≫ᵣᵣ ρ★₂ ] Γ₃
abstract 
  (ρ₁ E≫ᵣᵣ ρ₂) _ _ x = ρ₂ _ _ (ρ₁ _ _ x)
  E≫ᵣᵣ-def : (ρ★₁ : Δ₁ T⇛ᵣ Δ₂) (ρ★₂ :  Δ₂ T⇛ᵣ Δ₃) (ρ₁ : Γ₁ E⇛ᵣ[ ρ★₁ ] Γ₂) (ρ₂ : Γ₂ E⇛ᵣ[ ρ★₂ ] Γ₃) (T : Type Δ₁ ℓ) (x : T ∈# Γ₁) → 
    (ρ₁ E≫ᵣᵣ ρ₂) _ _ x ≡ ρ₂ _ _ (ρ₁ _ _ x)
  E≫ᵣᵣ-def _ _ _ _ _ _ = refl

_E↑ᵣ_ : Γ₁ E⇛ᵣ[ ρ★ ] Γ₂ → (T : Type Δ₁ ℓ) → (Γ₁ ، T) E⇛ᵣ[ ρ★ ] (Γ₂ ، (T T⋯ᵣ ρ★))
(ρ E↑ᵣ _) = here E∷ᵣ (_E≫ᵣᵣ_ {ρ★₂ = Tidᵣ} ρ Ewkᵣ)

_Eℓ↑ᵣ_ : Γ₁ E⇛ᵣ[ ρ★ ] Γ₂ → (ℓ : Level) → (Γ₁ ،★ ℓ) E⇛ᵣ[ ρ★ T↑ᵣ ℓ ] (Γ₂ ،★ ℓ)
(ρ Eℓ↑ᵣ _) = here refl Eℓ∷ᵣ (ρ E≫ᵣᵣ Eℓwkᵣ)

_E⋯ᵣ_ : Expr Γ₁ T → Γ₁ E⇛ᵣ[ ρ★ ] Γ₂ → Expr Γ₂ (T T⋯ᵣ ρ★)
(` x)      E⋯ᵣ ρ          = ` (ρ _ _ x)
(λx e)     E⋯ᵣ ρ          = λx (e E⋯ᵣ (ρ E↑ᵣ _))
(Λα ℓ , e) E⋯ᵣ ρ          = Λα ℓ , (e E⋯ᵣ (ρ Eℓ↑ᵣ ℓ))
(e₁ · e₂)  E⋯ᵣ ρ          = (e₁ E⋯ᵣ ρ) · (e₂ E⋯ᵣ ρ)
_E⋯ᵣ_ {ρ★ = ρ★} (e ∙ T) ρ = (e E⋯ᵣ ρ) ∙ (T T⋯ᵣ ρ★)

Ewk : Expr Γ T → Expr (Γ ، T') T 
Ewk e = _E⋯ᵣ_ {ρ★ = Tidᵣ} e Ewkᵣ

Eℓwk : Expr Γ T → Expr (Γ ،★ ℓ) (Twk T)
Eℓwk e = _E⋯ᵣ_ {ρ★ = Twkᵣ} e Eℓwkᵣ

_E⇛ₛ[_]_ : Ctx Δ₁ → Δ₁ T⇛ₛ Δ₂ → Ctx Δ₂ → Set
_E⇛ₛ[_]_ {Δ₁}{Δ₂} Γ₁ σ★ Γ₂ = ∀ ℓ (T : Type Δ₁ ℓ) → T ∈# Γ₁ →  Expr Γ₂ (T T⋯ₛ σ★)

Eidₛ : Γ E⇛ₛ[ Tidₛ ] Γ
Eidₛ _ _ = `_

_E∷ₛ_ : Expr Γ₂ (T T⋯ₛ σ★) → Γ₁ E⇛ₛ[ σ★ ] Γ₂ → (Γ₁ ، T) E⇛ₛ[ σ★ ] Γ₂
(T E∷ₛ _) _ _ here      = T
(_ E∷ₛ σ) _ _ (there x) = σ _ _ x

_Eℓ∷ₛ_ : (T : Type Δ₂ ℓ) → Γ₁ E⇛ₛ[ σ★ ] Γ₂ → (Γ₁ ،★ ℓ) E⇛ₛ[ T T∷ₛ σ★ ] Γ₂
(_ Eℓ∷ₛ σ) _ _ (tskip x) = σ _ _ x 

_E≫ᵣₛ_ : Γ₁ E⇛ᵣ[ ρ★₁ ] Γ₂ → Γ₂ E⇛ₛ[ σ★₂ ] Γ₃ → Γ₁ E⇛ₛ[ ρ★₁ T≫ᵣₛ σ★₂ ] Γ₃
abstract 
  (ρ₁ E≫ᵣₛ σ₂) _ _ x = σ₂ _ _ (ρ₁ _ _ x)
  E≫ᵣₛ-def : (ρ★₁ : Δ₁ T⇛ᵣ Δ₂) (σ★₂ : Δ₂ T⇛ₛ Δ₃) (ρ₁ : Γ₁ E⇛ᵣ[ ρ★₁ ] Γ₂) (σ₂ : Γ₂ E⇛ₛ[ σ★₂ ] Γ₃) (T : Type Δ₁ ℓ) (x : T ∈# Γ₁) → 
    (_E≫ᵣₛ_ {σ★₂ = σ★₂} ρ₁ σ₂) _ _ x ≡ σ₂ _ _ (ρ₁ _ _ x)
  E≫ᵣₛ-def _ _ _ _ _ _ = refl

_E≫ₛᵣ_ : Γ₁ E⇛ₛ[ σ★₁ ] Γ₂ → Γ₂ E⇛ᵣ[ ρ★₂ ] Γ₃ → Γ₁ E⇛ₛ[ σ★₁ T≫ₛᵣ ρ★₂ ] Γ₃
_E⋯ₛ_ : Expr Γ₁ T → Γ₁ E⇛ₛ[ σ★ ] Γ₂ → Expr Γ₂ (T T⋯ₛ σ★)

abstract 
  (σ₁ E≫ₛᵣ ρ₂) _ _ x = (σ₁ _ _ x) E⋯ᵣ ρ₂
  E≫ₛᵣ-def : (σ★₁ : Δ₁ T⇛ₛ Δ₂) (ρ★₂ : Δ₂ T⇛ᵣ Δ₃) (σ₁ : Γ₁ E⇛ₛ[ σ★₁ ] Γ₂) (ρ₂ : Γ₂ E⇛ᵣ[ ρ★₂ ] Γ₃) (T : Type Δ₁ ℓ) (x : T ∈# Γ₁) → 
    (_E≫ₛᵣ_ {σ★₁ = σ★₁} σ₁ ρ₂) _ _ x ≡ (σ₁ _ _ x) E⋯ᵣ ρ₂
  E≫ₛᵣ-def _ _ _ _ _ _ = refl
 
_E↑ₛ_ : Γ₁ E⇛ₛ[ σ★ ] Γ₂ → (T : Type Δ₁ ℓ) → (Γ₁ ، T) E⇛ₛ[ σ★ ] (Γ₂ ، (T T⋯ₛ σ★))
_E↑ₛ_ {σ★ = σ★} σ _ = _E∷ₛ_ {σ★ = σ★} (` here) (_E≫ₛᵣ_ {σ★₁ = σ★} {ρ★₂ = Tidᵣ} σ Ewkᵣ)

_Eℓ↑ₛ_ : Γ₁ E⇛ₛ[ σ★ ] Γ₂ → (ℓ : Level) → (Γ₁ ،★ ℓ) E⇛ₛ[ σ★ T↑ₛ ℓ ] (Γ₂ ،★ ℓ)
_Eℓ↑ₛ_ {σ★ = σ★} σ _ = _Eℓ∷ₛ_ {σ★ = σ★ T≫ₛᵣ Twkᵣ} ((` here refl)) (_E≫ₛᵣ_ {σ★₁ = σ★} {ρ★₂ = Twkᵣ} σ Eℓwkᵣ)

(` x) E⋯ₛ                  σ = σ _ _ x 
_E⋯ₛ_ {σ★ = σ★} (λx e)     σ = λx (_E⋯ₛ_ {σ★ = σ★} e (_E↑ₛ_ {σ★ = σ★} σ _))
_E⋯ₛ_ {σ★ = σ★} (Λα ℓ , e) σ = Λα ℓ , (_E⋯ₛ_ {σ★ = σ★ T↑ₛ _} e (_Eℓ↑ₛ_ {σ★ = σ★} σ ℓ))
_E⋯ₛ_ {σ★ = σ★} (e₁ · e₂)  σ = (_E⋯ₛ_ {σ★ = σ★} e₁ σ) · (_E⋯ₛ_ {σ★ = σ★} e₂ σ)
_E⋯ₛ_ {σ★ = σ★} (e ∙ T)    σ = (_E⋯ₛ_ {σ★ = σ★} e σ) ∙ (T T⋯ₛ σ★)

_E≫ₛₛ_ : Γ₁ E⇛ₛ[ σ★₁ ] Γ₂ → Γ₂ E⇛ₛ[ σ★₂ ] Γ₃ → Γ₁ E⇛ₛ[ σ★₁ T≫ₛₛ σ★₂ ] Γ₃
abstract 
  _E≫ₛₛ_ {σ★₁ = σ★₁} {σ★₂ = σ★₂} σ₁ σ₂ _ _ x = _E⋯ₛ_ {σ★ = σ★₂} (σ₁ _ _ x) σ₂
  E≫ₛₛ-def : (σ★₁ : Δ₁ T⇛ₛ Δ₂) (σ★₂ : Δ₂ T⇛ₛ Δ₃) (σ₁ : Γ₁ E⇛ₛ[ σ★₁ ] Γ₂) (σ₂ : Γ₂ E⇛ₛ[ σ★₂ ] Γ₃) (T : Type Δ₁ ℓ) (x : T ∈# Γ₁) → 
     (_E≫ₛₛ_ {σ★₁ = σ★₁} {σ★₂ = σ★₂} σ₁ σ₂) _ _ x ≡ _E⋯ₛ_ {σ★ = σ★₂} (σ₁ _ _ x) σ₂
  E≫ₛₛ-def _ _ _ _ _ _ = refl

_E[_] : Expr (Γ ، T') T → Expr Γ T' →  Expr Γ T
e E[ e' ] = _E⋯ₛ_ {σ★ = Tidₛ} e (_E∷ₛ_ {σ★ = Tidₛ} e' Eidₛ) 

_ET[_] : Expr (Γ ،★ ℓ) T → (T' : Type Δ ℓ) →  Expr Γ (T T[ T' ])
e ET[ T ] = _E⋯ₛ_ {σ★ = T T∷ₛ Tidₛ} e (_Eℓ∷ₛ_ {σ★ = Tidₛ} T Eidₛ)

Edistributivityᵣᵣ : (ρ★₁ : Δ₁ T⇛ᵣ Δ₂) (ρ★₂ :  Δ₂ T⇛ᵣ Δ₃) (T : Type Δ₁ ℓ) (x : (T T⋯ᵣ ρ★₁) ∈# Γ₂)
  (ρ₁ : Γ₁ E⇛ᵣ[ ρ★₁ ] Γ₂) (ρ₂ : Γ₂ E⇛ᵣ[ ρ★₂ ] Γ₃) → (_E∷ᵣ_ {T = T} x ρ₁) E≫ᵣᵣ ρ₂ ≡ ρ₂ _ _ x E∷ᵣ (ρ₁ E≫ᵣᵣ ρ₂)  
Edistributivityᵣᵣ _ _ _ _ _ _ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { here → E≫ᵣᵣ-def _ _ _ _ _ _ ; (there x) → trans (E≫ᵣᵣ-def _ _ _ _ _ _) (sym (E≫ᵣᵣ-def _ _ _ _ _ _)) }

Edistributivityᵣₛ : (ρ★₁ : Δ₁ T⇛ᵣ Δ₂) (σ★₂ :  Δ₂ T⇛ₛ Δ₃) (T : Type Δ₁ ℓ) (x : (T T⋯ᵣ ρ★₁) ∈# Γ₂)
  (ρ₁ : Γ₁ E⇛ᵣ[ ρ★₁ ] Γ₂) (σ₂ : Γ₂ E⇛ₛ[ σ★₂ ] Γ₃) → _E≫ᵣₛ_ {σ★₂ = σ★₂} (_E∷ᵣ_ {T = T} x ρ₁) σ₂ ≡ _E∷ₛ_ {σ★ = ρ★₁ T≫ᵣₛ σ★₂} (σ₂ _ _ x) (_E≫ᵣₛ_ {σ★₂ = σ★₂} ρ₁ σ₂)  
Edistributivityᵣₛ _ _ _ _ _ _ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { here → E≫ᵣₛ-def _ _ _ _ _ _ ; (there x) → trans (E≫ᵣₛ-def _ _ _ _ _ _) (sym (E≫ᵣₛ-def _ _ _ _ _ _)) }

Edistributivityₛᵣ : (σ★₁ : Δ₁ T⇛ₛ Δ₂) (ρ★₂ : Δ₂ T⇛ᵣ Δ₃) (T : Type Δ₁ ℓ) (e : Expr Γ₂ (T T⋯ₛ σ★₁))
  (σ₁ : Γ₁ E⇛ₛ[ σ★₁ ] Γ₂) (ρ₂ : Γ₂ E⇛ᵣ[ ρ★₂ ] Γ₃) → _E≫ₛᵣ_ {σ★₁ = σ★₁} (_E∷ₛ_ {T = T} {σ★ = σ★₁} e σ₁) ρ₂ ≡ _E∷ₛ_ {σ★ = σ★₁ T≫ₛᵣ ρ★₂} (e E⋯ᵣ ρ₂) (_E≫ₛᵣ_ {σ★₁ = σ★₁} σ₁ ρ₂)  
Edistributivityₛᵣ _ _ _ _ _ _ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { here → E≫ₛᵣ-def _ _ _ _ _ _ ; (there x) → trans (E≫ₛᵣ-def _ _ _ _ _ _) (sym (E≫ₛᵣ-def _ _ _ _ _ _)) }

Edistributivityₛₛ : (σ★₁ : Δ₁ T⇛ₛ Δ₂) (σ★₂ : Δ₂ T⇛ₛ Δ₃) (T : Type Δ₁ ℓ) (e : Expr Γ₂ (T T⋯ₛ σ★₁))
  (σ₁ : Γ₁ E⇛ₛ[ σ★₁ ] Γ₂) (σ₂ : Γ₂ E⇛ₛ[ σ★₂ ] Γ₃) → _E≫ₛₛ_ {σ★₁ = σ★₁} {σ★₂ = σ★₂} (_E∷ₛ_ {T = T} {σ★ = σ★₁} e σ₁) σ₂ ≡ _E∷ₛ_ {σ★ = σ★₁ T≫ₛₛ σ★₂} (_E⋯ₛ_ {σ★ = σ★₂} e σ₂) (_E≫ₛₛ_ {σ★₁ = σ★₁} {σ★₂ = σ★₂} σ₁ σ₂)  
Edistributivityₛₛ _ _ _ _ _ _ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { here → E≫ₛₛ-def _ _ _ _ _ _ ; (there x) → trans (E≫ₛₛ-def _ _ _ _ _ _) (sym (E≫ₛₛ-def _ _ _ _ _ _)) }

Eℓdistributivityᵣᵣ : (ρ★₁ : Δ₁ T⇛ᵣ Δ₂) (ρ★₂ :  Δ₂ T⇛ᵣ Δ₃) (x : ℓ ∈ Δ₂) (ρ₁ : Γ₁ E⇛ᵣ[ ρ★₁ ] Γ₂) (ρ₂ : Γ₂ E⇛ᵣ[ ρ★₂ ] Γ₃) → 
  (x Eℓ∷ᵣ ρ₁) E≫ᵣᵣ ρ₂ ≡ ρ★₂ _ x Eℓ∷ᵣ (ρ₁ E≫ᵣᵣ ρ₂)  
Eℓdistributivityᵣᵣ _ _ _ _ _ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { (tskip x) → 
  trans (E≫ᵣᵣ-def _ _ _ _ _ _) (sym (E≫ᵣᵣ-def _ _ _ _ _ _)) }

Eℓdistributivityᵣₛ : (ρ★₁ : Δ₁ T⇛ᵣ Δ₂) (σ★₂ :  Δ₂ T⇛ₛ Δ₃) (x : ℓ ∈ Δ₂) (ρ₁ : Γ₁ E⇛ᵣ[ ρ★₁ ] Γ₂) (σ₂ : Γ₂ E⇛ₛ[ σ★₂ ] Γ₃) → 
  _E≫ᵣₛ_ {σ★₂ = σ★₂} (x Eℓ∷ᵣ ρ₁) σ₂ ≡ _Eℓ∷ₛ_ {σ★ = ρ★₁ T≫ᵣₛ σ★₂} (σ★₂ _ x) (_E≫ᵣₛ_ {σ★₂ = σ★₂} ρ₁ σ₂)  
Eℓdistributivityᵣₛ _ _ _ _ _ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { (tskip x) → trans (E≫ᵣₛ-def _ _ _ _ _ _) (sym (E≫ᵣₛ-def _ _ _ _ _ _)) }

Eℓdistributivityₛᵣ : (σ★₁ : Δ₁ T⇛ₛ Δ₂) (ρ★₂ : Δ₂ T⇛ᵣ Δ₃) (T : Type Δ₂ ℓ) (σ₁ : Γ₁ E⇛ₛ[ σ★₁ ] Γ₂) (ρ₂ : Γ₂ E⇛ᵣ[ ρ★₂ ] Γ₃) → 
  _E≫ₛᵣ_ {σ★₁ = T T∷ₛ σ★₁} (_Eℓ∷ₛ_ {σ★ = σ★₁} T σ₁) ρ₂ ≡ (_Eℓ∷ₛ_ {σ★ = σ★₁ T≫ₛᵣ ρ★₂} (T T⋯ᵣ ρ★₂) (_E≫ₛᵣ_ {σ★₁ = σ★₁} σ₁ ρ₂))
Eℓdistributivityₛᵣ _ _ _ _ _ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { (tskip x) → trans (E≫ₛᵣ-def _ _ _ _ _ _) (sym (E≫ₛᵣ-def _ _ _ _ _ _)) }

Eℓdistributivityₛₛ : (σ★₁ : Δ₁ T⇛ₛ Δ₂) (σ★₂ : Δ₂ T⇛ₛ Δ₃) (T : Type Δ₂ ℓ) (σ₁ : Γ₁ E⇛ₛ[ σ★₁ ] Γ₂) (σ₂ : Γ₂ E⇛ₛ[ σ★₂ ] Γ₃) → 
  _E≫ₛₛ_ {σ★₁ = T T∷ₛ σ★₁} {σ★₂ = σ★₂} (_Eℓ∷ₛ_ {σ★ = σ★₁} T σ₁) σ₂ ≡ (_Eℓ∷ₛ_ {σ★ = σ★₁ T≫ₛₛ σ★₂} (T T⋯ₛ σ★₂) (_E≫ₛₛ_ {σ★₁ = σ★₁} {σ★₂ = σ★₂} σ₁ σ₂))
Eℓdistributivityₛₛ _ _ _ _ _ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { (tskip x) → trans (E≫ₛₛ-def _ _ _ _ _ _) (sym (E≫ₛₛ-def _ _ _ _ _ _)) }

Eη-id : _E∷ᵣ_ {ρ★ = Tidᵣ} {Γ₁ = Γ} here (Ewkᵣ {T = T}) ≡ Eidᵣ 
Eη-id = fun-ext (λ _ → fun-ext λ _ → fun-ext λ { here → refl ; (there x) → refl })

Eη-law : (T : Type Δ₁ ℓ) (σ★ : Δ₁ T⇛ₛ Δ₂) (σ : (Γ₁ ، T) E⇛ₛ[ σ★ ] Γ₂) → _E∷ₛ_ {σ★ = σ★} (σ _ _ here) (_E≫ᵣₛ_ {ρ★₁ = Tidᵣ} {σ★₂ = σ★} Ewkᵣ σ) ≡ σ
Eη-law _ _ _ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { (here) → refl ; (there x) → E≫ᵣₛ-def _ _ _ _ _ _ }

Eℓη-id : (ℓ : Level) (Γ : Ctx Δ) → _Eℓ∷ᵣ_ {ℓ = ℓ} {Γ₁ = Γ} (here refl) (Eℓwkᵣ) ≡ Eidᵣ 
Eℓη-id _ _ = fun-ext (λ _ → fun-ext λ _ → fun-ext λ { (tskip x) → refl })

-- TODO: is this correct?
Eℓη-law : (T : Type Δ₂ ℓ) (σ★ : Δ₁ T⇛ₛ Δ₂) (σ : (Γ₁ ،★  ℓ) E⇛ₛ[ T T∷ₛ σ★ ] Γ₂) → 
  _Eℓ∷ₛ_ {σ★ = σ★} ((T T∷ₛ σ★) _ (here refl)) (_E≫ᵣₛ_ {σ★₂ = T T∷ₛ σ★} Eℓwkᵣ σ) ≡ σ
Eℓη-law _ _ _ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { (tskip x) → E≫ᵣₛ-def _ _ _ _ _ _ }

{-# REWRITE Eη-id Eη-law #-}
{-# REWRITE Eℓη-law Eℓη-law #-}

{-# REWRITE E≫ᵣᵣ-def E≫ᵣₛ-def E≫ₛᵣ-def E≫ₛₛ-def #-}

{-# REWRITE Edistributivityᵣᵣ Edistributivityᵣₛ Edistributivityₛᵣ Edistributivityₛₛ #-}
{-# REWRITE Eℓdistributivityᵣᵣ Eℓdistributivityᵣₛ Eℓdistributivityₛᵣ Eℓdistributivityₛₛ #-}

Efusionᵣᵣ : (T : Type Δ₁ ℓ) (ρ★₁ : Δ₁ T⇛ᵣ Δ₂) (ρ★₂ :  Δ₂ T⇛ᵣ Δ₃) (ρ₁ : Γ₁ E⇛ᵣ[ ρ★₁ ] Γ₂) (ρ₂ : Γ₂ E⇛ᵣ[ ρ★₂ ] Γ₃) (e : Expr Γ₁ T) → 
  (e E⋯ᵣ ρ₁) E⋯ᵣ ρ₂ ≡ e E⋯ᵣ (ρ₁ E≫ᵣᵣ ρ₂)
Efusionᵣᵣ _ _   _   ρ₁ ρ₂ (` x)      = refl
Efusionᵣᵣ _ _   _   ρ₁ ρ₂ (λx e)     = cong λx_ (Efusionᵣᵣ _ _ _ (ρ₁ E↑ᵣ _) (ρ₂ E↑ᵣ _) e) 
Efusionᵣᵣ _ _   _   ρ₁ ρ₂ (Λα ℓ , e) = cong (Λα ℓ ,_) (Efusionᵣᵣ _ _ _ (ρ₁ Eℓ↑ᵣ _) (ρ₂ Eℓ↑ᵣ _) e)
Efusionᵣᵣ _ _   _   ρ₁ ρ₂ (e₁ · e₂)  = cong₂ _·_ (Efusionᵣᵣ _ _ _ ρ₁ ρ₂ e₁) (Efusionᵣᵣ _ _ _ ρ₁ ρ₂ e₂)
Efusionᵣᵣ _ ρ★₁ ρ★₂ ρ₁ ρ₂ (_∙_ e T') = cong (_∙ _) (Efusionᵣᵣ _ _ _ ρ₁ ρ₂ e)

{-# REWRITE Efusionᵣᵣ #-}

Efusionᵣₛ : {Γ₁ : Ctx Δ₁} (T : Type Δ₁ ℓ) (ρ★₁ : Δ₁ T⇛ᵣ Δ₂) (σ★₂ : Δ₂ T⇛ₛ Δ₃) (ρ₁ : Γ₁ E⇛ᵣ[ ρ★₁ ] Γ₂) (σ₂ : Γ₂ E⇛ₛ[ σ★₂ ] Γ₃) (e : Expr Γ₁ T) → 
  _E⋯ₛ_ {σ★ = σ★₂} (e E⋯ᵣ ρ₁) σ₂ ≡ _E⋯ₛ_ {σ★ = ρ★₁ T≫ᵣₛ σ★₂} e (_E≫ᵣₛ_ {σ★₂ = σ★₂} ρ₁ σ₂)
Efusionᵣₛ _ ρ★₁ σ★₂ ρ₁ σ₂ (` x)      = refl
Efusionᵣₛ _ ρ★₁ σ★₂ ρ₁ σ₂ (λx e)     = cong λx_ (Efusionᵣₛ _ _ _ (ρ₁ E↑ᵣ _) (_E↑ₛ_ {σ★ = σ★₂} σ₂ _) e) 
Efusionᵣₛ _ ρ★₁ σ★₂ ρ₁ σ₂ (Λα ℓ , e) = cong (Λα ℓ ,_) (Efusionᵣₛ _ _ _ (ρ₁ Eℓ↑ᵣ _) (_Eℓ↑ₛ_ {σ★ = σ★₂} σ₂ _) e)
Efusionᵣₛ _ ρ★₁ σ★₂ ρ₁ σ₂ (e₁ · e₂)  = cong₂ _·_ (Efusionᵣₛ _ _ _ ρ₁ σ₂ e₁) (Efusionᵣₛ _ _ _ ρ₁ σ₂ e₂)
Efusionᵣₛ .(T T[ T' ]) ρ★₁ σ★₂ ρ₁ σ₂ (_∙_ {T = T} e T') = cong (_∙ (T' T⋯ₛ (ρ★₁ T≫ᵣₛ σ★₂))) (Efusionᵣₛ _ _ _ ρ₁ σ₂ e)

{-# REWRITE Efusionᵣₛ #-}

-- Eassocᵣₛᵣ : ∀{Δ₄ Γ₄}  (ρ★₁ : Δ₁ T⇛ᵣ Δ₂) (σ★₂ : Δ₂ T⇛ₛ Δ₃) (ρ★₃ : Δ₃ T⇛ᵣ Δ₄)  
--              (ρ₁ : Γ₁ E⇛ᵣ[ ρ★₁ ] Γ₂) (σ₂ : Γ₂ E⇛ₛ[ σ★₂ ] Γ₃) (ρ₃ : Γ₃ E⇛ᵣ[ ρ★₃ ] Γ₄) → 
--              _E≫ₛᵣ_ {σ★₁ = ρ★₁ T≫ᵣₛ σ★₂} (_E≫ᵣₛ_ {σ★₂ = σ★₂} ρ₁ σ₂) ρ₃ ≡ _E≫ᵣₛ_ {σ★₂ = σ★₂ T≫ₛᵣ ρ★₃} ρ₁ (_E≫ₛᵣ_ {σ★₁ = σ★₂} σ₂ ρ₃)
-- Eassocᵣₛᵣ σ★₁ _ _ ρ₁ σ₂ ρ₃ = refl

Eassocₛᵣᵣ : ∀ {Δ₄ Γ₄} (σ★₁ : Δ₁ T⇛ₛ Δ₂) (ρ★₂ : Δ₂ T⇛ᵣ Δ₃) (ρ★₃ : Δ₃ T⇛ᵣ Δ₄)  
             (σ₁ : Γ₁ E⇛ₛ[ σ★₁ ] Γ₂) (ρ₂ : Γ₂ E⇛ᵣ[ ρ★₂ ] Γ₃) (ρ₃ : Γ₃ E⇛ᵣ[ ρ★₃ ] Γ₄) → 
             _E≫ₛᵣ_ {σ★₁ = σ★₁ T≫ₛᵣ ρ★₂} (_E≫ₛᵣ_ {σ★₁ = σ★₁} σ₁ ρ₂) ρ₃ ≡ _E≫ₛᵣ_ {σ★₁ = σ★₁} σ₁ (ρ₂ E≫ᵣᵣ ρ₃)
Eassocₛᵣᵣ σ★₁ _ _ σ₁ ρ₂ ρ₃ = fun-ext λ _ → fun-ext λ T → fun-ext λ { x → Efusionᵣᵣ (T T⋯ₛ σ★₁) _ _ ρ₂ ρ₃ (σ₁ _ _ x) }
{-# REWRITE Eassocₛᵣᵣ #-}

Eassocₛᵣₛ : ∀{Δ₄ Γ₄}  (σ★₁ : Δ₁ T⇛ₛ Δ₂) (ρ★₂ : Δ₂ T⇛ᵣ Δ₃) (σ★₃ : Δ₃ T⇛ₛ Δ₄)  
             (σ₁ : Γ₁ E⇛ₛ[ σ★₁ ] Γ₂) (ρ₂ : Γ₂ E⇛ᵣ[ ρ★₂ ] Γ₃) (σ₃ : Γ₃ E⇛ₛ[ σ★₃ ] Γ₄) → 
             _E≫ₛₛ_ {σ★₁ = σ★₁ T≫ₛᵣ ρ★₂} {σ★₂ = σ★₃} (_E≫ₛᵣ_ {σ★₁ = σ★₁} σ₁ ρ₂) σ₃ ≡ _E≫ₛₛ_ {σ★₁ = σ★₁} {σ★₂ = ρ★₂ T≫ᵣₛ σ★₃} σ₁ (_E≫ᵣₛ_ {σ★₂ = σ★₃} ρ₂  σ₃)
Eassocₛᵣₛ σ★₁ _ _ σ₁ ρ₂ σ₃ = fun-ext λ _ → fun-ext λ T → fun-ext λ { x → Efusionᵣₛ (T T⋯ₛ σ★₁) _ _ ρ₂ σ₃ (σ₁ _ _ x) }
{-# REWRITE Eassocₛᵣₛ #-}

-- Einteractₛ : (T : Type Δ₁ ℓ) (σ★ : Δ₁ T⇛ₛ Δ₂) (e : Expr Γ₂ (T T⋯ₛ σ★)) (σ : Γ₁ E⇛ₛ[ σ★ ] Γ₂) → 
--   _E≫ᵣₛ_ {σ★₂ = σ★} (Ewkᵣ {T = T}) (_E∷ₛ_ {σ★ = σ★} e σ) ≡ σ
-- Einteractₛ _ _ _ _ = refl


E↑fusionₛᵣ : (T' : Type Δ₁ ℓ) (T : Type Δ₁ ℓ) (σ★₁ : Δ₁ T⇛ₛ Δ₂) (ρ★₂ : Δ₂ T⇛ᵣ Δ₃) (σ₁ : Γ₁ E⇛ₛ[ σ★₁ ] Γ₂) (ρ₂ : Γ₂ E⇛ᵣ[ ρ★₂ ] Γ₃) (e : Expr (Γ₁ ، T') T) → 
    _E⋯ᵣ_ (_E⋯ₛ_ {σ★ = σ★₁} e (_E↑ₛ_ {σ★ = σ★₁} σ₁ T')) (ρ₂ E↑ᵣ (T' T⋯ₛ σ★₁)) ≡ _E⋯ₛ_ {σ★ = σ★₁ T≫ₛᵣ ρ★₂} e ((_E↑ₛ_ {σ★ = σ★₁ T≫ₛᵣ ρ★₂} (_E≫ₛᵣ_ {σ★₁ = σ★₁} σ₁ ρ₂)) T')
E↑fusionₛᵣ _ _ _ _ _ _ _ = {!   !} 

Efusionₛᵣ : (T : Type Δ₁ ℓ) (σ★₁ : Δ₁ T⇛ₛ Δ₂) (ρ★₂ : Δ₂ T⇛ᵣ Δ₃) (σ₁ : Γ₁ E⇛ₛ[ σ★₁ ] Γ₂) (ρ₂ : Γ₂ E⇛ᵣ[ ρ★₂ ] Γ₃) (e : Expr Γ₁ T) → 
  _E⋯ᵣ_ (_E⋯ₛ_ {σ★ = σ★₁} e σ₁) ρ₂ ≡ _E⋯ₛ_ {σ★ = σ★₁ T≫ₛᵣ ρ★₂} e (_E≫ₛᵣ_ {σ★₁ = σ★₁} σ₁ ρ₂)
Efusionₛᵣ _ σ★₁ ρ★₂ σ₁ ρ₂ (` x)      = refl
-- want:
--  (σ₁ E≫ₛᵣ (ρ₂ E≫ᵣᵣ wkᵣ)
-- have: 
--  (σ₁ E≫ₛᵣ Ewkᵣ) E≫ₛᵣ (here E∷ᵣ (ρ₂ E≫ᵣᵣ Ewkᵣ))
-- (e E⋯ₛ ((` here) E∷ₛ
--         ((λ z T₁ ℓ₁ → σ₁ z T₁ ℓ₁ E⋯ᵣ (λ z₁ T₂ → there)) E≫ₛᵣ
--          (here E∷ᵣ (ρ₂ E≫ᵣᵣ (λ z z₁ x → there x))))))
--       ≡ (e E⋯ₛ ((` here) E∷ₛ (σ₁ E≫ₛᵣ (ρ₂ E≫ᵣᵣ (λ z T₁ → there)))))
Efusionₛᵣ T σ★₁ ρ★₂ σ₁ ρ₂ (λx_ {T' = T'} e) = cong λx_ (begin 
    _
  ≡⟨ Efusionₛᵣ T σ★₁ ρ★₂ (_E↑ₛ_ {σ★ = σ★₁} σ₁ T') (ρ₂ E↑ᵣ _) e ⟩ 
    _
  ≡⟨ {!   !} ⟩ 
    _
  ≡⟨ cong (λ σ → _E⋯ₛ_ {σ★ = σ★₁ T≫ₛᵣ ρ★₂} e (_E∷ₛ_ {σ★ = σ★₁ T≫ₛᵣ ρ★₂} (` here) σ)) (Eassocₛᵣᵣ σ★₁ ρ★₂ Tidᵣ σ₁ ρ₂ Ewkᵣ) ⟩
    _
  ∎)
-- cong λx_ (trans (Efusionₛᵣ T σ★₁ ρ★₂ (_E↑ₛ_ {σ★ = σ★₁} σ₁ T') (ρ₂ E↑ᵣ _) e) (Efusionₛᵣ T σ★₁ ρ★₂ σ₁ {!   !} {! λx e  !}))
Efusionₛᵣ _ σ★₁ ρ★₂ σ₁ ρ₂ (Λα ℓ , e) = {!   !} --cong (Λα ℓ ,_) (Efusionₛᵣ _ σ★₁ ρ★₂ ? ? e)
Efusionₛᵣ _ σ★₁ ρ★₂ σ₁ ρ₂ (e₁ · e₂)  = cong₂ _·_ (Efusionₛᵣ _ _ _ σ₁ ρ₂ e₁) (Efusionₛᵣ _ σ★₁ _ σ₁ ρ₂ e₂)
Efusionₛᵣ .(T T[ T' ]) σ★₁ ρ★₂ σ₁ ρ₂ (_∙_ {T = T} e T') = cong (_∙ (T' T⋯ₛ (σ★₁ T≫ₛᵣ ρ★₂))) (Efusionₛᵣ _ _ _ σ₁ ρ₂ e)

-- {-# REWRITE Efusionₛᵣ #-}