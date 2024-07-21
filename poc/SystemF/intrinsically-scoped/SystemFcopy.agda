{-# OPTIONS --rewriting #-}
module SystemFcopy where

-- Imports ---------------------------------------------------------------------

open import Function using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; trans; sym; module ≡-Reasoning)
open ≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; ∃-syntax)
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Membership.Propositional public using (_∈_)


open import Agda.Builtin.Equality.Rewrite

postulate
  -- probably could get rid of this with a little effort
  fun-ext : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} {f g : (x : A) → B x} →
    (∀ (x : A) → f x ≡ g x) →
    f ≡ g

-- Sorts -----------------------------------------------------------------------

data Sort : Set where 
  expr : Sort
  type : Sort 
  kind : Sort 

variable
  s s₁ s₂ s₃ s₄ s' s₁' s₂' s₃' s₄' : Sort
  S S₁ S₂ S₃ S₄ S' S₁' S₂' S₃' S₄' : List Sort
  
-- Syntax ----------------------------------------------------------------------

data _⊢_ : List Sort → Sort → Set where
  `_       : s ∈ S → S ⊢ s    
  λx_     : (expr ∷ S) ⊢ expr → S ⊢ expr
  Λα_     : (type ∷ S) ⊢ expr → S ⊢ expr
  ∀[α∶_]_ : S ⊢ kind → (type ∷ S) ⊢ type → S ⊢ type
  _·_     : S ⊢ expr → S ⊢ expr → S ⊢ expr
  _∙_     : S ⊢ expr → S ⊢ type → S ⊢ expr
  _⇒_     : S ⊢ type → S ⊢ type → S ⊢ type
  ★       : S ⊢ kind

variable
  x x₁ x₂ x₃ x₄ x' x₁' x₂' x₃' x₄' : s ∈ S
  e e₁ e₂ e₃ e₄ e' e₁' e₂' e₃' e₄' : S ⊢ expr
  t t₁ t₂ t₃ t₄ t' t₁' t₂' t₃' t₄' : S ⊢ type
  k k₁ k₂ k₃ k₄ k' k₁' k₂' k₃' k₄' : S ⊢ kind

-- Substitution ----------------------------------------------------------------

_⇛ᵣ_ : List Sort → List Sort → Set
S₁ ⇛ᵣ S₂ = ∀ s → s ∈ S₁ → s ∈ S₂

idᵣ : S ⇛ᵣ S
idᵣ _ = id

wkᵣ : S ⇛ᵣ (s ∷ S)
wkᵣ _ x = there x
  
_∷ᵣ_ : s ∈ S₂ → S₁ ⇛ᵣ S₂ → (s ∷ S₁) ⇛ᵣ S₂
(x ∷ᵣ _) _ (here refl) = x
(_ ∷ᵣ ρ) _ (there x) = ρ _ x

_≫ᵣᵣ_ : S₁ ⇛ᵣ S₂ → S₂ ⇛ᵣ S₃ → S₁ ⇛ᵣ S₃
(ρ₁ ≫ᵣᵣ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)
_↑ᵣ_ : S₁ ⇛ᵣ S₂ → (s : Sort) → (s ∷ S₁) ⇛ᵣ (s ∷ S₂)
ρ ↑ᵣ _ = here refl ∷ᵣ (ρ ≫ᵣᵣ wkᵣ)

_⋯ᵣ_ : S₁ ⊢ s → S₁ ⇛ᵣ S₂ → S₂ ⊢ s
(` x)         ⋯ᵣ ρ = ` (ρ _ x)
(λx e)        ⋯ᵣ ρ = λx (e ⋯ᵣ (ρ ↑ᵣ expr))
(Λα e)        ⋯ᵣ ρ = Λα (e ⋯ᵣ (ρ ↑ᵣ type))
(∀[α∶ k ] t)  ⋯ᵣ ρ = ∀[α∶ k ⋯ᵣ ρ ] (t ⋯ᵣ (ρ ↑ᵣ type))
(e₁ · e₂)     ⋯ᵣ ρ = (e₁ ⋯ᵣ ρ) · (e₂ ⋯ᵣ ρ)
(e ∙ t)       ⋯ᵣ ρ = (e ⋯ᵣ ρ) ∙ (t ⋯ᵣ ρ)
(t₁ ⇒ t₂)     ⋯ᵣ ρ = (t₁ ⋯ᵣ ρ) ⇒ (t₂ ⋯ᵣ ρ)
★             ⋯ᵣ ρ = ★ 

wk : S ⊢ s → (s' ∷ S) ⊢ s
wk T = T ⋯ᵣ wkᵣ

_⇛ₛ_ : List Sort → List Sort → Set
S₁ ⇛ₛ S₂ = ∀ s → s ∈ S₁ → S₂ ⊢ s

idₛ : S ⇛ₛ S
idₛ _ = `_
  
_∷ₛ_ : S₂ ⊢ s → S₁ ⇛ₛ S₂ → (s ∷ S₁) ⇛ₛ S₂
(T ∷ₛ _) _ (here refl) = T
(_ ∷ₛ σ) _ (there x) = σ _ x

_≫ᵣₛ_ : S₁ ⇛ᵣ S₂ → S₂ ⇛ₛ S₃ → S₁ ⇛ₛ S₃
(ρ₁ ≫ᵣₛ σ₂) _ x = σ₂ _ (ρ₁ _ x)

_≫ₛᵣ_ : S₁ ⇛ₛ S₂ → S₂ ⇛ᵣ S₃ → S₁ ⇛ₛ S₃
(σ₁ ≫ₛᵣ ρ₂) _ x = (σ₁ _ x) ⋯ᵣ ρ₂

_↑ₛ_ : S₁ ⇛ₛ S₂ → (s : Sort) → (s ∷ S₁) ⇛ₛ (s ∷ S₂)
(σ ↑ₛ _) = (` (here refl)) ∷ₛ (σ ≫ₛᵣ wkᵣ)

_⋯ₛ_ : S₁ ⊢ s → S₁ ⇛ₛ S₂ → S₂ ⊢ s
(` x)         ⋯ₛ σ = (σ _ x)
(λx e)        ⋯ₛ σ = λx (e ⋯ₛ (σ ↑ₛ expr))
(Λα e)        ⋯ₛ σ = Λα (e ⋯ₛ (σ ↑ₛ type))
(∀[α∶ k ] t)  ⋯ₛ σ = ∀[α∶ k ⋯ₛ σ ] (t ⋯ₛ (σ ↑ₛ type))
(e₁ · e₂)     ⋯ₛ σ = (e₁ ⋯ₛ σ) · (e₂ ⋯ₛ σ)
(e ∙ t)       ⋯ₛ σ = (e ⋯ₛ σ) ∙ (t ⋯ₛ σ)
(t₁ ⇒ t₂)     ⋯ₛ σ = (t₁ ⋯ₛ σ) ⇒ (t₂ ⋯ₛ σ)
★             ⋯ₛ σ = ★ 

_≫ₛₛ_ :  S₁ ⇛ₛ S₂ → S₂ ⇛ₛ S₃ → S₁ ⇛ₛ S₃
(σ₁ ≫ₛₛ σ₂) _ x = (σ₁ _ x) ⋯ₛ σ₂

_[_] : (s' ∷ S) ⊢ s → S ⊢ s' → S ⊢ s
T [ T' ] = T ⋯ₛ (T' ∷ₛ idₛ) 

η-id : _∷ᵣ_ {s = s} {S₁ = S₁} (here refl) wkᵣ ≡ idᵣ 
η-id = fun-ext (λ _ → fun-ext λ { (here refl) → refl ; (there x) → refl })

η-law : _∷ₛ_ {s = s} {S₁ = S₁} (` (here refl)) (wkᵣ ≫ᵣₛ idₛ) ≡ idₛ
η-law = fun-ext λ _ → fun-ext λ { (here refl) → refl ; (there x) → refl }

{-# REWRITE η-id η-law #-}

distributivityᵣᵣ : (x : s ∈ S₂) (ρ₁ : S₁ ⇛ᵣ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) → (λ z x₁ → ρ₂ z ((x ∷ᵣ ρ₁) z x₁)) ≡ ρ₂ _ x ∷ᵣ (ρ₁ ≫ᵣᵣ ρ₂)  
distributivityᵣᵣ _ _ _ = fun-ext (λ _ → fun-ext λ { (here refl) → refl ; (there x) → refl })

distributivityᵣₛ : (x : s ∈ S₂) (ρ₁ : S₁ ⇛ᵣ S₂) (σ₂ : S₂ ⇛ₛ S₃) → (x ∷ᵣ ρ₁) ≫ᵣₛ σ₂ ≡ σ₂ _ x ∷ₛ (ρ₁ ≫ᵣₛ σ₂)
distributivityᵣₛ _ _ _ = fun-ext (λ _ → fun-ext λ { (here refl) → refl ; (there x) → refl })

distributivityₛᵣ : (T : S₂ ⊢ s) (σ₁ : S₁ ⇛ₛ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) → (T ∷ₛ σ₁) ≫ₛᵣ ρ₂ ≡ (T ⋯ᵣ ρ₂) ∷ₛ (σ₁ ≫ₛᵣ ρ₂)
distributivityₛᵣ _ _ _ = fun-ext (λ _ → fun-ext λ { (here refl) → refl ; (there x) → refl })

distributivityₛₛ : (T : S₂ ⊢ s) (σ₁ : S₁ ⇛ₛ S₂) (σ₂ : S₂ ⇛ₛ S₃) → (T ∷ₛ σ₁) ≫ₛₛ σ₂ ≡ (T ⋯ₛ σ₂) ∷ₛ (σ₁ ≫ₛₛ σ₂)
distributivityₛₛ _ _ _ = fun-ext (λ _ → fun-ext λ { (here refl) → refl ; (there x) → refl })

{-# REWRITE distributivityᵣᵣ distributivityᵣₛ distributivityₛᵣ distributivityₛₛ #-}
