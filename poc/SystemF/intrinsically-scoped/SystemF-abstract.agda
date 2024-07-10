{-# OPTIONS --rewriting #-}
module SystemF-abstract where

-- Imports ---------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; ∃-syntax)
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional public using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst)
open import Function using (id)

open import Agda.Builtin.Equality.Rewrite

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

_⇛ₛ_ : List Sort → List Sort → Set
S₁ ⇛ₛ S₂ = ∀ s → s ∈ S₁ → S₂ ⊢ s

abstract 
  idᵣ : S ⇛ᵣ S
  idᵣ _ = id
  
  wkᵣ : S ⇛ᵣ (s ∷ S)
  wkᵣ s x = there x
  
  _∷ᵣ_ : s ∈ S₂ → S₁ ⇛ᵣ S₂ → (s ∷ S₁) ⇛ᵣ S₂
  (x ∷ᵣ _) _ (here refl) = x
  (x ∷ᵣ ρ) _ (there x') = ρ _ x'

  _≫ᵣᵣ_ : S₁ ⇛ᵣ S₂ → S₂ ⇛ᵣ S₃ → S₁ ⇛ᵣ S₃
  (ρ₁ ≫ᵣᵣ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)
  
  _⋯ᵣ_ : S₁ ⊢ s → S₁ ⇛ᵣ S₂ → S₂ ⊢ s
  (` x)         ⋯ᵣ ρ = ` (ρ _ x)
  (λx e)        ⋯ᵣ ρ = λx (e ⋯ᵣ (here refl ∷ᵣ (ρ ≫ᵣᵣ wkᵣ)))
  (Λα e)        ⋯ᵣ ρ = Λα (e ⋯ᵣ (here refl ∷ᵣ (ρ ≫ᵣᵣ wkᵣ)))
  (∀[α∶ k ] t)  ⋯ᵣ ρ = ∀[α∶ k ⋯ᵣ ρ ] (t ⋯ᵣ (here refl ∷ᵣ (ρ ≫ᵣᵣ wkᵣ)))
  (e₁ · e₂)     ⋯ᵣ ρ = (e₁ ⋯ᵣ ρ) · (e₂ ⋯ᵣ ρ)
  (e ∙ t)       ⋯ᵣ ρ = (e ⋯ᵣ ρ) ∙ (t ⋯ᵣ ρ)
  (t₁ ⇒ t₂)     ⋯ᵣ ρ = (t₁ ⋯ᵣ ρ) ⇒ (t₂ ⋯ᵣ ρ)
  ★             ⋯ᵣ ρ = ★ 

  idₛ : S ⇛ₛ S
  idₛ _ = `_
  
  _∷ₛ_ : S₂ ⊢ s → S₁ ⇛ₛ S₂ → (s ∷ S₁) ⇛ₛ S₂
  (T ∷ₛ _) _ (here refl) = T
  (_ ∷ₛ σ) _ (there x) = σ _ x

  _≫ᵣₛ_ : S₁ ⇛ᵣ S₂ → S₂ ⇛ₛ S₃ → S₁ ⇛ₛ S₃
  (ρ₁ ≫ᵣₛ σ₂) _ x = σ₂ _ (ρ₁ _ x)

  _≫ₛᵣ_ : S₁ ⇛ₛ S₂ → S₂ ⇛ᵣ S₃ → S₁ ⇛ₛ S₃
  _⋯ₛ_ : S₁ ⊢ s → S₁ ⇛ₛ S₂ → S₂ ⊢ s

  (σ₁ ≫ₛᵣ ρ₂) _ x = (σ₁ _ x) ⋯ᵣ ρ₂

  (` x)         ⋯ₛ σ = (σ _ x)
  (λx e)        ⋯ₛ σ = λx (e ⋯ₛ ((` (here refl)) ∷ₛ (σ ≫ₛᵣ wkᵣ)))
  (Λα e)        ⋯ₛ σ = Λα (e ⋯ₛ ((` (here refl)) ∷ₛ (σ ≫ₛᵣ wkᵣ)))
  (∀[α∶ k ] t)  ⋯ₛ σ = ∀[α∶ k ⋯ₛ σ ] (t ⋯ₛ ((` (here refl)) ∷ₛ (σ ≫ₛᵣ wkᵣ)))
  (e₁ · e₂)     ⋯ₛ σ = (e₁ ⋯ₛ σ) · (e₂ ⋯ₛ σ)
  (e ∙ t)       ⋯ₛ σ = (e ⋯ₛ σ) ∙ (t ⋯ₛ σ)
  (t₁ ⇒ t₂)     ⋯ₛ σ = (t₁ ⋯ₛ σ) ⇒ (t₂ ⋯ₛ σ)
  ★             ⋯ₛ σ = ★ 
  
  _≫ₛₛ_ :  S₁ ⇛ₛ S₂ → S₂ ⇛ₛ S₃ → S₁ ⇛ₛ S₃
  (σ₁ ≫ₛₛ σ₂) _ x = (σ₁ _ x) ⋯ₛ σ₂


  -- The laws for the rewriting sytem and lemmas required to proof these laws:
  postulate
    -- Interaction Laws:
    left-idᵣᵣ  : (ρ : S₁ ⇛ᵣ S₂) → idᵣ ≫ᵣᵣ ρ ≡ ρ 
    right-idᵣᵣ : (ρ : S₁ ⇛ᵣ S₂) → ρ ≫ᵣᵣ idᵣ ≡ ρ
    left-idᵣₛ  : (σ : S₁ ⇛ₛ S₂) → idᵣ ≫ᵣₛ σ ≡ σ
    -- right-idᵣₛ : (ρ : S₁ ⇛ᵣ S₂) → ρ ≫ᵣₛ idₛ ≡ ? -- second most reduced form of a renaming that is used as substitution 
    -- left-idₛᵣ  : (ρ : S₁ ⇛ᵣ S₂) → idₛ ≫ₛᵣ ρ ≡ ? -- first most educed form of a renaming that is used as substitution 
    idᵣₛidₛᵣ   : (ρ : S₁ ⇛ᵣ S₂) → ρ ≫ᵣₛ idₛ ≡ idₛ ≫ₛᵣ ρ -- second reduces to first! (this is important homies)
    right-idₛᵣ : (σ : S₁ ⇛ₛ S₂) → σ ≫ₛᵣ idᵣ ≡ σ
    left-idₛₛ  : (σ : S₁ ⇛ₛ S₂) → idₛ ≫ₛₛ σ ≡ σ   
    right-idₛₛ : (σ : S₁ ⇛ₛ S₂) → σ ≫ₛₛ idₛ ≡ σ   
    assocᵣᵣᵣ   : (ρ₁ : S₁ ⇛ᵣ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) (ρ₃ : S₃ ⇛ᵣ S₄) → (ρ₁ ≫ᵣᵣ ρ₂) ≫ᵣᵣ ρ₃ ≡ ρ₁ ≫ᵣᵣ (ρ₂ ≫ᵣᵣ ρ₃)
    assocᵣᵣₛ   : (ρ₁ : S₁ ⇛ᵣ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) (σ₃ : S₃ ⇛ₛ S₄) → (ρ₁ ≫ᵣᵣ ρ₂) ≫ᵣₛ σ₃ ≡ ρ₁ ≫ᵣₛ (ρ₂ ≫ᵣₛ σ₃)
    assocᵣₛᵣ   : (ρ₁ : S₁ ⇛ᵣ S₂) (σ₂ : S₂ ⇛ₛ S₃) (ρ₃ : S₃ ⇛ᵣ S₄) → (ρ₁ ≫ᵣₛ σ₂) ≫ₛᵣ ρ₃ ≡ ρ₁ ≫ᵣₛ (σ₂ ≫ₛᵣ ρ₃) -- not included in equational theory as far as i understand 
    assocᵣₛₛ   : (ρ₁ : S₁ ⇛ᵣ S₂) (σ₂ : S₂ ⇛ₛ S₃) (σ₃ : S₃ ⇛ₛ S₄) → (ρ₁ ≫ᵣₛ σ₂) ≫ₛₛ σ₃ ≡ ρ₁ ≫ᵣₛ (σ₂ ≫ₛₛ σ₃) -- not included in equational theory as far as i understand 
    assocₛᵣᵣ   : (σ₁ : S₁ ⇛ₛ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) (ρ₃ : S₃ ⇛ᵣ S₄) → (σ₁ ≫ₛᵣ ρ₂) ≫ₛᵣ ρ₃ ≡ σ₁ ≫ₛᵣ (ρ₂ ≫ᵣᵣ ρ₃)
    assocₛᵣₛ   : (σ₁ : S₁ ⇛ₛ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) (σ₃ : S₃ ⇛ₛ S₄) → (σ₁ ≫ₛᵣ ρ₂) ≫ₛₛ σ₃ ≡ σ₁ ≫ₛₛ (ρ₂ ≫ᵣₛ σ₃)
    assocₛₛᵣ   : (σ₁ : S₁ ⇛ₛ S₂) (σ₂ : S₂ ⇛ₛ S₃) (ρ₃ : S₃ ⇛ᵣ S₄) → (σ₁ ≫ₛₛ σ₂) ≫ₛᵣ ρ₃ ≡ σ₁ ≫ₛₛ (σ₂ ≫ₛᵣ ρ₃)
    assocₛₛₛ   : (σ₁ : S₁ ⇛ₛ S₂) (σ₂ : S₂ ⇛ₛ S₃) (σ₃ : S₃ ⇛ₛ S₄) → (σ₁ ≫ₛₛ σ₂) ≫ₛₛ σ₃ ≡ σ₁ ≫ₛₛ (σ₂ ≫ₛₛ σ₃)

    distributivityᵣᵣ : (x : s ∈ S₂) (ρ₁ : S₁ ⇛ᵣ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) → (x ∷ᵣ ρ₁) ≫ᵣᵣ ρ₂ ≡ (ρ₂ _ x ∷ᵣ (ρ₁ ≫ᵣᵣ ρ₂)) -- not included in equational theory as far as i understand 
    distributivityᵣₛ : (x : s ∈ S₂) (ρ₁ : S₁ ⇛ᵣ S₂) (σ₂ : S₂ ⇛ₛ S₃) → (x ∷ᵣ ρ₁) ≫ᵣₛ σ₂ ≡ (σ₂ _ x ∷ₛ (ρ₁ ≫ᵣₛ σ₂)) -- not included in equational theory as far as i understand 
    distributivityₛᵣ : (T : S₂ ⊢ s) (σ₁ : S₁ ⇛ₛ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) → (T ∷ₛ σ₁) ≫ₛᵣ ρ₂ ≡ ((T ⋯ᵣ ρ₂) ∷ₛ (σ₁ ≫ₛᵣ ρ₂)) -- not included in equational theory as far as i understand 
    distributivityₛₛ : (T : S₂ ⊢ s) (σ₁ : S₁ ⇛ₛ S₂) (σ₂ : S₂ ⇛ₛ S₃) → (T ∷ₛ σ₁) ≫ₛₛ σ₂ ≡ ((T ⋯ₛ σ₂) ∷ₛ (σ₁ ≫ₛₛ σ₂))
    interactᵣ       : (x : s ∈ S₂) (ρ : S₁ ⇛ᵣ S₂) → wkᵣ ≫ᵣᵣ (x ∷ᵣ ρ) ≡ ρ -- not included in equational theory as far as i understand 
    interactₛ       : (T : S₂ ⊢ s) (σ : S₁ ⇛ₛ S₂) → wkᵣ ≫ᵣₛ (T ∷ₛ σ) ≡ σ
    η-id            : (S : List Sort) (s : Sort) → _∷ᵣ_ {s = s} {S₁ = S} (here refl) wkᵣ ≡ idᵣ
    η-law           : (σ : (s ∷ S₁) ⇛ₛ S₂) → (σ _ (here refl)) ∷ₛ (wkᵣ ≫ᵣₛ σ) ≡ σ

    -- Supplementary Laws:
    -- Monad Laws:
    -- Compositionality Lemmas:
    -- fusion↑ᵣᵣ : (T : (s ∷ S₁) ⊢ s') (ρ₁ : S₁ ⇛ᵣ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) (s' : Sort) → (T ⋯ᵣ (ρ₁ ↑ᵣ s)) ⋯ᵣ (ρ₂ ↑ᵣ s) ≡ T ⋯ᵣ ((ρ₁ ≫ᵣᵣ ρ₂) ↑ᵣ s)
    -- fusion↑ₛᵣ : (T : (s ∷ S₁) ⊢ s') (σ₁ : S₁ ⇛ₛ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) (s' : Sort) → (T ⋯ₛ (σ₁ ↑ₛ s)) ⋯ᵣ (ρ₂ ↑ᵣ s) ≡ T ⋯ₛ ((σ₁ ≫ₛᵣ ρ₂) ↑ₛ s)
    -- fusion↑ᵣₛ : (T : (s ∷ S₁) ⊢ s') (ρ₁ : S₁ ⇛ᵣ S₂) (σ₂ : S₂ ⇛ₛ S₃) (s' : Sort) → (T ⋯ᵣ (ρ₁ ↑ᵣ s)) ⋯ₛ (σ₂ ↑ₛ s) ≡ T ⋯ₛ ((ρ₁ ≫ᵣₛ σ₂) ↑ₛ s)
    -- fusion↑ₛₛ : (T : (s ∷ S₁) ⊢ s') (σ₁ : S₁ ⇛ₛ S₂) (σ₂ : S₂ ⇛ₛ S₃) (s' : Sort) → (T ⋯ₛ (σ₁ ↑ₛ s)) ⋯ₛ (σ₂ ↑ₛ s) ≡ T ⋯ₛ ((σ₁ ≫ₛₛ σ₂) ↑ₛ s)
    -- Compositionality Laws:
    fusionᵣᵣ : (T : S₁ ⊢ s) (ρ₁ : S₁ ⇛ᵣ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) → (T ⋯ᵣ ρ₁) ⋯ᵣ ρ₂ ≡ T ⋯ᵣ (ρ₁ ≫ᵣᵣ ρ₂)
    fusionₛᵣ : (T : S₁ ⊢ s) (σ₁ : S₁ ⇛ₛ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) → (T ⋯ₛ σ₁) ⋯ᵣ ρ₂ ≡ T ⋯ₛ (σ₁ ≫ₛᵣ ρ₂)
    fusionᵣₛ : (T : S₁ ⊢ s) (ρ₁ : S₁ ⇛ᵣ S₂) (σ₂ : S₂ ⇛ₛ S₃) → (T ⋯ᵣ ρ₁) ⋯ₛ σ₂ ≡ T ⋯ₛ (ρ₁ ≫ᵣₛ σ₂)
    fusionₛₛ : (T : S₁ ⊢ s) (σ₁ : S₁ ⇛ₛ S₂) (σ₂ : S₂ ⇛ₛ S₃) → (T ⋯ₛ σ₁) ⋯ₛ σ₂ ≡ T ⋯ₛ (σ₁ ≫ₛₛ σ₂)
    -- Right Identity Lemmas: 
    -- ↑idᵣ : (S : List Sort) (s : Sort) → _∷ᵣ_ {s = s} {S₁ = S} (here refl) wkᵣ ≡ idᵣ -- this is η-id
    -- ↑idₛ : (S : List Sort) (s : Sort) → _∷ₛ_ {s = s} {S₁ = S} (` (here refl))  (idₛ ≫ₛᵣ wkᵣ) ≡ idₛ
    -- Right Identity Laws:
    ⋯idᵣ : (T : S ⊢ s) → T ⋯ᵣ idᵣ ≡ T 
    ⋯idₛ : (T : S ⊢ s) → T ⋯ₛ idₛ ≡ T 
    -- Additional Laws: 
    coincidence : (T : S₁ ⊢ s) (ρ : S₁ ⇛ᵣ S₂) → T ⋯ₛ (ρ ≫ᵣₛ idₛ) ≡ T ⋯ᵣ ρ

    -- Syntactic Laws:
    -- These laws allow us to push renamings and substitutions into syntax homomorphically.
    -- We use the lifting when going under a binder and they all follow by definition.
    `_⋯ₛ_      : (x : s ∈ S₁) (σ : S₁ ⇛ₛ S₂) → (` x) ⋯ₛ σ ≡ σ s x 
    λx_⋯ₛ_     : (e : (expr ∷ S₁) ⊢ expr) (σ : S₁ ⇛ₛ S₂) → (λx e) ⋯ₛ σ ≡ (λx (e ⋯ₛ ((` (here refl)) ∷ₛ (σ ≫ₛᵣ wkᵣ))))
    Λα_⋯ₛ_     : (e : (type ∷ S₁) ⊢ expr) (σ : S₁ ⇛ₛ S₂) → (Λα e) ⋯ₛ σ ≡ (Λα (e ⋯ₛ ((` (here refl)) ∷ₛ (σ ≫ₛᵣ wkᵣ))))
    ∀[α∶_]_⋯ₛ_ : (k : S₁ ⊢ kind) (t : (type ∷ S₁) ⊢ type) (σ : S₁ ⇛ₛ S₂) → (∀[α∶ k ] t) ⋯ₛ σ ≡ ∀[α∶ k ⋯ₛ σ ] (t ⋯ₛ ((` (here refl)) ∷ₛ (σ ≫ₛᵣ wkᵣ)))
    _·_⋯ₛ_     : (e₁ : S₁ ⊢ expr) (e₂ : S₁ ⊢ expr) (σ : S₁ ⇛ₛ S₂) → (e₁ · e₂) ⋯ₛ σ ≡ (e₁ ⋯ₛ σ) · (e₂ ⋯ₛ σ)
    _∙_⋯ₛ_     : (e : S₁ ⊢ expr) (t : S₁ ⊢ type) (σ : S₁ ⇛ₛ S₂) → (e ∙ t) ⋯ₛ σ ≡ (e ⋯ₛ σ) ∙ (t ⋯ₛ σ)
    _⇒_⋯ₛ_     : (t₁ : S₁ ⊢ type) (t₂ : S₁ ⊢ type) (σ : S₁ ⇛ₛ S₂) → (t₁ ⇒ t₂) ⋯ₛ σ ≡ (t₁ ⋯ₛ σ) ⇒ (t₂ ⋯ₛ σ)
    ★⋯ₛ_       : (σ : S₁ ⇛ₛ S₂) → ★ ⋯ₛ σ ≡ ★
    
    `_⋯ᵣ_      : (x : s ∈ S₁) (ρ : S₁ ⇛ᵣ S₂) → (` x) ⋯ᵣ ρ ≡ ` ρ s x 
    λx_⋯ᵣ_     : (e : (expr ∷ S₁) ⊢ expr) (ρ : S₁ ⇛ᵣ S₂) → (λx e) ⋯ᵣ ρ ≡ (λx (e ⋯ᵣ (here refl ∷ᵣ (ρ ≫ᵣᵣ wkᵣ))))
    Λα_⋯ᵣ_     : (e : (type ∷ S₁) ⊢ expr) (ρ : S₁ ⇛ᵣ S₂) → (Λα e) ⋯ᵣ ρ ≡ (Λα (e ⋯ᵣ (here refl ∷ᵣ (ρ ≫ᵣᵣ wkᵣ))))
    ∀[α∶_]_⋯ᵣ_ : (k : S₁ ⊢ kind) (t : (type ∷ S₁) ⊢ type) (ρ : S₁ ⇛ᵣ S₂) → (∀[α∶ k ] t) ⋯ᵣ ρ ≡ ∀[α∶ k ⋯ᵣ ρ ] (t ⋯ᵣ (here refl ∷ᵣ (ρ ≫ᵣᵣ wkᵣ)))
    _·_⋯ᵣ_     : (e₁ : S₁ ⊢ expr) (e₂ : S₁ ⊢ expr) (ρ : S₁ ⇛ᵣ S₂) → (e₁ · e₂) ⋯ᵣ ρ ≡ (e₁ ⋯ᵣ ρ) · (e₂ ⋯ᵣ ρ)
    _∙_⋯ᵣ_     : (e : S₁ ⊢ expr) (t : S₁ ⊢ type) (ρ : S₁ ⇛ᵣ S₂) → (e ∙ t) ⋯ᵣ ρ ≡ (e ⋯ᵣ ρ) ∙ (t ⋯ᵣ ρ)
    _⇒_⋯ᵣ_     : (t₁ : S₁ ⊢ type) (t₂ : S₁ ⊢ type) (ρ : S₁ ⇛ᵣ S₂) → (t₁ ⇒ t₂) ⋯ᵣ ρ ≡ (t₁ ⋯ᵣ ρ) ⇒ (t₂ ⋯ᵣ ρ)
    ★⋯ᵣ_       : (ρ : S₁ ⇛ᵣ S₂) → ★ ⋯ᵣ ρ ≡ ★
    
    -- Definitions 
    ∷ᵣ-here  : (ρ : S₁ ⇛ᵣ S₂) (x : s ∈ S₂) → (x ∷ᵣ ρ) s (here refl) ≡ x 
    ∷ᵣ-there : (ρ : S₁ ⇛ᵣ S₂) (x : s ∈ S₂) (x' : s' ∈ S₁) → (x ∷ᵣ ρ) s' (there x') ≡ ρ s' x' 
    ∷ₛ-here  : (σ : S₁ ⇛ₛ S₂) (T : S₂ ⊢ s) → (T ∷ₛ σ) s (here refl) ≡ T 
    ∷ₛ-there : (σ : S₁ ⇛ₛ S₂) (T : S₂ ⊢ s) (x : s ∈ S₁) → (T ∷ₛ σ) s (there x) ≡ σ s x
    ≫ᵣᵣ-def  : (ρ₁ : S₁ ⇛ᵣ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) (s : Sort) (x : s ∈ S₁) → (ρ₁ ≫ᵣᵣ ρ₂) s x ≡ ρ₂ s (ρ₁ s x)
    wkᵣ-def  : (s : Sort) (x : s ∈ S₁) (s' : Sort) → wkᵣ {s = s'} s x ≡ there x
    ≫ᵣₛ-def  : (ρ₁ : S₁ ⇛ᵣ S₂) (σ₂ : S₂ ⇛ₛ S₃) (s : Sort) (x : s ∈ S₁) → (ρ₁ ≫ᵣₛ σ₂) s x ≡ σ₂ s (ρ₁ s x)
    ≫ₛᵣ-def  : (σ₁ : S₁ ⇛ₛ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) (s : Sort) (x : s ∈ S₁) → (σ₁ ≫ₛᵣ ρ₂) s x ≡ (σ₁ s x) ⋯ᵣ ρ₂
    ≫ₛₛ-def  : (σ₁ : S₁ ⇛ₛ S₂) (σ₂ : S₂ ⇛ₛ S₃) (s : Sort) (x : s ∈ S₁) → (σ₁ ≫ₛₛ σ₂) s x ≡ (σ₁ s x) ⋯ₛ σ₂

-- TODO: add shorthands back to equational theory using refl rewrite rules
_↑ᵣ_ : S₁ ⇛ᵣ S₂ → (s : Sort) → (s ∷ S₁) ⇛ᵣ (s ∷ S₂)
ρ ↑ᵣ _ = here refl ∷ᵣ (ρ ≫ᵣᵣ wkᵣ)

wk : S ⊢ s → (s' ∷ S) ⊢ s
wk T = T ⋯ᵣ wkᵣ

_↑ₛ_ : S₁ ⇛ₛ S₂ → (s : Sort) → (s ∷ S₁) ⇛ₛ (s ∷ S₂)
(σ ↑ₛ _) = (` (here refl)) ∷ₛ (σ ≫ₛᵣ wkᵣ)

_[_] : (s' ∷ S) ⊢ s → S ⊢ s' → S ⊢ s
T [ T' ] = T ⋯ₛ (T' ∷ₛ idₛ) 

-- Interaction Laws
{-# REWRITE left-idᵣᵣ right-idᵣᵣ left-idᵣₛ idᵣₛidₛᵣ right-idₛᵣ left-idₛₛ right-idₛₛ
            assocᵣᵣᵣ assocᵣᵣₛ assocᵣₛᵣ assocᵣₛₛ assocₛᵣᵣ assocₛᵣₛ assocₛₛᵣ assocₛₛₛ 
            distributivityᵣᵣ distributivityᵣₛ distributivityₛᵣ distributivityₛₛ 
            interactᵣ interactₛ η-id η-law #-}
            
-- Supplementary Laws
{-# REWRITE fusionᵣᵣ fusionₛᵣ fusionᵣₛ fusionₛₛ  ⋯idᵣ ⋯idₛ 
            coincidence #-}

-- Syntactic Laws
{-# REWRITE `_⋯ₛ_ λx_⋯ₛ_ Λα_⋯ₛ_ ∀[α∶_]_⋯ₛ_ _·_⋯ₛ_ _∙_⋯ₛ_ _⇒_⋯ₛ_ ★⋯ₛ_ 
            `_⋯ᵣ_ λx_⋯ᵣ_ Λα_⋯ᵣ_ ∀[α∶_]_⋯ᵣ_ _·_⋯ᵣ_ _∙_⋯ᵣ_ _⇒_⋯ᵣ_ ★⋯ᵣ_ #-}
          
-- Definitions
{-# REWRITE ≫ᵣᵣ-def wkᵣ-def ≫ᵣₛ-def ≫ₛᵣ-def ≫ₛᵣ-def ∷ᵣ-here ∷ᵣ-there ∷ₛ-here ∷ₛ-there #-}

variable
  ρ ρ₁ ρ₂ ρ₃ ρ₄ ρ' ρ₁' ρ₂' ρ₃' ρ₄' : S₁ ⇛ᵣ S₂
  σ σ₁ σ₂ σ₃ σ₄ σ' σ₁' σ₂' σ₃' σ₄' : S₁ ⇛ₛ S₂

-- Typing ----------------------------------------------------------------------

⤊_ : Sort → Sort
⤊ expr = type
⤊ type = kind
⤊ kind = kind

_∶⊢_ : List Sort → Sort → Set
S ∶⊢ s = S ⊢ (⤊ s)

depth : ∀ {ℓ} {A : Set ℓ} {x : A} {xs : List A} → x ∈ xs → ℕ
depth (here refl) = zero
depth (there x)   = suc (depth x)

drop-∈ :  ∀ {ℓ} {A : Set ℓ} {x : A} {xs : List A} →
          x ∈ xs → List A → List A
drop-∈ e xs = drop (suc (depth e)) xs

Ctx : List Sort → Set
Ctx S = ∀ s → (x : s ∈ S) → drop-∈ x S ∶⊢ s

∅ : Ctx []
∅ _ ()

_،_ : Ctx S → S ∶⊢ s → Ctx (s ∷ S)
(Γ ، t) _ (here refl) = t
(Γ ، t) _ (there x)   = Γ _ x

wk-drop-∈ : (x : s ∈ S) → drop-∈ x S ⊢ s' → S ⊢ s'
wk-drop-∈ (here refl) t = wk t 
wk-drop-∈ (there x)   t = wk (wk-drop-∈ x t) 

wk-telescope : Ctx S → s ∈ S → S ∶⊢ s
wk-telescope Γ x = wk-drop-∈ x (Γ _ x)

_∶_∈_ : s ∈ S → S ∶⊢ s → Ctx S → Set
x ∶ t ∈ Γ = wk-telescope Γ x ≡ t

variable 
  Γ Γ₁ Γ₂ Γ₃ Γ' Γ₁' Γ₂' Γ₃' : Ctx S

data _⊢_∶_ : Ctx S → S ⊢ s → S ∶⊢ s → Set where
  ⊢` : ∀ {T : S ∶⊢ s} → 
    x ∶ T ∈ Γ →
    -------------
    Γ ⊢ (` x) ∶ T
  ⊢λ : 
    (Γ ، t) ⊢ e ∶ (wk t') → 
    ------------------------
    Γ ⊢ (λx e) ∶ (t ⇒ t')
  ⊢Λ :
    (Γ ، k) ⊢ e ∶ t →  
    -------------------------
    Γ ⊢ (Λα e) ∶ (∀[α∶ k ] t)
  ⊢· : 
    Γ ⊢ e₁ ∶ (t₁ ⇒ t₂) →
    Γ ⊢ e₂ ∶ t₁ →
    --------------------
    Γ ⊢ (e₁ · e₂) ∶ t₂
  ⊢∙ : 
    Γ ⊢ e ∶ (∀[α∶ k ] t') →
    Γ ⊢ t ∶ k →
    (Γ ، k) ⊢ t' ∶ k' →
    ------------------------
    Γ ⊢ (e ∙ t) ∶ (t' [ t ])
  ⊢★ : 
    ---------
    Γ ⊢ t ∶ ★

_∶_⇛ᵣ_ : S₁ ⇛ᵣ S₂ → Ctx S₁ → Ctx S₂ → Set
_∶_⇛ᵣ_ {S₁} {S₂} ρ Γ₁ Γ₂ = ∀ (s : Sort) (x : s ∈ S₁) (T : S₁ ∶⊢ s) → x ∶ T ∈ Γ₁ → (ρ _ x) ∶ T ⋯ᵣ ρ ∈ Γ₂ 

⊢wk : ∀ (Γ : Ctx S) (x : s ∈ S) (T : S ∶⊢ s) (T' : S ∶⊢ s') → x ∶ T ∈ Γ → (there x) ∶ (wk T) ∈ (Γ ، T')
⊢wk _ _ _ _ refl = refl

⊢↑ᵣ : ρ ∶ Γ₁ ⇛ᵣ Γ₂ → (T : S₁ ∶⊢ s) → (ρ ↑ᵣ s) ∶ Γ₁ ، T ⇛ᵣ (Γ₂ ، (T ⋯ᵣ ρ))
⊢↑ᵣ ⊢ρ T _ (here refl) _ refl = refl
⊢↑ᵣ {ρ = ρ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ⊢ρ T _ (there x)   _ refl =
   ⊢wk Γ₂ (ρ _ x) (wk-drop-∈ x (Γ₁ _ x) ⋯ᵣ ρ) (T ⋯ᵣ ρ) (⊢ρ _ x (wk-drop-∈ x (Γ₁ _ x)) refl)

_∶_⇛ₛ_ : S₁ ⇛ₛ S₂ → Ctx S₁ → Ctx S₂ → Set
_∶_⇛ₛ_ {S₁} {S₂} σ Γ₁ Γ₂ = ∀ (s : Sort) (x : s ∈ S₁) (T : S₁ ∶⊢ s) → x ∶ T ∈ Γ₁ → Γ₂ ⊢ (σ _ x) ∶ (T ⋯ₛ σ)

⊢↑ₛ : ∀ {T : S ∶⊢ s} → σ ∶ Γ₁ ⇛ₛ Γ₂ → (σ ↑ₛ s) ∶ Γ₁ ، T ⇛ₛ (Γ₂ ، (T ⋯ₛ σ))
⊢↑ₛ ⊢σ _ (here refl) _ refl = {!   !}
⊢↑ₛ ⊢σ _ (there x) _ refl   = {!  ⊢σ    !}

-- Semantics -------------------------------------------------------------------

data Val : S ⊢ expr → Set where
  vλ : Val (λx e)
  vΛ : Val (Λα e)

data _↪_ : S ⊢ expr → S ⊢ expr → Set where
  β-λ :
    Val e₂ →
    ----------------------------
    ((λx e₁) · e₂) ↪ (e₁ [ e₂ ])
  β-Λ :
    ------------------------
    ((Λα e) ∙ t) ↪ (e [ t ])
  ξ-·₁ :
    e₁ ↪ e →
    --------------------
    (e₁ · e₂) ↪ (e · e₂)
  ξ-·₂ :
    e₂ ↪ e →
    Val e₁ →
    --------------------
    (e₁ · e₂) ↪ (e₁ · e)
  ξ-∙ :
    e ↪ e' →
    ------------------
    (e ∙ t) ↪ (e' ∙ t)

-- Soundness -------------------------------------------------------------------

progress : 
  ∅ ⊢ e ∶ t →
  (∃[ e' ] (e ↪ e')) ⊎ Val e
progress (⊢λ _) = inj₂ vλ
progress (⊢Λ _) = inj₂ vΛ
progress (⊢· {e₁ = e₁} {e₂ = e₂} ⊢e₁  ⊢e₂) with progress ⊢e₁ | progress ⊢e₂ 
... | inj₁ (e₁' , e₁↪e₁') | _                   = inj₁ (e₁' · e₂ , ξ-·₁ e₁↪e₁')
... | inj₂ v              | inj₁ (e₂' , e₂↪e₂') = inj₁ (e₁ · e₂' , ξ-·₂ e₂↪e₂' v)
... | inj₂ (vλ {e = e₁})  | inj₂ v              = inj₁ (e₁ [ e₂ ] , β-λ v)
progress (⊢∙ {t = t} ⊢e _ _) with progress ⊢e 
... | inj₁ (e' , e↪e')  = inj₁ (e' ∙ t , ξ-∙ e↪e')
... | inj₂ (vΛ {e = e}) = inj₁ (e [ t ] , β-Λ)

⊢ρ-preserves : ∀ {t : S₁ ⊢ s} {T : S₁ ⊢ (⤊ s)} →
  ρ ∶ Γ₁ ⇛ᵣ Γ₂ →
  Γ₁ ⊢ t ∶ T →
  Γ₂ ⊢ (t ⋯ᵣ ρ) ∶ (T ⋯ᵣ ρ)
⊢ρ-preserves ⊢ρ (⊢` ⊢x)        = ⊢` (⊢ρ _ _ _ ⊢x) 
⊢ρ-preserves ⊢ρ (⊢λ ⊢e)        = ⊢λ (⊢ρ-preserves (⊢↑ᵣ ⊢ρ _) ⊢e)
⊢ρ-preserves ⊢ρ (⊢Λ ⊢e)        = ⊢Λ ((⊢ρ-preserves (⊢↑ᵣ ⊢ρ _) ⊢e))
⊢ρ-preserves ⊢ρ (⊢· ⊢e₁ ⊢e₂)   = ⊢· (⊢ρ-preserves ⊢ρ ⊢e₁) (⊢ρ-preserves ⊢ρ ⊢e₂)
⊢ρ-preserves ⊢ρ (⊢∙ ⊢e ⊢t ⊢t') = {!   !} -- ⊢∙ (⊢ρ-preserves ⊢ρ ⊢e) (⊢ρ-preserves ⊢ρ ⊢t) (⊢ρ-preserves (⊢↑ᵣ ⊢ρ _) ⊢t') 
⊢ρ-preserves ⊢ρ ⊢★             = ⊢★


⊢σ-preserves : ∀ {t : S₁ ⊢ s} {T : S₁ ⊢ (⤊ s)} →
  σ ∶ Γ₁ ⇛ₛ Γ₂ →
  Γ₁ ⊢ t ∶ T →
  Γ₂ ⊢ (t ⋯ₛ σ) ∶ (T ⋯ₛ σ)
⊢σ-preserves ⊢σ (⊢` ⊢x)        = ⊢σ _ _ _ ⊢x
⊢σ-preserves ⊢σ (⊢λ ⊢e)        = {!   !} -- ⊢λ (⊢σ-preserves (⊢↑ₛ ⊢σ) ⊢e)
⊢σ-preserves ⊢σ (⊢Λ ⊢e)        = ⊢Λ (⊢σ-preserves (⊢↑ₛ ⊢σ) ⊢e)
⊢σ-preserves ⊢σ (⊢· ⊢e₁ ⊢e₂)   = ⊢· (⊢σ-preserves ⊢σ ⊢e₁) (⊢σ-preserves ⊢σ ⊢e₂)
⊢σ-preserves ⊢σ (⊢∙ ⊢e ⊢t ⊢t') = {!   !} -- ⊢∙ (⊢σ-preserves ⊢σ ⊢e) (⊢σ-preserves ⊢σ ⊢t) (⊢σ-preserves (⊢↑ₛ ⊢σ) ⊢t')
⊢σ-preserves ⊢σ ⊢★             = ⊢★

-- 
-- subject-reduction : 
--   Γ ⊢ e ∶ t → 
--   e ↪ e' → 
--   Γ ⊢ e' ∶ t 
-- subject-reduction (⊢· (⊢λ ⊢e₁) ⊢e₂)             (β-λ v₂)      = ⊢σ-preserves (⊢[] ⊢e₂) ⊢e₁
-- subject-reduction (⊢· ⊢e₁ ⊢e₂)                  (ξ-·₁ e₁↪e)   = ⊢· (subject-reduction ⊢e₁ e₁↪e) ⊢e₂
-- subject-reduction (⊢· ⊢e₁ ⊢e₂)                  (ξ-·₂ e₂↪e x) = ⊢· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e)       
-- subject-reduction (⊢∙ {t' = t'} ⊢t ⊢t' (⊢Λ ⊢e)) β-Λ           = ⊢σ-preserves (⊢[] ⊢t) ⊢e     
-- subject-reduction (⊢∙ ⊢t ⊢t' ⊢e)                (ξ-∙ e↪e')    = ⊢∙ ⊢t ⊢t' (subject-reduction ⊢e e↪e')                        