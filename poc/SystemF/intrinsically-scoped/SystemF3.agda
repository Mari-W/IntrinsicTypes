{-# OPTIONS --rewriting #-}
module SystemF3 where

-- Imports ---------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; ∃-syntax)
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional public using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; trans; sym; module ≡-Reasoning)
open ≡-Reasoning
open import Function using (id)

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
abstract 
  (ρ₁ ≫ᵣᵣ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)
  ≫ᵣᵣ-def : (ρ₁ : S₁ ⇛ᵣ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) (x : s ∈ S₁) → (ρ₁ ≫ᵣᵣ ρ₂) s x ≡ ρ₂ s (ρ₁ s x)
  ≫ᵣᵣ-def _ _ _ = refl

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
abstract
  (ρ₁ ≫ᵣₛ σ₂) _ x = σ₂ _ (ρ₁ _ x)
  ≫ᵣₛ-def : (ρ₁ : S₁ ⇛ᵣ S₂) (σ₂ : S₂ ⇛ₛ S₃) (x : s ∈ S₁) → (ρ₁ ≫ᵣₛ σ₂) s x ≡ σ₂ s (ρ₁ s x)
  ≫ᵣₛ-def _ _ _ = refl 
  
_≫ₛᵣ_ : S₁ ⇛ₛ S₂ → S₂ ⇛ᵣ S₃ → S₁ ⇛ₛ S₃
abstract
  (σ₁ ≫ₛᵣ ρ₂) _ x = (σ₁ _ x) ⋯ᵣ ρ₂
  ≫ₛᵣ-def : (σ₁ : S₁ ⇛ₛ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) (x : s ∈ S₁) → (σ₁ ≫ₛᵣ ρ₂) s x ≡ (σ₁ s x) ⋯ᵣ ρ₂
  ≫ₛᵣ-def _ _ _ = refl

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
abstract 
  (σ₁ ≫ₛₛ σ₂) _ x = (σ₁ _ x) ⋯ₛ σ₂
  ≫ₛₛ-def : (σ₁ : S₁ ⇛ₛ S₂) (σ₂ : S₂ ⇛ₛ S₃) (x : s ∈ S₁) → (σ₁ ≫ₛₛ σ₂) s x ≡ (σ₁ s x) ⋯ₛ σ₂
  ≫ₛₛ-def _ _ _ = refl
  
_[_] : (s' ∷ S) ⊢ s → S ⊢ s' → S ⊢ s
T [ T' ] = T ⋯ₛ (T' ∷ₛ idₛ) 

η-id : _∷ᵣ_ {s = s} {S₁ = S₁} (here refl) wkᵣ ≡ idᵣ 
η-id = fun-ext (λ _ → fun-ext λ { (here refl) → refl ; (there x) → refl })

η-law : (σ : (s ∷ S₁) ⇛ₛ S₂) → (σ _ (here refl)) ∷ₛ (wkᵣ ≫ᵣₛ σ) ≡ σ
η-law σ = fun-ext λ _ → fun-ext λ { (here refl) → refl ; (there x) → ≫ᵣₛ-def wkᵣ σ x }

{-# REWRITE η-id η-law #-}

{-# REWRITE ≫ᵣᵣ-def ≫ᵣₛ-def ≫ₛᵣ-def ≫ₛₛ-def #-}

η-law' : (σ : (s ∷ S₁) ⇛ₛ S₂) → (σ _ (here refl)) ∷ₛ (wkᵣ ≫ᵣₛ σ) ≡ σ
η-law' σ = fun-ext λ _ → fun-ext λ { (here refl) → refl ; (there x) → refl }


⋯idᵣ : (T : S ⊢ s) → T ⋯ᵣ idᵣ ≡ T 
⋯idᵣ (` x)        = refl
⋯idᵣ (λx e)       = cong λx_ (⋯idᵣ e)
⋯idᵣ (Λα e)       = cong Λα_ (⋯idᵣ e)
⋯idᵣ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (⋯idᵣ k) (⋯idᵣ t)
⋯idᵣ (e₁ · e₂)    = cong₂ _·_ (⋯idᵣ e₁) (⋯idᵣ e₂)
⋯idᵣ (e ∙ t)      = cong₂ _∙_ (⋯idᵣ e) (⋯idᵣ t)
⋯idᵣ (t₁ ⇒ t₂)    = cong₂ _⇒_ (⋯idᵣ t₁) (⋯idᵣ t₂)
⋯idᵣ ★            = refl

↑idₛ : _∷ₛ_ {s = s} {S₁ = S} (` here refl) (idₛ ≫ₛᵣ wkᵣ) ≡ idₛ 
↑idₛ = fun-ext (λ _ → fun-ext λ { (here refl) → refl ; (there x) → refl })
{-# REWRITE ↑idₛ #-}

⋯idₛ : (T : S ⊢ s) → T ⋯ₛ idₛ ≡ T 
⋯idₛ (` x)        = refl
⋯idₛ (λx e)       = cong λx_ (subst (λ σ → (e ⋯ₛ σ) ≡ e) (sym ↑idₛ) (⋯idₛ e))
⋯idₛ (Λα e)       = cong Λα_ (subst (λ σ → (e ⋯ₛ σ) ≡ e) (sym ↑idₛ) (⋯idₛ e))
⋯idₛ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (⋯idₛ k) (⋯idₛ t)
⋯idₛ (e₁ · e₂)    = cong₂ _·_ (⋯idₛ e₁) (⋯idₛ e₂)
⋯idₛ (e ∙ t)      = cong₂ _∙_ (⋯idₛ e) (⋯idₛ t)
⋯idₛ (t₁ ⇒ t₂)    = cong₂ _⇒_ (⋯idₛ t₁) (⋯idₛ t₂)
⋯idₛ ★            = refl

{-# REWRITE ⋯idᵣ ⋯idₛ #-}

distributivityᵣᵣ : (x : s ∈ S₂) (ρ₁ : S₁ ⇛ᵣ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) → (x ∷ᵣ ρ₁) ≫ᵣᵣ ρ₂ ≡ ρ₂ _ x ∷ᵣ (ρ₁ ≫ᵣᵣ ρ₂)  
distributivityᵣᵣ _ _ _ = fun-ext (λ _ → fun-ext λ { (here refl) → refl ; (there x) → refl })

distributivityᵣₛ : (x : s ∈ S₂) (ρ₁ : S₁ ⇛ᵣ S₂) (σ₂ : S₂ ⇛ₛ S₃) → (x ∷ᵣ ρ₁) ≫ᵣₛ σ₂ ≡ σ₂ _ x ∷ₛ (ρ₁ ≫ᵣₛ σ₂)
distributivityᵣₛ _ _ _ = fun-ext (λ _ → fun-ext λ { (here refl) → refl ; (there x) → refl })

distributivityₛᵣ : (T : S₂ ⊢ s) (σ₁ : S₁ ⇛ₛ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) → (T ∷ₛ σ₁) ≫ₛᵣ ρ₂ ≡ (T ⋯ᵣ ρ₂) ∷ₛ (σ₁ ≫ₛᵣ ρ₂)
distributivityₛᵣ _ _ _ = fun-ext (λ _ → fun-ext λ { (here refl) → refl ; (there x) → refl })

distributivityₛₛ : (T : S₂ ⊢ s) (σ₁ : S₁ ⇛ₛ S₂) (σ₂ : S₂ ⇛ₛ S₃) → (T ∷ₛ σ₁) ≫ₛₛ σ₂ ≡ (T ⋯ₛ σ₂) ∷ₛ (σ₁ ≫ₛₛ σ₂)
distributivityₛₛ _ _ _ = fun-ext (λ _ → fun-ext λ { (here refl) → refl ; (there x) → refl })

{-# REWRITE distributivityᵣᵣ distributivityᵣₛ distributivityₛᵣ distributivityₛₛ #-}

fusionᵣᵣ : (ρ₁ : S₁ ⇛ᵣ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) (T : S₁ ⊢ s) → (T ⋯ᵣ ρ₁) ⋯ᵣ ρ₂ ≡ T ⋯ᵣ (ρ₁ ≫ᵣᵣ ρ₂)
fusionᵣᵣ ρ₁ ρ₂ (` x)        = refl
fusionᵣᵣ ρ₁ ρ₂ (λx e)       = cong λx_ (fusionᵣᵣ (ρ₁ ↑ᵣ expr) (ρ₂ ↑ᵣ expr) e)
fusionᵣᵣ ρ₁ ρ₂ (Λα e)       = cong Λα_ (fusionᵣᵣ (ρ₁ ↑ᵣ type) (ρ₂ ↑ᵣ type) e)
fusionᵣᵣ ρ₁ ρ₂ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (fusionᵣᵣ ρ₁ ρ₂ k) (fusionᵣᵣ (ρ₁ ↑ᵣ type) (ρ₂ ↑ᵣ type) t)
fusionᵣᵣ ρ₁ ρ₂ (e₁ · e₂)    = cong₂ _·_ (fusionᵣᵣ ρ₁ ρ₂ e₁) (fusionᵣᵣ ρ₁ ρ₂ e₂)
fusionᵣᵣ ρ₁ ρ₂ (e ∙ t)      = cong₂ _∙_ (fusionᵣᵣ ρ₁ ρ₂ e) (fusionᵣᵣ ρ₁ ρ₂ t)
fusionᵣᵣ ρ₁ ρ₂ (t₁ ⇒ t₂)    = cong₂ _⇒_ (fusionᵣᵣ ρ₁ ρ₂ t₁) (fusionᵣᵣ ρ₁ ρ₂ t₂)
fusionᵣᵣ ρ₁ ρ₂ ★            = refl

{-# REWRITE fusionᵣᵣ #-}

fusionᵣₛ : (ρ₁ : S₁ ⇛ᵣ S₂) (σ₂ : S₂ ⇛ₛ S₃)  (T : S₁ ⊢ s) → (T ⋯ᵣ ρ₁) ⋯ₛ σ₂ ≡ T ⋯ₛ (ρ₁ ≫ᵣₛ σ₂)
fusionᵣₛ ρ₁ σ₂ (` x)        = refl
fusionᵣₛ ρ₁ σ₂ (λx e)       = cong λx_ (fusionᵣₛ (ρ₁ ↑ᵣ expr) (σ₂ ↑ₛ expr) e)
fusionᵣₛ ρ₁ σ₂ (Λα e)       = cong Λα_ (fusionᵣₛ (ρ₁ ↑ᵣ type) (σ₂ ↑ₛ type) e)
fusionᵣₛ ρ₁ σ₂ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (fusionᵣₛ ρ₁ σ₂ k) (fusionᵣₛ (ρ₁ ↑ᵣ type) (σ₂ ↑ₛ type) t)
fusionᵣₛ ρ₁ σ₂ (e₁ · e₂)    = cong₂ _·_ (fusionᵣₛ ρ₁ σ₂ e₁) (fusionᵣₛ ρ₁ σ₂ e₂)
fusionᵣₛ ρ₁ σ₂ (e ∙ t)      = cong₂ _∙_ (fusionᵣₛ ρ₁ σ₂ e) (fusionᵣₛ ρ₁ σ₂ t)
fusionᵣₛ ρ₁ σ₂ (t₁ ⇒ t₂)    = cong₂ _⇒_ (fusionᵣₛ ρ₁ σ₂ t₁) (fusionᵣₛ ρ₁ σ₂ t₂)
fusionᵣₛ ρ₁ σ₂ ★            = refl

{-# REWRITE fusionᵣₛ #-}

fusionₛᵣ : (σ₁ : S₁ ⇛ₛ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) (T : S₁ ⊢ s) → (T ⋯ₛ σ₁) ⋯ᵣ ρ₂ ≡ T ⋯ₛ (σ₁ ≫ₛᵣ ρ₂)
fusionₛᵣ σ₁ ρ₂ (` x)        = refl
fusionₛᵣ σ₁ ρ₂ (λx e)       = cong λx_ (fusionₛᵣ (σ₁ ↑ₛ expr) (ρ₂ ↑ᵣ expr) e)
fusionₛᵣ σ₁ ρ₂ (Λα e)       = cong Λα_ (fusionₛᵣ (σ₁ ↑ₛ type) (ρ₂ ↑ᵣ type) e)
fusionₛᵣ σ₁ ρ₂ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (fusionₛᵣ σ₁ ρ₂ k) ((fusionₛᵣ (σ₁ ↑ₛ type) (ρ₂ ↑ᵣ type) t))
fusionₛᵣ σ₁ ρ₂ (e₁ · e₂)    = cong₂ _·_ (fusionₛᵣ σ₁ ρ₂ e₁) (fusionₛᵣ σ₁ ρ₂ e₂)
fusionₛᵣ σ₁ ρ₂ (e ∙ t)      = cong₂ _∙_ (fusionₛᵣ σ₁ ρ₂ e) (fusionₛᵣ σ₁ ρ₂ t)
fusionₛᵣ σ₁ ρ₂ (t₁ ⇒ t₂)    = cong₂ _⇒_ (fusionₛᵣ σ₁ ρ₂ t₁) (fusionₛᵣ σ₁ ρ₂ t₂)
fusionₛᵣ σ₁ ρ₂ ★            = refl

{-# REWRITE fusionₛᵣ #-}

fusionₛₛ : (σ₁ : S₁ ⇛ₛ S₂) (σ₂ : S₂ ⇛ₛ S₃) (T : S₁ ⊢ s) → (T ⋯ₛ σ₁) ⋯ₛ σ₂ ≡ T ⋯ₛ (σ₁ ≫ₛₛ σ₂)
fusionₛₛ σ₁ σ₂ (` x)        = refl
fusionₛₛ σ₁ σ₂ (λx e)       = cong λx_ (fusionₛₛ (σ₁ ↑ₛ expr) (σ₂ ↑ₛ expr) e)
fusionₛₛ σ₁ σ₂ (Λα e)       = cong Λα_ (fusionₛₛ (σ₁ ↑ₛ type) (σ₂ ↑ₛ type) e)
fusionₛₛ σ₁ σ₂ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (fusionₛₛ σ₁ σ₂ k) (fusionₛₛ (σ₁ ↑ₛ type) (σ₂ ↑ₛ type) t)
fusionₛₛ σ₁ σ₂ (e₁ · e₂)    = cong₂ _·_ (fusionₛₛ σ₁ σ₂ e₁) (fusionₛₛ σ₁ σ₂ e₂)
fusionₛₛ σ₁ σ₂ (e ∙ t)      = cong₂ _∙_ (fusionₛₛ σ₁ σ₂ e) (fusionₛₛ σ₁ σ₂ t)
fusionₛₛ σ₁ σ₂ (t₁ ⇒ t₂)    = cong₂ _⇒_ (fusionₛₛ σ₁ σ₂ t₁) (fusionₛₛ σ₁ σ₂ t₂)
fusionₛₛ σ₁ σ₂ ★            = refl

{-# REWRITE fusionₛₛ #-}

↑coincidence : (ρ : S₁ ⇛ᵣ S₂) (s : Sort) → ((ρ ↑ᵣ s) ≫ᵣₛ idₛ) ≡ (ρ ≫ᵣₛ idₛ) ↑ₛ s
↑coincidence _ _ = fun-ext (λ _ → fun-ext λ { (here refl) → refl ; (there x) → refl })

coincidence : (ρ : S₁ ⇛ᵣ S₂) (T : S₁ ⊢ s) → T ⋯ₛ (ρ ≫ᵣₛ idₛ) ≡ T ⋯ᵣ ρ
coincidence ρ (` x)        = refl
coincidence ρ (λx e)       = cong λx_ (subst (λ σ → e ⋯ₛ σ ≡ (e ⋯ᵣ (ρ ↑ᵣ expr))) (↑coincidence _ _) (coincidence (ρ ↑ᵣ expr) e))
coincidence ρ (Λα e)       = cong Λα_ (subst (λ σ → e ⋯ₛ σ ≡ (e ⋯ᵣ (ρ ↑ᵣ type))) (↑coincidence _ _) (coincidence (ρ ↑ᵣ type) e))
coincidence ρ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (coincidence ρ k) (subst (λ σ → t ⋯ₛ σ ≡ (t ⋯ᵣ (ρ ↑ᵣ type))) (↑coincidence _ _) (coincidence (ρ ↑ᵣ type) t))
coincidence ρ (e₁ · e₂)    = cong₂ _·_ (coincidence ρ e₁) (coincidence ρ e₂)
coincidence ρ (e ∙ t)      = cong₂ _∙_ (coincidence ρ e) (coincidence ρ t)
coincidence ρ (t₁ ⇒ t₂)    = cong₂ _⇒_ (coincidence ρ t₁) (coincidence ρ t₂)
coincidence ρ ★            = refl

{-# REWRITE coincidence #-}

bar : ∀ {ρ : S₁ ⇛ᵣ S₂} → t ⋯ₛ (ρ ≫ᵣₛ idₛ) ≡ t ⋯ᵣ ρ
bar {t = t} {ρ = ρ} = {! ρ ≫ᵣₛ idₛ  !}

foo : (σ : S₁ ⇛ₛ S₂) → σ ≫ₛᵣ idᵣ ≡ σ
foo _ = refl

abc : ∀ {ρ : S₁ ⇛ᵣ S₂} → (t ⋯ₛ ((ρ ≫ᵣₛ idₛ {S = S₂}) ↑ₛ s)) ≡ (t ⋯ᵣ (ρ ↑ᵣ s))
abc {S₂ = S₂} {s = s} {t = t} {ρ = ρ} = begin 
    t ⋯ₛ ((ρ ≫ᵣₛ idₛ {S = S₂}) ↑ₛ s)
  ≡⟨ refl ⟩
    t ⋯ₛ ((` here refl) ∷ₛ (λ z x → ` there (ρ z x)))
  ≡⟨ cong (t ⋯ₛ_) (η-law ((ρ ≫ᵣₛ idₛ {S = S₂}) ↑ₛ s)) ⟩
    (t ⋯ₛ ((` here refl) ∷ₛ ((ρ ≫ᵣₛ idₛ) ≫ₛᵣ (λ s → there))))
  ≡⟨ refl ⟩
    t ⋯ₛ ((` here refl) ∷ₛ (λ z x → ` there (ρ z x)))
  ≡⟨ {!   !} ⟩
    t ⋯ᵣ (here refl ∷ᵣ (λ z x → there (ρ z x)))
  ≡⟨ refl ⟩
    (t ⋯ᵣ (ρ ↑ᵣ s))
  ∎
  