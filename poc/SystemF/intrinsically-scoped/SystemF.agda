{-# OPTIONS --rewriting #-}
module SystemF where

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

{-# REWRITE ≫ᵣᵣ-def ≫ᵣₛ-def ≫ₛᵣ-def ≫ₛₛ-def #-}

η-id : _∷ᵣ_ {s = s} {S₁ = S₁} (here refl) wkᵣ ≡ idᵣ 
η-id = fun-ext (λ _ → fun-ext λ { (here refl) → refl ; (there x) → refl })

η-law : (σ : (s ∷ S₁) ⇛ₛ S₂) → _∷ₛ_ {s = s} {S₁ = S₁} (σ _ ( (here refl))) (wkᵣ ≫ᵣₛ σ) ≡ σ
η-law = ?

{-# REWRITE η-id η-law #-}

⋯idᵣ : (T : S ⊢ s) → T ⋯ᵣ idᵣ ≡ T 
⋯idᵣ (` x)        = refl
⋯idᵣ (λx e)       = cong λx_ (⋯idᵣ e)
⋯idᵣ (Λα e)       = cong Λα_ (⋯idᵣ e)
⋯idᵣ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (⋯idᵣ k) (⋯idᵣ t)
⋯idᵣ (e₁ · e₂)    = cong₂ _·_ (⋯idᵣ e₁) (⋯idᵣ e₂)
⋯idᵣ (e ∙ t)      = cong₂ _∙_ (⋯idᵣ e) (⋯idᵣ t)
⋯idᵣ (t₁ ⇒ t₂)    = cong₂ _⇒_ (⋯idᵣ t₁) (⋯idᵣ t₂)
⋯idᵣ ★            = refl

⋯idₛ : (T : S ⊢ s) → T ⋯ₛ idₛ ≡ T 
⋯idₛ (` x)        = refl
⋯idₛ (λx e)       = cong λx_ (⋯idₛ e)
⋯idₛ (Λα e)       = cong Λα_ (⋯idₛ e)
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

compositionalityᵣᵣ : (ρ₁ : S₁ ⇛ᵣ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) (T : S₁ ⊢ s) → (T ⋯ᵣ ρ₁) ⋯ᵣ ρ₂ ≡ T ⋯ᵣ (ρ₁ ≫ᵣᵣ ρ₂)
compositionalityᵣᵣ ρ₁ ρ₂ (` x)        = refl
compositionalityᵣᵣ ρ₁ ρ₂ (λx e)       = cong λx_ (compositionalityᵣᵣ (ρ₁ ↑ᵣ expr) (ρ₂ ↑ᵣ expr) e)
compositionalityᵣᵣ ρ₁ ρ₂ (Λα e)       = cong Λα_ (compositionalityᵣᵣ (ρ₁ ↑ᵣ type) (ρ₂ ↑ᵣ type) e)
compositionalityᵣᵣ ρ₁ ρ₂ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityᵣᵣ ρ₁ ρ₂ k) (compositionalityᵣᵣ (ρ₁ ↑ᵣ type) (ρ₂ ↑ᵣ type) t)
compositionalityᵣᵣ ρ₁ ρ₂ (e₁ · e₂)    = cong₂ _·_ (compositionalityᵣᵣ ρ₁ ρ₂ e₁) (compositionalityᵣᵣ ρ₁ ρ₂ e₂)
compositionalityᵣᵣ ρ₁ ρ₂ (e ∙ t)      = cong₂ _∙_ (compositionalityᵣᵣ ρ₁ ρ₂ e) (compositionalityᵣᵣ ρ₁ ρ₂ t)
compositionalityᵣᵣ ρ₁ ρ₂ (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityᵣᵣ ρ₁ ρ₂ t₁) (compositionalityᵣᵣ ρ₁ ρ₂ t₂)
compositionalityᵣᵣ ρ₁ ρ₂ ★            = refl

{-# REWRITE compositionalityᵣᵣ #-}

compositionalityᵣₛ : (ρ₁ : S₁ ⇛ᵣ S₂) (σ₂ : S₂ ⇛ₛ S₃)  (T : S₁ ⊢ s) → (T ⋯ᵣ ρ₁) ⋯ₛ σ₂ ≡ T ⋯ₛ (ρ₁ ≫ᵣₛ σ₂)
compositionalityᵣₛ ρ₁ σ₂ (` x)        = refl
compositionalityᵣₛ ρ₁ σ₂ (λx e)       = cong λx_ (compositionalityᵣₛ (ρ₁ ↑ᵣ expr) (σ₂ ↑ₛ expr) e)
compositionalityᵣₛ ρ₁ σ₂ (Λα e)       = cong Λα_ (compositionalityᵣₛ (ρ₁ ↑ᵣ type) (σ₂ ↑ₛ type) e)
compositionalityᵣₛ ρ₁ σ₂ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityᵣₛ ρ₁ σ₂ k) (compositionalityᵣₛ (ρ₁ ↑ᵣ type) (σ₂ ↑ₛ type) t)
compositionalityᵣₛ ρ₁ σ₂ (e₁ · e₂)    = cong₂ _·_ (compositionalityᵣₛ ρ₁ σ₂ e₁) (compositionalityᵣₛ ρ₁ σ₂ e₂)
compositionalityᵣₛ ρ₁ σ₂ (e ∙ t)      = cong₂ _∙_ (compositionalityᵣₛ ρ₁ σ₂ e) (compositionalityᵣₛ ρ₁ σ₂ t)
compositionalityᵣₛ ρ₁ σ₂ (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityᵣₛ ρ₁ σ₂ t₁) (compositionalityᵣₛ ρ₁ σ₂ t₂)
compositionalityᵣₛ ρ₁ σ₂ ★            = refl

{-# REWRITE compositionalityᵣₛ #-}

compositionalityₛᵣ : (σ₁ : S₁ ⇛ₛ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) (T : S₁ ⊢ s) → (T ⋯ₛ σ₁) ⋯ᵣ ρ₂ ≡ T ⋯ₛ (σ₁ ≫ₛᵣ ρ₂)
compositionalityₛᵣ σ₁ ρ₂ (` x)        = refl
compositionalityₛᵣ σ₁ ρ₂ (λx e)       = cong λx_ (compositionalityₛᵣ (σ₁ ↑ₛ expr) (ρ₂ ↑ᵣ expr) e)
compositionalityₛᵣ σ₁ ρ₂ (Λα e)       = cong Λα_ (compositionalityₛᵣ (σ₁ ↑ₛ type) (ρ₂ ↑ᵣ type) e)
compositionalityₛᵣ σ₁ ρ₂ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityₛᵣ σ₁ ρ₂ k) ((compositionalityₛᵣ (σ₁ ↑ₛ type) (ρ₂ ↑ᵣ type) t))
compositionalityₛᵣ σ₁ ρ₂ (e₁ · e₂)    = cong₂ _·_ (compositionalityₛᵣ σ₁ ρ₂ e₁) (compositionalityₛᵣ σ₁ ρ₂ e₂)
compositionalityₛᵣ σ₁ ρ₂ (e ∙ t)      = cong₂ _∙_ (compositionalityₛᵣ σ₁ ρ₂ e) (compositionalityₛᵣ σ₁ ρ₂ t)
compositionalityₛᵣ σ₁ ρ₂ (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityₛᵣ σ₁ ρ₂ t₁) (compositionalityₛᵣ σ₁ ρ₂ t₂)
compositionalityₛᵣ σ₁ ρ₂ ★            = refl

{-# REWRITE compositionalityₛᵣ #-}

compositionalityₛₛ : (σ₁ : S₁ ⇛ₛ S₂) (σ₂ : S₂ ⇛ₛ S₃) (T : S₁ ⊢ s) → (T ⋯ₛ σ₁) ⋯ₛ σ₂ ≡ T ⋯ₛ (σ₁ ≫ₛₛ σ₂)
compositionalityₛₛ σ₁ σ₂ (` x)        = refl
compositionalityₛₛ σ₁ σ₂ (λx e)       = cong λx_ (compositionalityₛₛ (σ₁ ↑ₛ expr) (σ₂ ↑ₛ expr) e)
compositionalityₛₛ σ₁ σ₂ (Λα e)       = cong Λα_ (compositionalityₛₛ (σ₁ ↑ₛ type) (σ₂ ↑ₛ type) e)
compositionalityₛₛ σ₁ σ₂ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityₛₛ σ₁ σ₂ k) (compositionalityₛₛ (σ₁ ↑ₛ type) (σ₂ ↑ₛ type) t)
compositionalityₛₛ σ₁ σ₂ (e₁ · e₂)    = cong₂ _·_ (compositionalityₛₛ σ₁ σ₂ e₁) (compositionalityₛₛ σ₁ σ₂ e₂)
compositionalityₛₛ σ₁ σ₂ (e ∙ t)      = cong₂ _∙_ (compositionalityₛₛ σ₁ σ₂ e) (compositionalityₛₛ σ₁ σ₂ t)
compositionalityₛₛ σ₁ σ₂ (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityₛₛ σ₁ σ₂ t₁) (compositionalityₛₛ σ₁ σ₂ t₂)
compositionalityₛₛ σ₁ σ₂ ★            = refl

{-# REWRITE compositionalityₛₛ #-}

↑coincidence : (ρ : S₁ ⇛ᵣ S₂) (s : Sort) → (` here refl) ∷ₛ ((λ z s₁ → there (ρ z s₁)) ≫ᵣₛ (λ z → `_)) ≡ (ρ ≫ᵣₛ idₛ) ↑ₛ s
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

_∶_⇛ₛ_ : S₁ ⇛ₛ S₂ → Ctx S₁ → Ctx S₂ → Set
_∶_⇛ₛ_ {S₁} {S₂} σ Γ₁ Γ₂ = ∀ (s : Sort) (x : s ∈ S₁) (T : S₁ ∶⊢ s) → x ∶ T ∈ Γ₁ → Γ₂ ⊢ (σ _ x) ∶ (T ⋯ₛ σ)

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

-- Subject Reduction ----------------------------------------------------------- 

⊢wkᵣ : ∀ (Γ : Ctx S) (x : s ∈ S) (T : S ∶⊢ s) (T' : S ∶⊢ s') → x ∶ T ∈ Γ → (there x) ∶ (wk T) ∈ (Γ ، T')
⊢wkᵣ _ _ _ _ refl = refl

⊢↑ᵣ : ρ ∶ Γ₁ ⇛ᵣ Γ₂ → (T : S₁ ∶⊢ s) → (ρ ↑ᵣ s) ∶ Γ₁ ، T ⇛ᵣ (Γ₂ ، (T ⋯ᵣ ρ))
⊢↑ᵣ ⊢ρ T _ (here refl) _ refl = refl
⊢↑ᵣ {ρ = ρ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ⊢ρ T _ (there x) _ refl = ⊢wkᵣ Γ₂ (ρ _ x) (wk-drop-∈ x (Γ₁ _ x) ⋯ᵣ ρ) (T ⋯ᵣ ρ) (⊢ρ _ x _ refl)

⊢ρ-preserves : ∀ {t : S₁ ⊢ s} {T : S₁ ⊢ (⤊ s)} →
  ρ ∶ Γ₁ ⇛ᵣ Γ₂ →
  Γ₁ ⊢ t ∶ T →
  Γ₂ ⊢ (t ⋯ᵣ ρ) ∶ (T ⋯ᵣ ρ)
⊢ρ-preserves ⊢ρ (⊢` ⊢x)        = ⊢` (⊢ρ _ _ _ ⊢x) 
⊢ρ-preserves ⊢ρ (⊢λ ⊢e)        = ⊢λ (⊢ρ-preserves (⊢↑ᵣ ⊢ρ _) ⊢e)
⊢ρ-preserves ⊢ρ (⊢Λ ⊢e)        = ⊢Λ ((⊢ρ-preserves (⊢↑ᵣ ⊢ρ _) ⊢e))
⊢ρ-preserves ⊢ρ (⊢· ⊢e₁ ⊢e₂)   = ⊢· (⊢ρ-preserves ⊢ρ ⊢e₁) (⊢ρ-preserves ⊢ρ ⊢e₂)
⊢ρ-preserves ⊢ρ (⊢∙ ⊢e ⊢t ⊢t') = ⊢∙ (⊢ρ-preserves ⊢ρ ⊢e) (⊢ρ-preserves ⊢ρ ⊢t) ((⊢ρ-preserves (⊢↑ᵣ ⊢ρ _) ⊢t'))
⊢ρ-preserves ⊢ρ ⊢★             = ⊢★

⊢wkₛ : ∀ (Γ : Ctx S) (t : S ⊢ s) (T : S ∶⊢ s) (T' : S ∶⊢ s') → Γ ⊢ t ∶ T → (Γ ، T') ⊢ wk t ∶ wk T 
⊢wkₛ Γ _ _ T' ⊢T = ⊢ρ-preserves (λ s x T ⊢x → ⊢wkᵣ Γ x T T' ⊢x) ⊢T

⊢↑ₛ : σ ∶ Γ₁ ⇛ₛ Γ₂ → (T : S ∶⊢ s) → (σ ↑ₛ s) ∶ Γ₁ ، T ⇛ₛ (Γ₂ ، (T ⋯ₛ σ))
⊢↑ₛ ⊢σ T _ (here refl) _ refl = ⊢` refl
⊢↑ₛ {σ = σ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ⊢σ T _ (there x) _ refl = ⊢wkₛ Γ₂ (σ _ x) (wk-drop-∈ x (Γ₁ _ x) ⋯ₛ σ) (T ⋯ₛ σ) (⊢σ _ x _ refl)

⊢σ-preserves : ∀ {t : S₁ ⊢ s} {T : S₁ ⊢ (⤊ s)} →
  σ ∶ Γ₁ ⇛ₛ Γ₂ →
  Γ₁ ⊢ t ∶ T →
  Γ₂ ⊢ (t ⋯ₛ σ) ∶ (T ⋯ₛ σ)
⊢σ-preserves ⊢σ (⊢` ⊢x)        = ⊢σ _ _ _ ⊢x
⊢σ-preserves ⊢σ (⊢λ ⊢e)        = ⊢λ (⊢σ-preserves (⊢↑ₛ ⊢σ _) ⊢e)
⊢σ-preserves ⊢σ (⊢Λ ⊢e)        = ⊢Λ (⊢σ-preserves (⊢↑ₛ ⊢σ _) ⊢e)
⊢σ-preserves ⊢σ (⊢· ⊢e₁ ⊢e₂)   = ⊢· (⊢σ-preserves ⊢σ ⊢e₁) (⊢σ-preserves ⊢σ ⊢e₂)
⊢σ-preserves ⊢σ (⊢∙ ⊢e ⊢t ⊢t') = ⊢∙ (⊢σ-preserves ⊢σ ⊢e) (⊢σ-preserves ⊢σ ⊢t) (⊢σ-preserves (⊢↑ₛ ⊢σ _) ⊢t')
⊢σ-preserves ⊢σ ⊢★             = ⊢★

⊢[] : ∀ {Γ : Ctx S} {t : S ⊢ s} {T : S ∶⊢ s} → Γ ⊢ t ∶ T → (t ∷ₛ idₛ) ∶ (Γ ، T) ⇛ₛ Γ
⊢[] ⊢t _ (here refl) _ refl = ⊢t
⊢[] ⊢t _ (there x)   _ refl = ⊢` refl

subject-reduction : 
  Γ ⊢ e ∶ t →   
  e ↪ e' → 
  Γ ⊢ e' ∶ t 
subject-reduction (⊢· (⊢λ ⊢e₁) ⊢e₂)             (β-λ v₂)      = ⊢σ-preserves (⊢[] ⊢e₂) ⊢e₁
subject-reduction (⊢· ⊢e₁ ⊢e₂)                  (ξ-·₁ e₁↪e)   = ⊢· (subject-reduction ⊢e₁ e₁↪e) ⊢e₂
subject-reduction (⊢· ⊢e₁ ⊢e₂)                  (ξ-·₂ e₂↪e x) = ⊢· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e)       
subject-reduction (⊢∙ {t' = t'} (⊢Λ ⊢e) ⊢t ⊢t') β-Λ           = ⊢σ-preserves (⊢[] ⊢t) ⊢e        
subject-reduction (⊢∙ ⊢e ⊢t ⊢t')                (ξ-∙ e↪e')    = ⊢∙ (subject-reduction ⊢e e↪e') ⊢t ⊢t'                                  