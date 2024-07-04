{-# OPTIONS --rewriting #-}
module SystemF where

-- Imports ---------------------------------------------------------------------

open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; ∃-syntax)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional public using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst)

open import Agda.Builtin.Equality.Rewrite

-- Sorts -----------------------------------------------------------------------

data Sort : Set where 
  expr : Sort
  type : Sort 
  kind : Sort 

variable
  s s₁ s₂ s₃ s' s₁' s₂' s₃' : Sort
  S S₁ S₂ S₃ S' S₁' S₂' S₃' : List Sort
  
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
  x x₁ x₂ x₃ x' x₁' x₂' x₃' : s ∈ S
  e e₁ e₂ e₃ e' e₁' e₂' e₃' : S ⊢ expr
  t t₁ t₂ t₃ t' t₁' t₂' t₃' : S ⊢ type
  k k₁ k₂ k₃ k' k₁' k₂' k₃' : S ⊢ kind

-- Renamings -------------------------------------------------------------------

data _⇛ᵣ_ : List Sort → List Sort → Set where
  id  : S ⇛ᵣ S
  wk  : S₁ ⇛ᵣ S₂ → S₁ ⇛ᵣ (s ∷ S₂)
  _∷_ : s ∈ S₂ → S₁ ⇛ᵣ S₂ → (s ∷ S₁) ⇛ᵣ S₂

variable
  ρ ρ₁ ρ₂ ρ₃ ρ' ρ₁' ρ₂' ρ₃' : S₁ ⇛ᵣ S₂

_↑ᵣ_ : S₁ ⇛ᵣ S₂ → (s : Sort) → (s ∷ S₁) ⇛ᵣ (s ∷ S₂)
ρ ↑ᵣ _ = (here refl) ∷ wk ρ

_⋯xᵣ_ : s ∈ S₁ → S₁ ⇛ᵣ S₂ → s ∈ S₂ 
x ⋯xᵣ id              = x
x ⋯xᵣ wk ρ            = there (x ⋯xᵣ ρ)
here refl ⋯xᵣ (x ∷ ρ) = x
there x ⋯xᵣ (_ ∷ ρ)   = x ⋯xᵣ ρ

_⋯ᵣ_ : S₁ ⊢ s → S₁ ⇛ᵣ S₂ → S₂ ⊢ s
(` x)         ⋯ᵣ ρ = ` (x ⋯xᵣ ρ)
(λx e)        ⋯ᵣ ρ = λx (e ⋯ᵣ (ρ ↑ᵣ _))
(Λα e)        ⋯ᵣ ρ = Λα (e ⋯ᵣ (ρ ↑ᵣ _))
(∀[α∶ k ] t)  ⋯ᵣ ρ = ∀[α∶ k ⋯ᵣ ρ ] (t ⋯ᵣ (ρ ↑ᵣ _))
(e₁ · e₂)     ⋯ᵣ ρ = (e₁ ⋯ᵣ ρ) · (e₂ ⋯ᵣ ρ)
(e ∙ t)       ⋯ᵣ ρ = (e ⋯ᵣ ρ) ∙ (t ⋯ᵣ ρ)
(t₁ ⇒ t₂)     ⋯ᵣ ρ = (t₁ ⋯ᵣ ρ) ⇒ (t₂ ⋯ᵣ ρ)
★             ⋯ᵣ ρ = ★ 

postulate
  id⋯ᵣ : ∀ (T : S ⊢ s) → T ⋯ᵣ id ≡ T
{-# REWRITE id⋯ᵣ #-}

wkₜ : S ⊢ s → (s' ∷ S) ⊢ s
wkₜ T = T ⋯ᵣ wk id

-- Substitution ----------------------------------------------------------------

data _⇛ₛ_ : List Sort → List Sort → Set where
  id  : S ⇛ₛ S
  wk  : S₁ ⇛ₛ S₂ → S₁ ⇛ₛ (s ∷ S₂)
  _∷_ : S₂ ⊢ s → S₁ ⇛ₛ S₂ → (s ∷ S₁) ⇛ₛ S₂

variable
  σ σ₁ σ₂ σ₃ σ' σ₁' σ₂' σ₃' : S₁ ⇛ₛ S₂
 
_↑ₛ_ : S₁ ⇛ₛ S₂ → (s : Sort) → (s ∷ S₁) ⇛ₛ (s ∷ S₂)
σ ↑ₛ _ = (` here refl) ∷ (wk σ)

_⋯ₛ_ : S₁ ⊢ s → S₁ ⇛ₛ S₂ → S₂ ⊢ s
T             ⋯ₛ id        = T
T             ⋯ₛ (wk σ)    = wkₜ (T ⋯ₛ σ)
(` here refl) ⋯ₛ (T ∷ σ)   = T
(` there x)   ⋯ₛ (_ ∷ σ)   = (` x) ⋯ₛ σ
(λx e)        ⋯ₛ σ@(_ ∷ _) = λx (e ⋯ₛ (σ ↑ₛ _))
(Λα e)        ⋯ₛ σ@(_ ∷ _) = Λα (e ⋯ₛ (σ ↑ₛ _))
(∀[α∶ k ] t)  ⋯ₛ σ@(_ ∷ _) = ∀[α∶ k ⋯ₛ σ ] (t ⋯ₛ (σ ↑ₛ _))
(e₁ · e₂)     ⋯ₛ σ@(_ ∷ _) = (e₁ ⋯ₛ σ) · (e₂ ⋯ₛ σ)
(e ∙ t)       ⋯ₛ σ@(_ ∷ _) = (e ⋯ₛ σ) ∙ (t ⋯ₛ σ)
(t₁ ⇒ t₂)     ⋯ₛ σ@(_ ∷ _) = (t₁ ⋯ₛ σ) ⇒ (t₂ ⋯ₛ σ)
★             ⋯ₛ σ@(_ ∷ _) = ★ 

_[_] : (s' ∷ S) ⊢ s → S ⊢ s' → S ⊢ s
T [ T' ] = T ⋯ₛ (T' ∷ id) 

-- Fusion -------------------------------------------------------------------------

_∘ᵣᵣ_ : S₂ ⇛ᵣ S₃ → S₁ ⇛ᵣ S₂ → S₁ ⇛ᵣ S₃
id         ∘ᵣᵣ ρ₁       = ρ₁
wk ρ₂      ∘ᵣᵣ ρ₁       = wk (ρ₂ ∘ᵣᵣ ρ₁)
ρ₂@(_ ∷ _) ∘ᵣᵣ id       = ρ₂
(_ ∷ ρ₂)   ∘ᵣᵣ wk ρ₁    = ρ₂ ∘ᵣᵣ ρ₁
ρ₂@(_ ∷ _) ∘ᵣᵣ (x ∷ ρ₁) = (x ⋯xᵣ ρ₂) ∷ (ρ₂ ∘ᵣᵣ ρ₁)

_∘ₛᵣ_ : S₂ ⇛ₛ S₃ → S₁ ⇛ᵣ S₂ → S₁ ⇛ₛ S₃
id         ∘ₛᵣ id       = id
id         ∘ₛᵣ wk ρ₁    = wk (id ∘ₛᵣ ρ₁)
id         ∘ₛᵣ (x ∷ ρ₁) = (` x) ∷ (id ∘ₛᵣ ρ₁)
wk σ₂      ∘ₛᵣ ρ₁       = wk (σ₂ ∘ₛᵣ ρ₁)
σ₂@(_ ∷ _) ∘ₛᵣ id       = σ₂
(_ ∷ σ₂)   ∘ₛᵣ wk ρ₁    = σ₂ ∘ₛᵣ ρ₁
σ₂@(T ∷ _) ∘ₛᵣ (x ∷ ρ₁) = ((` x) ⋯ₛ σ₂) ∷ (σ₂ ∘ₛᵣ ρ₁)

_∘ᵣₛ_ : S₂ ⇛ᵣ S₃ → S₁ ⇛ₛ S₂ → S₁ ⇛ₛ S₃
id         ∘ᵣₛ σ₁        = σ₁
wk ρ₂      ∘ᵣₛ σ₁        = wk (ρ₂ ∘ᵣₛ σ₁)
(x ∷ ρ₂)   ∘ᵣₛ id        = (` x) ∷ (ρ₂ ∘ᵣₛ id)
(_ ∷ ρ₂)   ∘ᵣₛ wk σ₁     = ρ₂ ∘ᵣₛ σ₁
ρ₂@(_ ∷ _) ∘ᵣₛ (T ∷ σ₁)  = (T ⋯ᵣ ρ₂) ∷ (ρ₂ ∘ᵣₛ σ₁)

_∘ₛₛ_ : S₂ ⇛ₛ S₃ → S₁ ⇛ₛ S₂ → S₁ ⇛ₛ S₃
id         ∘ₛₛ σ₂        = σ₂
wk σ₁      ∘ₛₛ σ₂        = wk (σ₁ ∘ₛₛ σ₂)
σ₁@(_ ∷ _) ∘ₛₛ id        = σ₁
(_ ∷ σ₁)   ∘ₛₛ wk σ₂     = σ₁ ∘ₛₛ σ₂
σ₁@(_ ∷ _) ∘ₛₛ (T ∷ σ₂)  = (T ⋯ₛ σ₁) ∷ (σ₁ ∘ₛₛ σ₂)

idₛᵣ : (σ : S₁ ⇛ₛ S₂) → σ ∘ₛᵣ id ≡ σ 
idₛᵣ id      = refl
idₛᵣ (wk σ)  = cong wk (idₛᵣ σ)
idₛᵣ (x ∷ σ) = refl
{-# REWRITE idₛᵣ #-}

idᵣᵣ : (ρ : S₁ ⇛ᵣ S₂) → ρ ∘ᵣᵣ id ≡ ρ 
idᵣᵣ id      = refl
idᵣᵣ (wk ρ)  = cong wk (idᵣᵣ ρ)
idᵣᵣ (x ∷ ρ) = refl
{-# REWRITE idᵣᵣ #-}

idₛₛ : (σ : S₁ ⇛ₛ S₂) → σ ∘ₛₛ id ≡ σ  
idₛₛ id      = refl
idₛₛ (wk σ ) = cong wk (idₛₛ σ)
idₛₛ (x ∷ σ) = refl
{-# REWRITE idₛₛ #-}

postulate
  fusionᵣᵣ : (T : S₁ ⊢ s) → (ρ₂ : S₂ ⇛ᵣ S₃) → (ρ₁ : S₁ ⇛ᵣ S₂) → (T ⋯ᵣ ρ₁) ⋯ᵣ ρ₂ ≡ T ⋯ᵣ (ρ₂ ∘ᵣᵣ ρ₁)
{-# REWRITE fusionᵣᵣ #-}

-- fusion↑ᵣᵣ : (T : S₁ ⊢ s) → (ρ₂ : S₂ ⇛ᵣ S₃) → (ρ₁ : S₁ ⇛ᵣ S₂) → (T ⋯ᵣ ρ₁) ⋯ᵣ ρ₂ ≡ T ⋯ᵣ (ρ₂ ∘ᵣᵣ ρ₁)
-- 
-- fusionᵣᵣ T ρ₂ ρ₁ = {!   !}
-- fusion↑ᵣᵣ T ρ₂ ρ₁ = {!   !}


postulate 
  fusionₛᵣ : (T : S₁ ⊢ s) → (σ₂ : S₂ ⇛ₛ S₃) → (ρ₁ : S₁ ⇛ᵣ S₂) → (T ⋯ᵣ ρ₁) ⋯ₛ σ₂ ≡ T ⋯ₛ (σ₂ ∘ₛᵣ ρ₁)
{-# REWRITE fusionₛᵣ #-}

-- fusion↑ₛᵣ : (T : S₁ ⊢ s) → (σ₂ : S₂ ⇛ₛ S₃) → (ρ₁ : S₁ ⇛ᵣ S₂) → (T ⋯ᵣ ρ₁) ⋯ₛ σ₂ ≡ T ⋯ₛ (σ₂ ∘ₛᵣ ρ₁)
-- 
-- fusionₛᵣ T id id = refl
-- fusionₛᵣ T id (wk ρ₁) = cong wkₜ (fusionₛᵣ T id ρ₁)
-- fusionₛᵣ T id (x ∷ ρ₁) = {! (fusionₛᵣ T ? ρ₁)   !}
-- fusionₛᵣ T (wk σ₂) ρ₁ = cong wkₜ (fusionₛᵣ T σ₂ ρ₁)
-- fusionₛᵣ T (x ∷ σ₂) ρ₁ = {!   !}
-- fusion↑ₛᵣ T σ₂ ρ₁ = {!   !}


postulate
  fusionᵣₛ : (T : S₁ ⊢ s) → (ρ₂ : S₂ ⇛ᵣ S₃) → (σ₁ : S₁ ⇛ₛ S₂) → (T ⋯ₛ σ₁) ⋯ᵣ ρ₂ ≡ T ⋯ₛ (ρ₂ ∘ᵣₛ σ₁)
-- {-# REWRITE fusionᵣₛ #-}

-- fusion↑ᵣₛ : (T : S₁ ⊢ s) → (ρ₂ : S₂ ⇛ᵣ S₃) → (σ₁ : S₁ ⇛ₛ S₂) → (T ⋯ₛ σ₁) ⋯ᵣ ρ₂ ≡ T ⋯ₛ (ρ₂ ∘ᵣₛ σ₁)
-- fusionᵣₛ T ρ₂ σ₁ = {!   !}

fusionₛₛ : (T : S₁ ⊢ s) → (σ₂ : S₂ ⇛ₛ S₃) →(σ₁ : S₁ ⇛ₛ S₂) → (T ⋯ₛ σ₁) ⋯ₛ σ₂ ≡ T ⋯ₛ (σ₂ ∘ₛₛ σ₁)
fusionₛₛ T             id         σ₁         = refl
fusionₛₛ T             (wk σ₂)    σ₁         = cong wkₜ (fusionₛₛ T σ₂ σ₁ )
fusionₛₛ T             (_ ∷ _)    id         = refl
fusionₛₛ T             (_ ∷ σ₂)   (wk σ₁)    = fusionₛₛ T σ₂ σ₁
fusionₛₛ (` here refl) (_ ∷ _)    (_ ∷ _)    = refl
fusionₛₛ (` there x)   σ₂@(_ ∷ _) (_ ∷ σ₁)   = fusionₛₛ (` x) σ₂ σ₁
fusionₛₛ (λx e)        σ₂@(_ ∷ _) σ₁@(_ ∷ _) = cong λx_ (fusionₛₛ e (σ₂ ↑ₛ _) (σ₁ ↑ₛ _))
fusionₛₛ (Λα e)        σ₂@(_ ∷ _) σ₁@(_ ∷ _) = cong Λα_ (fusionₛₛ e (σ₂ ↑ₛ _) (σ₁ ↑ₛ _))
fusionₛₛ (∀[α∶ k ] t)  σ₂@(_ ∷ _) σ₁@(_ ∷ _) = cong₂ ∀[α∶_]_ (fusionₛₛ k σ₂ σ₁)  (fusionₛₛ t (σ₂ ↑ₛ _) (σ₁ ↑ₛ _))
fusionₛₛ (e₁ · e₂)     σ₂@(_ ∷ _) σ₁@(_ ∷ _) = cong₂ _·_ (fusionₛₛ e₁ σ₂ σ₁)  (fusionₛₛ e₂ σ₂ σ₁)
fusionₛₛ (e ∙ t)       σ₂@(_ ∷ _) σ₁@(_ ∷ _) = cong₂ _∙_ (fusionₛₛ e σ₂ σ₁)  (fusionₛₛ t σ₂ σ₁)
fusionₛₛ (t₁ ⇒ t₂)     σ₂@(_ ∷ _) σ₁@(_ ∷ _) = cong₂ _⇒_ (fusionₛₛ t₁ σ₂ σ₁) (fusionₛₛ t₂ σ₂ σ₁)
fusionₛₛ ★             σ₂@(_ ∷ _) σ₁@(_ ∷ _) = refl
{-# REWRITE fusionₛₛ #-}

-- -- Typing ----------------------------------------------------------------------
-- 
-- ⤊_ : Sort → Sort
-- ⤊ expr = type
-- ⤊ type = kind
-- ⤊ kind = kind
-- 
-- _:⊢_ : List Sort → Sort → Set
-- S :⊢ s = S ⊢ (⤊ s)
-- 
-- data Ctx : List Sort → Set where
--   ∅   : Ctx []
--   _,_ : Ctx S → S :⊢ s → Ctx (s ∷ S)
-- 
-- variable 
--   Γ Γ₁ Γ₂ Γ₃ Γ' Γ₁' Γ₂' Γ₃' : Ctx S
-- 
-- data _⊢_∶_ : Ctx S → S ⊢ s → S :⊢ s → Set where
--   ⊢here : ∀ {T : S ⊢ (⤊ s)} → 
--     ---------------------------------
--     (Γ , T) ⊢ (` (here refl)) ∶ wkₜ T
--   ⊢there : ∀ {T : S ⊢ (⤊ s)} {T' : S ⊢ (⤊ s')}  → 
--     Γ ⊢ (` x) ∶ T →
--     ------------------------------
--     (Γ , T') ⊢ (` (there x)) ∶ wkₜ T
--   ⊢λ : 
--     (Γ , t) ⊢ e ∶ (wkₜ t') → 
--     ---------------------
--     Γ ⊢ (λx e) ∶ (t ⇒ t')
--   ⊢Λ :
--     (Γ , k) ⊢ e ∶ t →  
--     -------------------------
--     Γ ⊢ (Λα e) ∶ (∀[α∶ k ] t)
--   ⊢· : 
--     Γ ⊢ e₁ ∶ (t₁ ⇒ t₂) →
--     Γ ⊢ e₂ ∶ t₁ →
--     ------------------
--     Γ ⊢ (e₁ · e₂) ∶ t₂
--   ⊢∙ : 
--     Γ ⊢ t ∶ k →
--     (Γ , k) ⊢ t' ∶ k' →
--     Γ ⊢ e ∶ (∀[α∶ k ] t') →
--     ------------------------
--     Γ ⊢ (e ∙ t) ∶ (t' [ t ])
--   ⊢★ : 
--     ---------
--     Γ ⊢ t ∶ ★
-- 
-- data _∶_⇛ᵣ_ : S₁ ⇛ᵣ S₂ → Ctx S₁ → Ctx S₂ → Set where
--   ⊢id : 
--     ----------
--     id ∶ Γ ⇛ᵣ Γ 
--   ⊢wk : ∀ {T : S₂ ⊢ (⤊ s)} → 
--     ρ ∶ Γ₁ ⇛ᵣ Γ₂ → 
--     ----------------------
--     (wk ρ) ∶ Γ₁ ⇛ᵣ (Γ₂ ,  T)
--   ⊢∷ : ∀ {T : S₁ ⊢ (⤊ s)}  →
--     ρ ∶ Γ₁ ⇛ᵣ Γ₂ →
--     Γ₂ ⊢ (` x) ∶ (T ⋯ᵣ ρ) →
--     -----------------------
--     (x ∷ ρ) ∶ (Γ₁ , T) ⇛ᵣ Γ₂
-- 
-- ⊢wkₜ : ∀ {T : S ⊢ (⤊ s')} → wk id ∶ Γ ⇛ᵣ (Γ , T)
-- ⊢wkₜ = ⊢wk ⊢id 
-- 
-- ⊢↑ᵣ : ∀ {Γ₁ : Ctx S₁} {T : S₁ ⊢ (⤊ s)} → ρ ∶ Γ₁ ⇛ᵣ Γ₂ → (((here refl)) ∷ wk ρ) ∶ Γ₁ , T ⇛ᵣ (Γ₂ , (T ⋯ᵣ ρ))
-- ⊢↑ᵣ ⊢ρ = ⊢∷ (⊢wk ⊢ρ) ⊢here
-- 
-- data _∶_⇛ₛ_ : S₁ ⇛ₛ S₂ → Ctx S₁ → Ctx S₂ → Set where
--   ⊢id : 
--     ----------
--     id ∶ Γ ⇛ₛ Γ 
--   ⊢wk  : ∀ {T : S₂ ⊢ (⤊ s)} → 
--     σ ∶ Γ₁ ⇛ₛ Γ₂ → 
--     ----------------------
--     (wk σ) ∶ Γ₁ ⇛ₛ (Γ₂ , T)
--   ⊢∷ : ∀ {t : S₂ ⊢ s} {T : S₁ ⊢ (⤊ s)}  →
--     σ ∶ Γ₁ ⇛ₛ Γ₂ →
--     Γ₂ ⊢ t ∶ (T ⋯ₛ σ) →
--     -----------------------
--     (t ∷ σ) ∶ (Γ₁ , T) ⇛ₛ Γ₂
-- 
-- ⊢[] : ∀ {t : S ⊢ s'} {T : S ⊢ (⤊ s')} (⊢t : Γ ⊢ t ∶ T) → (t ∷ id) ∶ (Γ , T) ⇛ₛ Γ 
-- ⊢[] = ⊢∷ ⊢id 
-- 
-- ⊢↑ₛ : ∀ {Γ₁ : Ctx S₁} {T : S₁ ⊢ (⤊ s)} → σ ∶ Γ₁ ⇛ₛ Γ₂ → ((` (here refl)) ∷ wk σ) ∶ Γ₁ , T ⇛ₛ (Γ₂ , (T ⋯ₛ σ))
-- ⊢↑ₛ ⊢σ = ⊢∷ (⊢wk ⊢σ) ⊢here
-- 
-- 
-- -- Semantics -------------------------------------------------------------------
-- 
-- data Val : S ⊢ expr → Set where
--   vλ : Val (λx e)
--   vΛ : Val (Λα e)
-- 
-- data _↪_ : S ⊢ expr → S ⊢ expr → Set where
--   β-λ :
--     Val e₂ →
--     ----------------------------
--     ((λx e₁) · e₂) ↪ (e₁ [ e₂ ])
--   β-Λ :
--     ------------------------
--     ((Λα e) ∙ t) ↪ (e [ t ])
--   ξ-·₁ :
--     e₁ ↪ e →
--     --------------------
--     (e₁ · e₂) ↪ (e · e₂)
--   ξ-·₂ :
--     e₂ ↪ e →
--     Val e₁ →
--     --------------------
--     (e₁ · e₂) ↪ (e₁ · e)
--   ξ-∙ :
--     e ↪ e' →
--     ------------------
--     (e ∙ t) ↪ (e' ∙ t)
-- 
-- -- Soundness -------------------------------------------------------------------
-- 
-- progress : 
--   ∅ ⊢ e ∶ t →
--   (∃[ e' ] (e ↪ e')) ⊎ Val e
-- progress (⊢λ _) = inj₂ vλ
-- progress (⊢Λ _) = inj₂ vΛ
-- progress (⊢· {e₁ = e₁} {e₂ = e₂} ⊢e₁  ⊢e₂) with progress ⊢e₁ | progress ⊢e₂ 
-- ... | inj₁ (e₁' , e₁↪e₁') | _                   = inj₁ (e₁' · e₂ , ξ-·₁ e₁↪e₁')
-- ... | inj₂ v              | inj₁ (e₂' , e₂↪e₂') = inj₁ (e₁ · e₂' , ξ-·₂ e₂↪e₂' v)
-- ... | inj₂ (vλ {e = e₁})  | inj₂ v              = inj₁ (e₁ [ e₂ ] , β-λ v)
-- progress (⊢∙ {t = t} _ _ ⊢e) with progress ⊢e 
-- ... | inj₁ (e' , e↪e')  = inj₁ (e' ∙ t , ξ-∙ e↪e')
-- ... | inj₂ (vΛ {e = e}) = inj₁ (e [ t ] , β-Λ)
-- 
-- ⊢ρ-preserves : ∀ {t : S₁ ⊢ s} {T : S₁ ⊢ (⤊ s)} →
--   ρ ∶ Γ₁ ⇛ᵣ Γ₂ →
--   Γ₁ ⊢ t ∶ T →
--   Γ₂ ⊢ (t ⋯ᵣ ρ) ∶ (T ⋯ᵣ ρ)
-- ⊢ρ-preserves ⊢id ⊢here                  = ⊢here
-- ⊢ρ-preserves (⊢wk ⊢ρ)   ⊢here           = ⊢there (⊢ρ-preserves ⊢ρ ⊢here)
-- ⊢ρ-preserves (⊢∷ ⊢ρ ⊢T) ⊢here           = ⊢T
-- ⊢ρ-preserves ⊢id        (⊢there ⊢x)     = ⊢there ⊢x
-- ⊢ρ-preserves (⊢wk ⊢ρ)   (⊢there ⊢x)     = ⊢there (⊢ρ-preserves ⊢ρ (⊢there ⊢x))
-- ⊢ρ-preserves (⊢∷ ⊢ρ _)  (⊢there ⊢x)     = ⊢ρ-preserves ⊢ρ ⊢x
-- ⊢ρ-preserves ⊢ρ         (⊢λ ⊢e)         = ⊢λ (⊢ρ-preserves (⊢↑ᵣ ⊢ρ) ⊢e)
-- ⊢ρ-preserves ⊢ρ         (⊢Λ ⊢e)         = ⊢Λ (⊢ρ-preserves (⊢↑ᵣ ⊢ρ) ⊢e)
-- ⊢ρ-preserves ⊢ρ         (⊢· ⊢e₁ ⊢e₂)    = ⊢· (⊢ρ-preserves ⊢ρ ⊢e₁) (⊢ρ-preserves ⊢ρ ⊢e₂)
-- ⊢ρ-preserves ⊢ρ         (⊢∙ ⊢t ⊢t' ⊢e)  = {! ⊢∙ (⊢ρ-preserves ⊢ρ ⊢t) ((⊢ρ-preserves (⊢↑ᵣ ⊢ρ) ⊢t')) (⊢ρ-preserves ⊢ρ ⊢e)  !}
-- ⊢ρ-preserves ⊢ρ         ⊢★              = ⊢★
-- 
-- ⊢σ-preserves : ∀ {t : S₁ ⊢ s} {T : S₁ ⊢ (⤊ s)} →
--   σ ∶ Γ₁ ⇛ₛ Γ₂ →
--   Γ₁ ⊢ t ∶ T →
--   Γ₂ ⊢ (t ⋯ₛ σ) ∶ (T ⋯ₛ σ)
-- ⊢σ-preserves ⊢id         ⊢T             = ⊢T
-- ⊢σ-preserves (⊢wk ⊢σ)    ⊢T             = ⊢ρ-preserves ⊢wkₜ (⊢σ-preserves ⊢σ ⊢T)
-- ⊢σ-preserves (⊢∷ ⊢σ ⊢T)  (⊢here)        = ⊢T
-- ⊢σ-preserves (⊢∷ ⊢σ ⊢T)  (⊢there ⊢x)    = ⊢σ-preserves ⊢σ ⊢x
-- ⊢σ-preserves ⊢σ@(⊢∷ _ _) (⊢λ ⊢e)        = ⊢λ (⊢σ-preserves (⊢↑ₛ ⊢σ) ⊢e)
-- ⊢σ-preserves ⊢σ@(⊢∷ _ _) (⊢Λ ⊢e)        = ⊢Λ (⊢σ-preserves (⊢↑ₛ ⊢σ) ⊢e)
-- ⊢σ-preserves ⊢σ@(⊢∷ _ _) (⊢· ⊢e₁ ⊢e₂)   = ⊢· (⊢σ-preserves ⊢σ ⊢e₁) (⊢σ-preserves ⊢σ ⊢e₂)
-- ⊢σ-preserves ⊢σ@(⊢∷ _ _) (⊢∙ ⊢t ⊢t' ⊢e) = ⊢∙ (⊢σ-preserves ⊢σ ⊢t) ((⊢σ-preserves (⊢↑ₛ ⊢σ) ⊢t')) (⊢σ-preserves ⊢σ ⊢e)
-- ⊢σ-preserves (⊢∷ _ _)  ⊢★               = ⊢★
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