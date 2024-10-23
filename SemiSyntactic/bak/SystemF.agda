module SystemF where

open import Axiom.Extensionality.Propositional using (∀-extensionality; Extensionality)
open import Level
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional public using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

variable 
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ' ℓ₁' ℓ₂' ℓ₃' : Level

Env = List Level

variable 
  Δ Δ₁ Δ₂ Δ₃ Δ' Δ₁' Δ₂' Δ₃' : Env

data Type : Env → Level → Set 
data Type where
  `_    : ℓ ∈ Δ → Type Δ ℓ
  Unit  : Type Δ zero
  _⇒_   : Type Δ ℓ → Type Δ ℓ' → Type Δ (ℓ ⊔ ℓ')
  ∀α_,_ : ∀ ℓ → Type (ℓ ∷ Δ) ℓ' → Type Δ (suc ℓ ⊔ ℓ')
  
variable
  T T₁ T₂ T₃ T' T₁' T₂' T₃' : Type Δ ℓ

data Env✦ : Env → Setω where
  []   : Env✦ []
  _∷_  : Set ℓ → Env✦ Δ → Env✦ (ℓ ∷ Δ)

variable
  η✦ η✦₁ η✦₂ η✦₃ η✦' η✦₁' η✦₂'η✦₃' : Env✦ Δ  
  ⟦T⟧ ⟦T⟧₁ ⟦T⟧₂ ⟦T⟧₃ ⟦T⟧' ⟦T⟧₁' ⟦T⟧₂' ⟦T⟧₃' : Set ℓ

Env-lookup : Env✦ Δ → ℓ ∈ Δ → Set ℓ
Env-lookup (x ∷ _) (here refl) = x
Env-lookup (_ ∷ η✦) (there x)  = Env-lookup η✦ x 

T⟦_⟧ : (T : Type Δ ℓ) → Env✦ Δ → Set ℓ
T⟦ ` x ⟧      η✦ = Env-lookup η✦ x
T⟦ Unit ⟧     η✦ = ⊤
T⟦ T₁ ⇒ T₂ ⟧  η✦ = T⟦ T₁ ⟧ η✦ → T⟦ T₂ ⟧ η✦
T⟦ ∀α ℓ , T ⟧ η✦ = (α : Set ℓ) → T⟦ T ⟧ (α ∷ η✦)

data Ctx : Setω where
  ∅     : Ctx
  _,_   : Ctx → Set ℓ → Ctx

variable 
  Γ Γ₁ Γ₂ Γ₃ Γ' Γ₁' Γ₂' Γ₃' : Ctx 

data _∈#_ : Set ℓ → Ctx → Setω where
  here   : ⟦T⟧ ∈# (Γ , ⟦T⟧)
  there  : ⟦T⟧ ∈# Γ → ⟦T⟧ ∈# (Γ , ⟦T⟧')
  
data Expr {Δ : Env} (η✦ : Env✦ Δ) (Γ : Ctx) : Set ℓ → Setω where
  `_    : ⟦T⟧ ∈# Γ → Expr η✦ Γ ⟦T⟧
  tt    : Expr η✦ Γ (T⟦ Unit ⟧ η✦)
  λx    : Expr η✦ (Γ , ⟦T⟧₁) ⟦T⟧₂ → Expr η✦ Γ (⟦T⟧₁ → ⟦T⟧₂)
  Λα_,_ : (ℓ : Level) → {T : Type (ℓ ∷ Δ) ℓ'} →
            (∀ {⟦T⟧ : Set ℓ} → Expr η✦ Γ (T⟦ T ⟧ (⟦T⟧ ∷ η✦))) →
            Expr η✦ Γ (T⟦ ∀α ℓ , T ⟧ η✦)
  _·_   : Expr η✦ Γ (T⟦ T₁ ⇒ T₂ ⟧ η✦ ) → Expr η✦ Γ (T⟦ T₁ ⟧ η✦) → Expr η✦ Γ (T⟦ T₂ ⟧ η✦)
  _∙_   : {T : Type (ℓ ∷ Δ) ℓ'} → 
            Expr η✦ Γ (T⟦ ∀α ℓ , T ⟧ η✦) → (T' : Type Δ ℓ) → Expr η✦ Γ (T⟦ T ⟧ (T⟦ T' ⟧ η✦ ∷ η✦))

ex₁ : Expr [] ∅ (T⟦ ∀α zero , ((` here refl) ⇒ (` here refl)) ⟧ [])
ex₁ = (Λα_,_ zero {T = (` here refl) ⇒ (` here refl)} 
            (λ {⟦T⟧} → λx {⟦T⟧₁ = ⟦T⟧}  (` here)))

ex₂ : Expr [] ∅ (T⟦ Unit ⟧ [])  
ex₂ = _·_ {T₁ = Unit} {T₂ = Unit} 
        (_∙_ {T = (` here refl) ⇒ (` here refl)} 
          ex₁
          Unit) 
        tt 

ex₃ : Expr [] ∅ (T⟦ Unit ⇒ Unit ⟧ [])
ex₃ = λx  tt

data Ctx✦ : Ctx → Setω where
  ∅    : Ctx✦ ∅
  _,_  : Ctx✦ Γ → T⟦ T ⟧ η✦ → Ctx✦ (Γ , T⟦ T ⟧ η✦)

Ctx-lookup : Ctx✦ Γ → ⟦T⟧ ∈# Γ → ⟦T⟧
Ctx-lookup (_ , x)   here      = x
Ctx-lookup (Γ✦ , _)  (there x) = Ctx-lookup Γ✦ x 

E⟦_⟧ : Expr η✦ Γ ⟦T⟧ → Ctx✦ Γ → ⟦T⟧
E⟦ ` x      ⟧ Γ✦ = Ctx-lookup Γ✦ x
E⟦ tt       ⟧ Γ✦ = tt
E⟦_⟧ {η✦ = η✦} (λx e) Γ✦ = λ x → E⟦ e ⟧ (_,_ {η✦ = {!  η✦ !}} Γ✦  x)
E⟦ Λα ℓ , e ⟧ Γ✦ = λ α → E⟦ e ⟧ Γ✦
E⟦ e₁ · e₂  ⟧ Γ✦ = E⟦ e₁ ⟧ Γ✦ (E⟦ e₂ ⟧ Γ✦)
E⟦ e ∙ T'   ⟧ Γ✦ = E⟦ e ⟧ Γ✦ (T⟦ T' ⟧ _)
   