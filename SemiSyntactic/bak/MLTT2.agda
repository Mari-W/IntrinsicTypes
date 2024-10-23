module MLTT2 where

open import Level
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

variable 
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ' ℓ₁' ℓ₂' ℓ₃' : Level

variable
  A A₁ A₂ A₃ A' A₁' A₂' A₃' : Set ℓ
  a a₁ a₂ a₃ a' a₁' a₂' a₃' : A
  
data Ctx : Setω
variable 
  Γ Γ₁ Γ₂ Γ₃ Γ' Γ₁' Γ₂' Γ₃' : Ctx

data Term (Γ : Ctx) : {ℓ : Level} → Set ℓ → Setω
variable
  T T₁ T₂ T₃ T' T₁' T₂' T₃' : Term Γ A

⟦_⟧ : Term Γ A → A

data Ctx where
  ∅    : Ctx
  _,_  : Ctx → A → Ctx

data _∈_ : {A : Set ℓ} → A → Ctx → Setω where
  here  : a ∈ (Γ , a)
  there : a ∈ Γ → a ∈ (Γ , a')

lookup : {Γ : Ctx} → _∈_ {A = A} a Γ → A 
lookup {Γ = .(_ , a)} (here {a = a}) = a
lookup {Γ = .(Γ , _)} (there {Γ = Γ} x) = lookup x

data Term Γ where
  `_ : _∈_ {A = A} a Γ → Term Γ A

  _`⊔_  : Term Γ₁ Level → Term Γ₂ Level → Term Γ Level
  `zero : Term Γ Level
  `suc  : Term Γ Level →  Term Γ Level 
  `Set  : (ℓ : Term Γ Level) → Term Γ (Set (suc ⟦ ℓ ⟧)) 

  `⊤  : Term Γ Set
  `tt : Term Γ ⟦ `⊤ {Γ} ⟧

  `∀_∶_ : 
    (A : Term Γ (Set ℓ)) → 
    ({a : ⟦ A ⟧} → (Term (Γ , a) (Set ℓ'))) → 
    Term Γ (Set (ℓ ⊔ ℓ'))
  `λ : 
    {A : Term Γ (Set ℓ)} 
    {B : ({a : ⟦ A ⟧} → (Term (Γ , a) (Set ℓ')))} →
    ({a : ⟦ A ⟧} → Term (Γ , a) (⟦ B {a} ⟧)) → 
    Term Γ ⟦ `∀ A ∶ B ⟧
  
  _·_ :   
    {A : Term Γ (Set ℓ)} 
    {B : ({a : ⟦ A ⟧} → (Term (Γ , a) (Set ℓ')))} →
    Term Γ (∀ (a : ⟦ A ⟧) → ⟦ B {a} ⟧) →
    (T : Term Γ (⟦ A ⟧)) →
    Term Γ ⟦ B {⟦ T ⟧} ⟧

  -- _`≡_ : 
  --   {A : Term Γ (Set ℓ)} →
  --   Term Γ ⟦ A ⟧ → 
  --   Term Γ ⟦ A ⟧ →
  --   Term Γ (Set ℓ)
  -- `refl : 
  --   {A : Term Γ (Set ℓ)} →
  --   {a : Term Γ ⟦ A ⟧} →
  --   Term Γ ⟦ a `≡ a ⟧
  
⟦ ` x ⟧      = lookup x
⟦ ℓ₁ `⊔ ℓ₂ ⟧ = ⟦ ℓ₁ ⟧ ⊔ ⟦ ℓ₂ ⟧
⟦ `zero ⟧    = zero
⟦ `suc ℓ ⟧   = suc ⟦ ℓ ⟧
⟦ `Set ℓ ⟧   = Set ⟦ ℓ ⟧
⟦ `⊤ ⟧       = ⊤
⟦ `tt ⟧      = tt
⟦ `∀ A ∶ B ⟧ = ∀ (a : ⟦ A ⟧) → ⟦ B {a} ⟧
⟦ `λ e ⟧     = λ x → ⟦ e ⟧ 
⟦ e₁ · e₂ ⟧  = ⟦ e₁ ⟧ ⟦ e₂ ⟧
-- ⟦ e₁ `≡ e₂ ⟧ = ⟦ e₁ ⟧ ≡ ⟦ e₂ ⟧
-- ⟦ `refl ⟧    = refl

open import Agda.Primitive using (LevelUniv)

record Σ (A : Setω) (B : A → Setω) : Setω₁ where
  constructor _,_
  field
    fst : A
    snd : B fst

data _⊎_ {ℓ} (A : Setω₁) (B : Set ℓ) : Setω₂ where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl; ≅-to-≡)

typeof : {A : Set ℓ} → Term Γ A → (Σ (Term Γ Level) λ ℓ → Term Γ (Set ⟦ ℓ ⟧)) ⊎ (A ≅ Level)
typeof (` x)      = {!   !}
typeof (_ `⊔ _)   = inj₂ refl
typeof `zero      = inj₂ refl
typeof (`suc t)   = inj₂ refl
typeof (`Set ℓ)   = inj₁ (`suc (`suc ℓ) , `Set (`suc ℓ)) 
typeof `⊤         = inj₁ (`suc `zero , `Set `zero)
typeof `tt        = inj₁ (`zero , `⊤)
typeof (`∀ A ∶ B) with typeof A | typeof (B {a = {!   !}})
... | inj₁ (ℓ₁ , snd) | inj₁ (ℓ₂ , snd₁) = inj₁ (`suc (ℓ₁ `⊔ ℓ₂) , (`Set (ℓ₁ `⊔ ℓ₂)))
... | _ | inj₂ y  = {!   !}
... | inj₂ y | _  = {!   !}
typeof (`λ x)     = {!   !}
typeof (e₁ · e₂) with typeof e₁ | typeof e₂
... | inj₁ (ℓ₁ , snd) | inj₁ (ℓ₂ , snd₁) = {!  !}
... | inj₁ x | inj₂ y = {!   !}
... | inj₂ y | b = {!   !}

Ren : Ctx → Ctx → Setω
Ren Γ₁ Γ₂ = ∀ {ℓ} {A : Set ℓ} {a : A} → a ∈ Γ₁ → a ∈ Γ₂

variable
  ρ ρ₁ ρ₂ ρ₃ ρ' ρ₁' ρ₂' ρ₃' : Ren Γ₁ Γ₂ 

idᵣ : Ren Γ Γ
idᵣ x = x

wkᵣ : Ren Γ (Γ , a)
wkᵣ = there 

dropᵣ : Ren (Γ₁ , a) Γ₂ → Ren Γ₁ Γ₂
dropᵣ ρ x = ρ (there x)

_∷ᵣ_ : a ∈ Γ₂ → Ren Γ₁ Γ₂ → Ren (Γ₁ , a) Γ₂
(x ∷ᵣ ρ) here      = x 
(_ ∷ᵣ ρ) (there x) = ρ x 

_≫ᵣᵣ_ : Ren Γ₁ Γ₂ → Ren Γ₂ Γ₃ → Ren Γ₁ Γ₃
(ρ₁ ≫ᵣᵣ ρ₂) x = ρ₂ (ρ₁ x)

_↑ᵣ_ : Ren Γ₁ Γ₂ → (a : A) → Ren (Γ₁ , a) (Γ₂ , a)
ρ ↑ᵣ _ = here ∷ᵣ (ρ ≫ᵣᵣ wkᵣ)

-- _⋯ᵣ_ : Term Γ₁ A → (ρ : Ren Γ₁ Γ₂) → Term Γ₂ A
-- (` x)      ⋯ᵣ ρ = ` ρ x
-- `zero      ⋯ᵣ ρ  = `zero
-- `suc ℓ     ⋯ᵣ ρ = `suc (ℓ ⋯ᵣ ρ)
-- `Set ℓ     ⋯ᵣ ρ = {! `Set (ℓ ⋯ᵣ ρ)  !}
-- `⊤         ⋯ᵣ ρ = `⊤
-- `tt        ⋯ᵣ ρ = `tt
-- (`∀ A ∶ B) ⋯ᵣ ρ = `∀ A ⋯ᵣ ρ ∶ (B ⋯ᵣ {! ρ ↑ᵣ ?  !})
-- `λ e       ⋯ᵣ ρ = {!   !}
-- (e₁ · e₂)  ⋯ᵣ ρ = {!   !}
 
 