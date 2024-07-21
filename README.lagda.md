# AutoSubstAgda

Autosubst 2[^Autosubst2] in Agda[^Agda].[^1]

## Project Goals

1. Proof of concept:
    1. Intrinsically scoped, extrinsically typed System F (kinda works)
    2. Intrinsically typed System F (working on this)
4. Make agda understand that the rewriting system is confluent (will be a pain)
3. Generalization to Kits
   (this might actually not be desirable due to tradeoff between additional complexity and code size) 
4. Framework:
    1. Generic universe of syntaxes with binding[^UniverseOfSyntaxesWithBinding]
       (boring)
    2. Kitty-like meta framework based on reflection[^Kitty]
       (cool™)

[^1]: hopefully maybe some day
[^Agda]: https://wiki.portal.chalmers.se/agda
[^Autosubst2]: https://www.ps.uni-saarland.de/extras/autosubst2/
[^Kits]: http://strictlypositive.org/Idiom.pdf
[^UniverseOfSyntaxesWithBinding]:https://arxiv.org/abs/2001.11001
[^Kitty]: https://github.com/m0rphism/kitty/

## Theory

```agda
{-# OPTIONS --rewriting  #-}
open import Function using (id)
open import Data.List using (List; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional public using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite

postulate
   Sort : Set

variable
  s s₁ s₂ s₃ s₄ s' s₁' s₂' s₃' s₄' : Sort
  S S₁ S₂ S₃ S₄ S' S₁' S₂' S₃' S₄' : List Sort

postulate
   _⊢_ : List Sort → Sort → Set
   `_ : s ∈ S → S ⊢ s    
  
_⇛ᵣ_ : List Sort → List Sort → Set
S₁ ⇛ᵣ S₂ = ∀ s → s ∈ S₁ → s ∈ S₂

_⇛ₛ_ : List Sort → List Sort → Set
S₁ ⇛ₛ S₂ = ∀ s → s ∈ S₁ → S₂ ⊢ s

abstract
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
   
   postulate
      _⋯ᵣ_ : S₁ ⊢ s → S₁ ⇛ᵣ S₂ → S₂ ⊢ s
   
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
   
   postulate
      _⋯ₛ_ : S₁ ⊢ s → S₁ ⇛ₛ S₂ → S₂ ⊢ s
   
   _≫ₛₛ_ :  S₁ ⇛ₛ S₂ → S₂ ⇛ₛ S₃ → S₁ ⇛ₛ S₃
   (σ₁ ≫ₛₛ σ₂) _ x = (σ₁ _ x) ⋯ₛ σ₂

   postulate
      -- Renaming Primitives
      idᵣ-def            : (S : List Sort) (s : Sort) → idᵣ {S = S} s ≡ id
      wkᵣ-def            : (x : s ∈ S) → wkᵣ {s = s'} _ x ≡ there x
      ∷ᵣ-def₁            : (x : s ∈ S₂) (ρ : S₁ ⇛ᵣ S₂) → (x ∷ᵣ ρ) _ (here refl) ≡ x
      ∷ᵣ-def₂            : (x : s ∈ S₂) (x' : s ∈ S₁) (ρ : S₁ ⇛ᵣ S₂) → (x ∷ᵣ ρ) _ (there x') ≡ ρ _ x'
      ↑ᵣ-def             : (ρ : S₁ ⇛ᵣ S₂) (s : Sort) → ρ ↑ᵣ s ≡ here refl ∷ᵣ (ρ ≫ᵣᵣ wkᵣ)

      -- Renaming Instantiation Primitves
      -- ⋯ᵣ-defᵢ
      -- Substitution Instantiation Primitves
      -- ⋯ₛ-defᵢ
   
      -- Substitution Primitives 
      idₛ-def            : (S : List Sort) (s : Sort) → idₛ {S = S} s ≡ `_
      ∷ₛ-def₁            : (T : S₂ ⊢ s) (σ : S₁ ⇛ₛ S₂) → (T ∷ₛ σ) _ (here refl) ≡ T
      ∷ₛ-def₂            : (T : S₂ ⊢ s) (x : s ∈ S₁) (σ : S₁ ⇛ₛ S₂) → (T ∷ₛ σ) _ (there x) ≡ σ _ x
      ↑ₛ-def             : (σ : S₁ ⇛ₛ S₂) (s : Sort) → σ ↑ₛ s ≡ (` here refl) ∷ₛ (σ ≫ₛᵣ wkᵣ)
   
      -- Forward Composition Primitves
      ≫ᵣᵣ-def            : (ρ₁ : S₁ ⇛ᵣ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) (x : s ∈ S₁) → (ρ₁ ≫ᵣᵣ ρ₂) _ x ≡ ρ₂ _ (ρ₁ _ x)
      ≫ᵣₛ-def            : (ρ₁ : S₁ ⇛ᵣ S₂) (σ₂ : S₂ ⇛ₛ S₃) (x : s ∈ S₁) → (ρ₁ ≫ᵣₛ σ₂) _ x ≡ σ₂ _ (ρ₁ _ x)
      ≫ₛᵣ-def            : (σ₁ : S₁ ⇛ₛ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) (x : s ∈ S₁) → (σ₁ ≫ₛᵣ ρ₂) _ x ≡ (σ₁ _ x) ⋯ᵣ ρ₂
      ≫ₛₛ-def            : (σ₁ : S₁ ⇛ₛ S₂) (σ₂ : S₂ ⇛ₛ S₃) (x : s ∈ S₁) → (σ₁ ≫ₛₛ σ₂) _ x ≡ (σ₁ _ x) ⋯ₛ σ₂
   
      -- Identity Laws   
      left-idᵣᵣ          : (ρ : S₁ ⇛ᵣ S₂) → idᵣ ≫ᵣᵣ ρ ≡ ρ 
      right-idᵣᵣ         : (ρ : S₁ ⇛ᵣ S₂) → ρ ≫ᵣᵣ idᵣ ≡ ρ
      left-idᵣₛ          : (σ : S₁ ⇛ₛ S₂) → idᵣ ≫ᵣₛ σ ≡ σ
      right-idᵣₛ         : (ρ : S₁ ⇛ᵣ S₂) → ρ ≫ᵣₛ idₛ ≡ ρ ≫ᵣₛ idₛ
      left-idₛᵣ          : (ρ : S₁ ⇛ᵣ S₂) → idₛ ≫ₛᵣ ρ ≡ ρ ≫ᵣₛ idₛ
      -- right-idₛᵣ      : (ρ : S₁ ⇛ᵣ S₂) → ρ ≫ᵣₛ idₛ ≡ ρ ˢ
      left-idₛₛ          : (σ : S₁ ⇛ₛ S₂) → idₛ ≫ₛₛ σ ≡ σ   
      right-idₛₛ         : (σ : S₁ ⇛ₛ S₂) → σ ≫ₛₛ idₛ ≡ σ 
   
      -- Associativity Laws 
      associativityᵣᵣᵣ   : (ρ₁ : S₁ ⇛ᵣ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) (ρ₃ : S₃ ⇛ᵣ S₄) → (ρ₁ ≫ᵣᵣ ρ₂) ≫ᵣᵣ ρ₃ ≡ ρ₁ ≫ᵣᵣ (ρ₂ ≫ᵣᵣ ρ₃)
      associativityᵣᵣₛ   : (ρ₁ : S₁ ⇛ᵣ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) (σ₃ : S₃ ⇛ₛ S₄) → (ρ₁ ≫ᵣᵣ ρ₂) ≫ᵣₛ σ₃ ≡ ρ₁ ≫ᵣₛ (ρ₂ ≫ᵣₛ σ₃)
      associativityᵣₛᵣ   : (ρ₁ : S₁ ⇛ᵣ S₂) (σ₂ : S₂ ⇛ₛ S₃) (ρ₃ : S₃ ⇛ᵣ S₄) → (ρ₁ ≫ᵣₛ σ₂) ≫ₛᵣ ρ₃ ≡ ρ₁ ≫ᵣₛ (σ₂ ≫ₛᵣ ρ₃)
      associativityᵣₛₛ   : (ρ₁ : S₁ ⇛ᵣ S₂) (σ₂ : S₂ ⇛ₛ S₃) (σ₃ : S₃ ⇛ₛ S₄) → (ρ₁ ≫ᵣₛ σ₂) ≫ₛₛ σ₃ ≡ ρ₁ ≫ᵣₛ (σ₂ ≫ₛₛ σ₃) 
      associativityₛᵣᵣ   : (σ₁ : S₁ ⇛ₛ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) (ρ₃ : S₃ ⇛ᵣ S₄) → (σ₁ ≫ₛᵣ ρ₂) ≫ₛᵣ ρ₃ ≡ σ₁ ≫ₛᵣ (ρ₂ ≫ᵣᵣ ρ₃)
      associativityₛᵣₛ   : (σ₁ : S₁ ⇛ₛ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) (σ₃ : S₃ ⇛ₛ S₄) → (σ₁ ≫ₛᵣ ρ₂) ≫ₛₛ σ₃ ≡ σ₁ ≫ₛₛ (ρ₂ ≫ᵣₛ σ₃)
      associativityₛₛᵣ   : (σ₁ : S₁ ⇛ₛ S₂) (σ₂ : S₂ ⇛ₛ S₃) (ρ₃ : S₃ ⇛ᵣ S₄) → (σ₁ ≫ₛₛ σ₂) ≫ₛᵣ ρ₃ ≡ σ₁ ≫ₛₛ (σ₂ ≫ₛᵣ ρ₃)
      associativityₛₛₛ   : (σ₁ : S₁ ⇛ₛ S₂) (σ₂ : S₂ ⇛ₛ S₃) (σ₃ : S₃ ⇛ₛ S₄) → (σ₁ ≫ₛₛ σ₂) ≫ₛₛ σ₃ ≡ σ₁ ≫ₛₛ (σ₂ ≫ₛₛ σ₃)
   
      -- Eta Laws
      η-idᵣ              : _∷ᵣ_ {s = s} {S₁ = S} (here refl) wkᵣ ≡ idᵣ 
      η-idₛ              : _∷ₛ_ {s = s} {S₁ = S} (` here refl) (wkᵣ ≫ᵣₛ idₛ) ≡ idₛ
   
      -- Interaction Laws
      interactᵣ          : (x : s ∈ S₂) (ρ : S₁ ⇛ᵣ S₂) → wkᵣ ≫ᵣᵣ (x ∷ᵣ ρ) ≡ ρ 
      interactₛ          : (T : S₂ ⊢ s) (σ : S₁ ⇛ₛ S₂) → wkᵣ ≫ᵣₛ (T ∷ₛ σ) ≡ σ
      
      -- Distributivity Laws
      distributivityᵣᵣ   : (x : s ∈ S₂) (ρ₁ : S₁ ⇛ᵣ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) → (x ∷ᵣ ρ₁) ≫ᵣᵣ ρ₂ ≡ ρ₂ _ x ∷ᵣ (ρ₁ ≫ᵣᵣ ρ₂)  
      distributivityᵣₛ   : (x : s ∈ S₂) (ρ₁ : S₁ ⇛ᵣ S₂) (σ₂ : S₂ ⇛ₛ S₃) → (x ∷ᵣ ρ₁) ≫ᵣₛ σ₂ ≡ σ₂ _ x ∷ₛ (ρ₁ ≫ᵣₛ σ₂)
      distributivityₛᵣ   : (T : S₂ ⊢ s) (σ₁ : S₁ ⇛ₛ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) → (T ∷ₛ σ₁) ≫ₛᵣ ρ₂ ≡ (T ⋯ᵣ ρ₂) ∷ₛ (σ₁ ≫ₛᵣ ρ₂)
      distributivityₛₛ   : (T : S₂ ⊢ s) (σ₁ : S₁ ⇛ₛ S₂) (σ₂ : S₂ ⇛ₛ S₃) → (T ∷ₛ σ₁) ≫ₛₛ σ₂ ≡ (T ⋯ₛ σ₂) ∷ₛ (σ₁ ≫ₛₛ σ₂)
   
      -- Identity Laws
      ⋯idᵣ               : (T : S ⊢ s) → T ⋯ᵣ idᵣ ≡ T 
      ⋯idₛ               : (T : S ⊢ s) → T ⋯ₛ idₛ ≡ T 
   
      -- Compositionality Laws
      compositionalityᵣᵣ : (ρ₁ : S₁ ⇛ᵣ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) (T : S₁ ⊢ s) → (T ⋯ᵣ ρ₁) ⋯ᵣ ρ₂ ≡ T ⋯ᵣ (ρ₁ ≫ᵣᵣ ρ₂)
      compositionalityᵣₛ : (ρ₁ : S₁ ⇛ᵣ S₂) (σ₂ : S₂ ⇛ₛ S₃) (T : S₁ ⊢ s) → (T ⋯ᵣ ρ₁) ⋯ₛ σ₂ ≡ T ⋯ₛ (ρ₁ ≫ᵣₛ σ₂)
      compositionalityₛᵣ : (σ₁ : S₁ ⇛ₛ S₂) (ρ₂ : S₂ ⇛ᵣ S₃) (T : S₁ ⊢ s) → (T ⋯ₛ σ₁) ⋯ᵣ ρ₂ ≡ T ⋯ₛ (σ₁ ≫ₛᵣ ρ₂)
      compositionalityₛₛ : (σ₁ : S₁ ⇛ₛ S₂) (σ₂ : S₂ ⇛ₛ S₃) (T : S₁ ⊢ s) → (T ⋯ₛ σ₁) ⋯ₛ σ₂ ≡ T ⋯ₛ (σ₁ ≫ₛₛ σ₂)
      
      -- Coinicidence Law
      coincidence        : (ρ : S₁ ⇛ᵣ S₂) (T : S₁ ⊢ s) → T ⋯ₛ (ρ ≫ᵣₛ idₛ) ≡ T ⋯ᵣ ρ


{-# REWRITE compositionalityᵣᵣ compositionalityᵣₛ compositionalityₛᵣ compositionalityₛₛ #-}
{-# REWRITE ⋯idᵣ ⋯idₛ #-}
{-# REWRITE coincidence #-}
{-# REWRITE distributivityᵣᵣ distributivityᵣₛ distributivityₛᵣ distributivityₛₛ #-}
{-# REWRITE interactᵣ interactₛ #-}
{-# REWRITE η-idᵣ η-idₛ #-}
{-# REWRITE associativityᵣᵣᵣ associativityᵣᵣₛ associativityᵣₛᵣ associativityᵣₛₛ associativityₛᵣᵣ associativityₛᵣₛ  associativityₛₛᵣ associativityₛₛₛ #-}
{-# REWRITE left-idᵣᵣ right-idᵣᵣ left-idᵣₛ right-idᵣₛ left-idₛᵣ left-idₛₛ right-idₛₛ #-}
