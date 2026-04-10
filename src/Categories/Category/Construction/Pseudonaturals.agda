{-# OPTIONS --without-K --safe #-}

module Categories.Category.Construction.Pseudonaturals where

open import Level

open import Categories.Category using (Category)
open import Categories.Category.Helper

open import Categories.Bicategory
open import Categories.Pseudofunctor
open import Categories.Pseudonatural
open import Categories.Modification

private
  variable
    o ℓ e t o′ ℓ′ e′ t′ : Level
    C : Bicategory o ℓ e t
    D : Bicategory o′ ℓ′ e′ t′

-- (1-)category of pseudonatural transformations between fixed pseudofunctors
Pseudonaturals : (F G : Pseudofunctor C D) → Category _ _ _
Pseudonaturals {D = D} F G = record
  { Obj = PseudonaturalTransformation F G
  ; _⇒_ = Modification
  ; _≈_ = λ m n → ∀ {X} → Modification.m m X ≈ Modification.m n X
  ; id = idM
  ; _∘_ = _∘Mᵥ_
  ; identityˡ = hom.identityˡ
  ; identityʳ = hom.identityʳ
  ; identity² = hom.identity²
  ; assoc = hom.assoc
  ; sym-assoc = hom.sym-assoc
  ; ∘-resp-≈ = λ p q → hom.∘-resp-≈ p q
  ; equiv = record { refl = hom.Equiv.refl ; sym = λ p → hom.Equiv.sym p ; trans = λ p q → hom.Equiv.trans p q }
  }
  where open Bicategory D
