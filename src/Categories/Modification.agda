{-# OPTIONS --without-K --safe #-}

open import Level using (_⊔_)

open import Categories.Bicategory
open import Categories.Category using (module Definitions)
open import Categories.Pseudofunctor
open import Categories.Pseudonatural

module Categories.Modification {o ℓ e t o′ ℓ′ e′ t′}{C : Bicategory o ℓ e t}{D : Bicategory o′ ℓ′ e′ t′} where

open import Categories.Bicategory.Extras D
open hom.HomReasoning

private
  module C = Bicategory C
  module _ {X Y} where
    open import Categories.Morphism.Reasoning (hom X Y) public
    open Definitions (hom X Y) public

-- Modification between pseudonatural transformations, following nLab
record Modification {F G : Pseudofunctor C D}(α β : PseudonaturalTransformation F G) : Set (o ⊔ ℓ′ ⊔ e′ ⊔ t) where
  eta-equality
  private
    module F = Pseudofunctor F
    module G = Pseudofunctor G
    module α = PseudonaturalTransformation α
    module β = PseudonaturalTransformation β

  field
    m : ∀ X → α.η X ⇒₂ β.η X
    commute : ∀ {X Y} f → CommutativeSquare (G.₁.₀ f ▷ m X) (α.commutator.⇒.η f)
                                            (β.commutator.⇒.η f) (m Y ◁ F.₁.₀ f)

idM : {F G : Pseudofunctor C D}{ψ : PseudonaturalTransformation F G} → Modification ψ ψ
idM = record { m = λ _ → id₂ ; commute = λ f → elimʳ ⊚.identity ○ introˡ ⊚.identity }

_∘Mᵥ_ : {F G : Pseudofunctor C D}{α β γ : PseudonaturalTransformation F G}
      → Modification β γ → Modification α β → Modification α γ 
_∘Mᵥ_ m n = record
  { m = λ X → m.m X ∘ᵥ n.m X
  ; commute = λ f → hom.∘-resp-≈ʳ (⟺ ∘ᵥ-distr-▷)
                  ○ glue′ (m.commute f) (n.commute f)
                  ○ hom.∘-resp-≈ˡ ∘ᵥ-distr-◁
  } 
  where
    module m = Modification m
    module n = Modification n

_∘Mₕ_ : {F G H : Pseudofunctor C D}{α β : PseudonaturalTransformation G H}
        {γ δ : PseudonaturalTransformation F G}
      → Modification α β → Modification γ δ → Modification (α ∘PTᵥ γ) (β ∘PTᵥ δ) 
_∘Mₕ_ m n = record
  { m = λ X → m.m X ∘ₕ n.m X
  ; commute = λ f → pullʳ α⇐-⊚
                  ○ extendʳ (pullʳ (⟺ ∘ᵥ-distr-⊚ ○ ⊚-resp-≈ (m.commute f) id-comm-sym ○ ∘ᵥ-distr-⊚)
                              ○ extendʳ (pullʳ α⇒-⊚
                                          ○ extendʳ (pullʳ (⟺ ∘ᵥ-distr-⊚ ○ ⊚-resp-≈ id-comm-sym (n.commute f) ○ ∘ᵥ-distr-⊚)
                                                      ○ extendʳ α⇐-⊚)))
  }
  where
    module m = Modification m
    module n = Modification n

