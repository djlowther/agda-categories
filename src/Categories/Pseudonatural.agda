{-# OPTIONS --without-K --safe #-}

open import Data.Product using (_,_)
open import Level using (_⊔_)

open import Categories.Bicategory
open import Categories.Functor using (_∘F_)
open import Categories.Functor.Properties using ([_]-resp-≅)
open import Categories.NaturalTransformation.NaturalIsomorphism as NI using (_≃_; NaturalIsomorphism)
open import Categories.NaturalTransformation.NaturalIsomorphism.Properties using (pointwise-iso)
open import Categories.Pseudofunctor

module Categories.Pseudonatural {o ℓ e t o′ ℓ′ e′ t′}{C : Bicategory o ℓ e t}{D : Bicategory o′ ℓ′ e′ t′} where

open import Categories.Bicategory.Extras D
open Shorthands
open hom.HomReasoning

private
  module C = Bicategory C
  module _ {X Y} where
    open import Categories.Morphism (hom X Y) public
    open import Categories.Morphism.Reasoning (hom X Y) public

-- Definition of a pseudonatural transformation mostly follows nLab,
-- but we define the commutator as a natural isomorphism in the hom-categories
-- (equivalent to a family of invertible 2-cells with the 'pseudo-naturality' property specified on nLab)

record PseudonaturalTransformation (F G : Pseudofunctor C D) : Set (o ⊔ o′ ⊔ ℓ ⊔ ℓ′ ⊔ e′ ⊔ t) where
  eta-equality
  private
    module F = Pseudofunctor F
    module G = Pseudofunctor G
  field
    η : ∀ X → F.₀ X ⇒₁ G.₀ X
    commutator : ∀ {X Y} → (-⊚ η X ∘F G.P₁) ≃ (η Y ⊚- ∘F F.P₁) 

  module commutator {X Y} = NaturalIsomorphism (commutator {X}{Y})

  field
    unitality : ∀ {X} → (η X ▷ F.unitˡ.η _) ∘ᵥ ρ⇐ ∘ᵥ λ⇒
                      ≈ commutator.⇒.η C.id₁ ∘ᵥ (G.unitˡ.η _ ◁ η X)
    associativity : ∀ {X Y Z} {f : X C.⇒₁ Y} {g : Y C.⇒₁ Z}
                  → (η Z ▷ F.Hom.η (g , f)) ∘ᵥ α⇒ ∘ᵥ (commutator.⇒.η g ◁ F.₁.₀ f)
                     ∘ᵥ α⇐ ∘ᵥ (G.₁.₀ g ▷ commutator.⇒.η f) ∘ᵥ α⇒
                  ≈ commutator.⇒.η (g C.∘₁ f) ∘ᵥ (G.Hom.η (g , f) ◁ η X) 

idPT : {F : Pseudofunctor C D} → PseudonaturalTransformation F F
idPT {F} = record
  { η = λ _ → id₁
  ; commutator = pointwise-iso (λ _ → ≅.trans unitorʳ (≅.sym unitorˡ))
                               (λ _ → pullʳ ρ⇒-∘ᵥ-◁ ○ extendʳ (⟺  ▷-∘ᵥ-λ⇐))
  ; unitality = unitality
  ; associativity = associativity
  }
  where
    module F = Pseudofunctor F
    unitality : ∀ {X} → (id₁ {F.₀ X} ▷ F.unitˡ.η _) ∘ᵥ ρ⇐ ∘ᵥ λ⇒ ≈ (λ⇐ ∘ᵥ ρ⇒) ∘ᵥ (F.unitˡ.η _ ◁ id₁) 
    unitality = pushʳ (push-eq unitorˡ λ⇒-∘ᵥ-▷ λ⇒-∘ᵥ-▷
                               (⟺ ∘ᵥ-distr-▷
                                ○ hom.∘-resp-≈ (unitorʳ-coherence-var₂
                                                 ○ (refl⟩∘⟨ ⟺ (cancel-fromʳ (≅.sym unitorʳ) ◁-∘ᵥ-ρ⇐))
                                                 ○ (refl⟩∘⟨ ⟺ triangle-inv)
                                                 ○ cancelˡ associator.isoʳ)
                                               (insertʳ associator.isoʳ
                                                 ○ (triangle ⟩∘⟨refl)
                                                 ○ (cancel-fromˡ unitorʳ ρ⇒-∘ᵥ-◁ ⟩∘⟨refl)
                                                 ○ ⟺ (switch-fromtoʳ associator (⟺ unitorʳ-coherence)))
                                ○ ∘ᵥ-distr-▷))
              ○ pushˡ ▷-∘ᵥ-λ⇐
              ○ pushʳ (⟺  ρ⇒-∘ᵥ-◁)
    associativity : ∀ {X Y Z}{f : X C.⇒₁ Y}{g : Y C.⇒₁ Z}
                  → (id₁ ▷ F.Hom.η (g , f)) ∘ᵥ α⇒  ∘ᵥ ((λ⇐ ∘ᵥ ρ⇒) ◁ F.₁.₀ f)
                     ∘ᵥ α⇐ ∘ᵥ (F.₁.₀ g ▷ (λ⇐ ∘ᵥ ρ⇒)) ∘ᵥ α⇒
                  ≈ (λ⇐ ∘ᵥ ρ⇒) ∘ᵥ (F.Hom.η (g , f) ◁ id₁) 
    associativity = hom.∘-resp-≈ʳ (pushʳ (hom.∘-resp-≈ (⟺  ∘ᵥ-distr-◁) (pushʳ (pushˡ (⟺  ∘ᵥ-distr-▷)))))
                  ○ hom.∘-resp-≈ʳ (hom.∘-resp-≈ (pullˡ (pushʳ unitorˡ-coherence-inv ○ elimˡ associator.isoʳ))
                                                (hom.∘-resp-≈ triangle-inv (⟺  unitorʳ-coherence)))
                  ○ pushʳ (cancelInner (∘ᵥ-distr-◁ ○ ◁-resp-≈ unitorʳ.isoʳ ○ id₂◁))
                  ○ pushˡ ▷-∘ᵥ-λ⇐
                  ○ pushʳ (⟺  ρ⇒-∘ᵥ-◁)

_∘PTᵥ_ : {F G H : Pseudofunctor C D}
       → PseudonaturalTransformation G H → PseudonaturalTransformation F G
       → PseudonaturalTransformation F H
_∘PTᵥ_ {F}{G}{H} α β = record
  { η = λ x → α.η x ∘₁ β.η x
  ; commutator = pointwise-iso χ χ-comm
  ; unitality = unitality
  ; associativity = λ {_ _ _ f g} → associativity f g
  }
  where
    module F = Pseudofunctor F
    module G = Pseudofunctor G
    module H = Pseudofunctor H
    module α = PseudonaturalTransformation α
    module β = PseudonaturalTransformation β
    χ : ∀ {x y}(f : x C.⇒₁ y) → (H.₁.₀ f ∘₁ (α.η x ∘₁ β.η x)) ≅ ((α.η y ∘₁ β.η y) ∘₁ F.₁.₀ f) 
    χ f = ≅.trans (≅.sym associator) (≅.trans ([ -⊚ β.η _ ]-resp-≅ α.commutator.FX≅GX)
         (≅.trans associator (≅.trans ([ α.η _ ⊚- ]-resp-≅ β.commutator.FX≅GX)
                  (≅.sym associator))))
                         
    χ-comm : ∀ {x y}{f g : x C.⇒₁ y}(ϕ : f C.⇒₂ g)
           → _≅_.from (χ g) ∘ᵥ (H.₁.₁ ϕ ◁ (α.η x ∘₁ β.η x))
           ≈ ((α.η y ∘₁ β.η y) ▷ F.₁.₁ ϕ) ∘ᵥ _≅_.from (χ f)
    χ-comm ϕ = pullʳ (hom.∘-resp-≈ʳ (⊚-resp-≈ʳ (⟺  ⊚.identity)) ○ ⊚-assoc.⇐.commute _)
                                   ○ pullˡ (pullʳ (◁-resp-sq (α.commutator.⇒.commute _))
                                             ○ pullˡ (pullʳ (⊚-assoc.⇒.commute _)
                                                       ○ pullˡ (pullʳ (▷-resp-sq (β.commutator.⇒.commute _))
                                                                 ○  pullˡ (⊚-assoc.⇐.commute _))))
                                   ○ pushˡ (pushˡ (pushˡ (pushˡ (hom.∘-resp-≈ˡ (⊚-resp-≈ˡ ⊚.identity)))))
    unitality : ∀ {x} → ((α.η x ∘₁ β.η x) ▷ F.unitˡ.η _) ∘ᵥ ρ⇐ ∘ᵥ λ⇒
                      ≈ _≅_.from (χ C.id₁) ∘ᵥ (H.unitˡ.η _ ◁ (α.η x ∘₁ β.η x))
    unitality = pushʳ (insertInner (∘ᵥ-distr-◁ ○ ◁-resp-≈ unitorʳ.isoʳ ○ id₂◁))
              ○ hom.∘-resp-≈ (⟺ (hom.∘-resp-≈ (⊚-resp-≈ˡ ⊚.identity) (hom.∘-resp-≈ unitorʳ-coherence-inv triangle))
                               ○ assoc²δγ
                               ○ hom.∘-resp-≈ (⟺  (⊚-assoc.⇐.commute _)) (pullˡ ∘ᵥ-distr-▷)
                               ○ extend² (▷-resp-sq β.unitality)
                               ○ pushʳ (⟺ (⊚-assoc.⇒.commute _)))
                             (introʳ (⊚-assoc.iso.isoʳ _)
                               ○ pullˡ (pullʳ (⟺ unitorˡ-coherence))
                               ○ hom.∘-resp-≈ˡ ∘ᵥ-distr-◁)
              ○ extend² (◁-resp-sq α.unitality)
              ○ pushʳ (⊚-assoc.⇐.sym-commute _ ○ hom.∘-resp-≈ʳ (⊚-resp-≈ʳ ⊚.identity))
    associativity : ∀ {x y z}(f : x C.⇒₁ y) (g : y C.⇒₁ z)
                  → ((α.η z ∘₁ β.η z) ▷ F.Hom.η (g , f)) ∘ᵥ α⇒ ∘ᵥ (_≅_.from (χ g) ◁ F.₁.₀ f)
                     ∘ᵥ α⇐ ∘ᵥ (H.₁.₀ g ▷ _≅_.from (χ f)) ∘ᵥ α⇒
                  ≈ _≅_.from (χ (g C.∘₁ f)) ∘ᵥ (H.Hom.η (g , f) ◁ (α.η x ∘₁ β.η x)) 
    associativity {x}{y}{z} f g = begin ((α.η z ∘₁ β.η z) ▷ F.Hom.η (g , f)) ∘ᵥ α⇒
                    ∘ᵥ (((((α⇐ ∘ᵥ (α.η z ▷ β.commutator.⇒.η g)) ∘ᵥ α⇒) ∘ᵥ (α.commutator.⇒.η g ◁ β.η y)) ∘ᵥ α⇐) ◁ F.₁.₀ f) ∘ᵥ α⇐
                    ∘ᵥ (H.₁.₀ g ▷ ((((α⇐ ∘ᵥ (α.η y ▷ β.commutator.⇒.η f)) ∘ᵥ α⇒) ∘ᵥ (α.commutator.⇒.η f ◁ β.η x)) ∘ᵥ α⇐)) ∘ᵥ α⇒
               ≈⟨ (refl⟩∘⟨ pushʳ (pushˡ (◁-resp-≈ (pushˡ assoc²αδ) ○ ⟺ ∘ᵥ-distr-◁) ○ (refl⟩∘⟨ (pushˡ (⟺ ∘ᵥ-distr-◁) ○ (refl⟩∘⟨ pushʳ (pushʳ (pushˡ (⟺ ∘ᵥ-distr-▷) ○ pushˡ (▷-resp-≈ assoc²αδ ○ ⟺  ∘ᵥ-distr-▷)))))))) ⟩
                    ((α.η z ∘₁ β.η z) ▷ F.Hom.η (g , f)) ∘ᵥ (α⇒ ∘ᵥ (α⇐ ◁ F.₁.₀ f))
                    ∘ᵥ ((((α.η z ▷ β.commutator.⇒.η g) ∘ᵥ α⇒) ∘ᵥ (α.commutator.⇒.η g ◁ β.η y)) ◁ F.₁.₀ f)
                    ∘ᵥ ((α⇐ ◁ F.₁.₀ f) ∘ᵥ α⇐ ∘ᵥ (H.₁.₀ g ▷ α⇐))
                    ∘ᵥ (H.₁.₀ g ▷ (((α.η y ▷ β.commutator.⇒.η f) ∘ᵥ α⇒) ∘ᵥ (α.commutator.⇒.η f ◁ β.η x)))
                    ∘ᵥ (H.₁.₀ g ▷ α⇐) ∘ᵥ α⇒
               ≈⟨ (⟺ ⊚.identity ⟩⊚⟨refl) ⟩∘⟨ ⟺  pentagon-conjugate₁ ⟩∘⟨ (⟺  ∘ᵥ-distr-◁ ○ pushˡ (⟺  ∘ᵥ-distr-◁))
                 ⟩∘⟨ pentagon-inv-var ⟩∘⟨ (⟺  ∘ᵥ-distr-▷ ○ pushˡ (⟺  ∘ᵥ-distr-▷))
                 ⟩∘⟨ (conjugate-from associator (H.₁.₀ g ▷ᵢ associator) (⟺  pentagon) ○ hom.assoc) ⟩
                    ((id₂ ∘ₕ id₂) ∘ₕ F.Hom.η (g , f))
                    ∘ᵥ (α⇐ ∘ᵥ (α.η z ▷ α⇒) ∘ᵥ α⇒)
                    ∘ᵥ (((α.η z ▷ β.commutator.⇒.η g) ◁ F.₁.₀ f) ∘ᵥ (α⇒ ◁ F.₁.₀ f) ∘ᵥ ((α.commutator.⇒.η g ◁ β.η y) ◁ F.₁.₀ f))
                    ∘ᵥ (α⇐ ∘ᵥ α⇐)
                    ∘ᵥ ((H.₁.₀ g ▷ (α.η y ▷ β.commutator.⇒.η f)) ∘ᵥ (H.₁.₀ g ▷ α⇒) ∘ᵥ (H.₁.₀ g ▷ (α.commutator.⇒.η f ◁ β.η x)))
                    ∘ᵥ α⇒ ∘ᵥ (α⇒ ◁ β.η x) ∘ᵥ α⇐
               ≈⟨ pushʳ (pullʳ (pullʳ (pushʳ (pullʳ (pullʳ (pushʳ (pullʳ (pushʳ (pullʳ (pullʳ hom.sym-assoc)))))))))) ⟩
                    (((id₂ ∘ₕ id₂) ∘ₕ F.Hom.η (g , f)) ∘ᵥ α⇐)
                    ∘ᵥ (α.η z ▷ α⇒)
                    ∘ᵥ (α⇒ ∘ᵥ ((α.η z ▷ β.commutator.⇒.η g) ◁ F.₁.₀ f))
                    ∘ᵥ (α⇒ ◁ F.₁.₀ f)
                    ∘ᵥ (((α.commutator.⇒.η g ◁ β.η y) ◁ F.₁.₀ f) ∘ᵥ α⇐)
                    ∘ᵥ (α⇐ ∘ᵥ (H.₁.₀ g ▷ (α.η y ▷ β.commutator.⇒.η f)))
                    ∘ᵥ (H.₁.₀ g ▷ α⇒)
                    ∘ᵥ ((H.₁.₀ g ▷ (α.commutator.⇒.η f ◁ β.η x)) ∘ᵥ α⇒)
                    ∘ᵥ (α⇒ ◁ β.η x) ∘ᵥ α⇐
               ≈⟨ ⟺ α⇐-⊚ ⟩∘⟨ refl⟩∘⟨ α⇒-⊚ ⟩∘⟨ refl⟩∘⟨ ⟺ α⇐-⊚ ⟩∘⟨ α⇐-⊚ ⟩∘⟨ refl⟩∘⟨ ⟺ α⇒-⊚ ⟩∘⟨refl ⟩
                    (α⇐ ∘ᵥ (α.η z ▷ β.η z ▷ F.Hom.η (g , f)))
                    ∘ᵥ (α.η z ▷ α⇒)
                    ∘ᵥ ((α.η z ▷ (β.commutator.⇒.η g ◁ F.₁.₀ f)) ∘ᵥ α⇒)
                    ∘ᵥ (α⇒ ◁ F.₁.₀ f)
                    ∘ᵥ (α⇐ ∘ᵥ (α.commutator.⇒.η g ∘ₕ (id₂ ∘ₕ id₂)))
                    ∘ᵥ (((id₂ ∘ₕ id₂) ∘ₕ β.commutator.⇒.η f) ∘ᵥ α⇐)
                    ∘ᵥ (H.₁.₀ g ▷ α⇒)
                    ∘ᵥ (α⇒ ∘ᵥ ((H.₁.₀ g ▷ α.commutator.⇒.η f) ◁ β.η x))
                    ∘ᵥ (α⇒ ◁ β.η x) ∘ᵥ α⇐
               ≈⟨ pullʳ (pushʳ (pushʳ (pullʳ (pushʳ (pushʳ (pullʳ (pushʳ (pullʳ (pushʳ (pushʳ (assoc²γδ))))))))))) ⟩
                    α⇐
                    ∘ᵥ ((α.η z ▷ β.η z ▷ F.Hom.η (g , f)) ∘ᵥ (α.η z ▷ α⇒) ∘ᵥ (α.η z ▷ (β.commutator.⇒.η g ◁ F.₁.₀ f)))
                    ∘ᵥ (α⇒ ∘ᵥ (α⇒ ◁ F.₁.₀ f) ∘ᵥ α⇐)
                    ∘ᵥ ((α.commutator.⇒.η g ∘ₕ (id₂ ∘ₕ id₂)) ∘ᵥ ((id₂ ∘ₕ id₂) ∘ₕ β.commutator.⇒.η f))
                    ∘ᵥ (α⇐ ∘ᵥ (H.₁.₀ g ▷ α⇒) ∘ᵥ α⇒)
                    ∘ᵥ (((H.₁.₀ g ▷ α.commutator.⇒.η f) ◁ β.η x) ∘ᵥ (α⇒ ◁ β.η x))
                    ∘ᵥ α⇐
               ≈⟨ refl⟩∘⟨ (hom.∘-resp-≈ʳ ∘ᵥ-distr-▷ ○ ∘ᵥ-distr-▷) ⟩∘⟨ (hom.sym-assoc ○ ⟺  (conjugate-from associator (α.η z ▷ᵢ associator) (⟺  pentagon)))
                      ⟩∘⟨ (hom.∘-resp-≈ (⊚-resp-≈ʳ ⊚.identity) (⊚-resp-≈ˡ ⊚.identity) ○ ⟺  ◁-▷-exchg ○ ⟺  (hom.∘-resp-≈ (⊚-resp-≈ˡ ⊚.identity) (⊚-resp-≈ʳ ⊚.identity)))
                      ⟩∘⟨ ⟺  pentagon-conjugate₄ ⟩∘⟨ ∘ᵥ-distr-◁ ⟩∘⟨refl ⟩ 
                    α⇐
                    ∘ᵥ (α.η z ▷ ((β.η z ▷ F.Hom.η (g , f)) ∘ᵥ α⇒ ∘ᵥ (β.commutator.⇒.η g ◁ F.₁.₀ f)))
                    ∘ᵥ ((α.η z ▷ α⇐) ∘ᵥ α⇒)
                    ∘ᵥ (((id₂ ∘ₕ id₂) ∘ₕ β.commutator.⇒.η f) ∘ᵥ (α.commutator.⇒.η g ∘ₕ (id₂ ∘ₕ id₂)))
                    ∘ᵥ (α⇒ ∘ᵥ (α⇐ ◁ β.η x))
                    ∘ᵥ (((H.₁.₀ g ▷ α.commutator.⇒.η f) ∘ᵥ α⇒) ◁ β.η x)
                    ∘ᵥ α⇐
               ≈⟨ refl⟩∘⟨ pushʳ (pullʳ (pushʳ (pullʳ (pushʳ assoc²γδ)))) ⟩ 
                    α⇐
                    ∘ᵥ ((α.η z ▷ ((β.η z ▷ F.Hom.η (g , f)) ∘ᵥ α⇒ ∘ᵥ (β.commutator.⇒.η g ◁ F.₁.₀ f))) ∘ᵥ (α.η z ▷ α⇐))
                    ∘ᵥ (α⇒ ∘ᵥ ((id₂ ∘ₕ id₂) ∘ₕ β.commutator.⇒.η f))
                    ∘ᵥ ((α.commutator.⇒.η g ∘ₕ (id₂ ∘ₕ id₂)) ∘ᵥ α⇒)
                    ∘ᵥ ((α⇐ ◁ β.η x) ∘ᵥ (((H.₁.₀ g ▷ α.commutator.⇒.η f) ∘ᵥ α⇒) ◁ β.η x))
                    ∘ᵥ α⇐
               ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩∘⟨ α⇒-⊚ ⟩∘⟨ ⟺  α⇒-⊚ ⟩∘⟨ ∘ᵥ-distr-◁ ⟩∘⟨refl ⟩ 
                    α⇐
                    ∘ᵥ (α.η z ▷ (((β.η z ▷ F.Hom.η (g , f)) ∘ᵥ α⇒ ∘ᵥ (β.commutator.⇒.η g ◁ F.₁.₀ f)) ∘ᵥ α⇐))
                    ∘ᵥ ((α.η z ▷ G.₁.₀ g ▷ β.commutator.⇒.η f) ∘ᵥ α⇒)
                    ∘ᵥ (α⇒ ∘ᵥ (α.commutator.⇒.η g ◁ G.₁.₀ f ◁ β.η x))
                    ∘ᵥ ((α⇐ ∘ᵥ (H.₁.₀ g ▷ α.commutator.⇒.η f) ∘ᵥ α⇒) ◁ β.η x)
                    ∘ᵥ α⇐
               ≈⟨ refl⟩∘⟨ pushʳ (pullʳ (pushʳ assoc²γδ)) ⟩
                    α⇐
                    ∘ᵥ ((α.η z ▷ (((β.η z ▷ F.Hom.η (g , f)) ∘ᵥ α⇒ ∘ᵥ (β.commutator.⇒.η g ◁ F.₁.₀ f)) ∘ᵥ α⇐)) ∘ᵥ (α.η z ▷ G.₁.₀ g ▷ β.commutator.⇒.η f))
                    ∘ᵥ (α⇒ ∘ᵥ α⇒)
                    ∘ᵥ ((α.commutator.⇒.η g ◁ G.₁.₀ f ◁ β.η x) ∘ᵥ ((α⇐ ∘ᵥ (H.₁.₀ g ▷ α.commutator.⇒.η f) ∘ᵥ α⇒) ◁ β.η x))
                    ∘ᵥ α⇐
               ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩∘⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩∘⟨refl ⟩
                    α⇐
                    ∘ᵥ (α.η z ▷ ((((β.η z ▷ F.Hom.η (g , f)) ∘ᵥ α⇒ ∘ᵥ (β.commutator.⇒.η g ◁ F.₁.₀ f)) ∘ᵥ α⇐) ∘ᵥ (G.₁.₀ g ▷ β.commutator.⇒.η f)))
                    ∘ᵥ (α⇒ ∘ᵥ α⇒)
                    ∘ᵥ (((α.commutator.⇒.η g ◁ G.₁.₀ f) ∘ᵥ α⇐ ∘ᵥ (H.₁.₀ g ▷ α.commutator.⇒.η f) ∘ᵥ α⇒) ◁ β.η x)
                    ∘ᵥ α⇐
               ≈⟨ refl⟩∘⟨ pushʳ (pushˡ (⟺  pentagon)) ⟩
                    α⇐
                    ∘ᵥ ((α.η z ▷ ((((β.η z ▷ F.Hom.η (g , f)) ∘ᵥ α⇒ ∘ᵥ (β.commutator.⇒.η g ◁ F.₁.₀ f)) ∘ᵥ α⇐) ∘ᵥ (G.₁.₀ g ▷ β.commutator.⇒.η f))) ∘ᵥ (α.η z ▷ α⇒))
                    ∘ᵥ (α⇒ ∘ᵥ (α⇒ ◁ β.η x))
                    ∘ᵥ (((α.commutator.⇒.η g ◁ G.₁.₀ f) ∘ᵥ α⇐ ∘ᵥ (H.₁.₀ g ▷ α.commutator.⇒.η f) ∘ᵥ α⇒) ◁ β.η x)
                    ∘ᵥ α⇐
               ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩∘⟨ pullʳ (pullˡ ∘ᵥ-distr-◁) ⟩
                    α⇐
                    ∘ᵥ (α.η z ▷ (((((β.η z ▷ F.Hom.η (g , f)) ∘ᵥ α⇒ ∘ᵥ (β.commutator.⇒.η g ◁ F.₁.₀ f)) ∘ᵥ α⇐) ∘ᵥ (G.₁.₀ g ▷ β.commutator.⇒.η f)) ∘ᵥ α⇒))
                    ∘ᵥ α⇒
                    ∘ᵥ ((α⇒ ∘ᵥ (α.commutator.⇒.η g ◁ G.₁.₀ f) ∘ᵥ α⇐ ∘ᵥ (H.₁.₀ g ▷ α.commutator.⇒.η f) ∘ᵥ α⇒) ◁ β.η x)
                    ∘ᵥ α⇐
               ≈⟨ refl⟩∘⟨ ▷-resp-≈ (assoc²αε ○ assoc²βε ○ β.associativity {f = f}{g}) ⟩∘⟨refl ⟩
                    α⇐
                    ∘ᵥ (α.η z ▷ (β.commutator.⇒.η (g C.∘₁ f) ∘ᵥ (G.Hom.η (g , f) ◁ β.η x)))
                    ∘ᵥ α⇒
                    ∘ᵥ ((α⇒ ∘ᵥ (α.commutator.⇒.η g ◁ G.₁.₀ f) ∘ᵥ α⇐ ∘ᵥ (H.₁.₀ g ▷ α.commutator.⇒.η f) ∘ᵥ α⇒) ◁ β.η x)
                    ∘ᵥ α⇐
               ≈⟨ pushʳ (pushˡ (⟺  ∘ᵥ-distr-▷)) ⟩
                    (α⇐ ∘ᵥ (α.η z ▷ β.commutator.⇒.η (g C.∘₁ f)))
                    ∘ᵥ (α.η z ▷ (G.Hom.η (g , f) ◁ β.η x))
                    ∘ᵥ α⇒
                    ∘ᵥ ((α⇒ ∘ᵥ (α.commutator.⇒.η g ◁ G.₁.₀ f) ∘ᵥ α⇐ ∘ᵥ (H.₁.₀ g ▷ α.commutator.⇒.η f) ∘ᵥ α⇒) ◁ β.η x)
                    ∘ᵥ α⇐
               ≈⟨ pushʳ (extendʳ (⟺  α⇒-⊚)) ⟩
                    ((α⇐ ∘ᵥ (α.η z ▷ β.commutator.⇒.η (g C.∘₁ f))) ∘ᵥ α⇒)
                    ∘ᵥ ((α.η z ▷ G.Hom.η (g , f)) ◁ β.η x)
                    ∘ᵥ ((α⇒ ∘ᵥ (α.commutator.⇒.η g ◁ G.₁.₀ f) ∘ᵥ α⇐ ∘ᵥ (H.₁.₀ g ▷ α.commutator.⇒.η f) ∘ᵥ α⇒) ◁ β.η x)
                    ∘ᵥ α⇐
               ≈⟨ refl⟩∘⟨ pullˡ ∘ᵥ-distr-◁ ⟩
                    ((α⇐ ∘ᵥ (α.η z ▷ β.commutator.⇒.η (g C.∘₁ f))) ∘ᵥ α⇒)
                    ∘ᵥ (((α.η z ▷ G.Hom.η (g , f)) ∘ᵥ α⇒ ∘ᵥ (α.commutator.⇒.η g ◁ G.₁.₀ f) ∘ᵥ α⇐ ∘ᵥ (H.₁.₀ g ▷ α.commutator.⇒.η f) ∘ᵥ α⇒) ◁ β.η x)
                    ∘ᵥ α⇐
               ≈⟨ refl⟩∘⟨ ◁-resp-≈ (α.associativity {f = f}{g}) ⟩∘⟨refl ⟩
                    ((α⇐ ∘ᵥ (α.η z ▷ β.commutator.⇒.η (g C.∘₁ f))) ∘ᵥ α⇒)
                    ∘ᵥ ((α.commutator.⇒.η (g C.∘₁ f) ∘ᵥ (H.Hom.η (g , f) ◁ α.η x)) ◁ β.η x)
                    ∘ᵥ α⇐
               ≈⟨ pushʳ (pushˡ (⟺  ∘ᵥ-distr-◁)) ⟩
                    (((α⇐ ∘ᵥ (α.η z ▷ β.commutator.⇒.η (g C.∘₁ f))) ∘ᵥ α⇒) ∘ᵥ (α.commutator.⇒.η (g C.∘₁ f) ◁ β.η x))
                    ∘ᵥ ((H.Hom.η (g , f) ◁ α.η x) ◁ β.η x) ∘ᵥ α⇐
               ≈⟨ pushʳ (hom.Equiv.trans (⟺  α⇐-⊚) (hom.∘-resp-≈ʳ (refl⟩⊚⟨ ⊚.identity))) ⟩
                    ((((α⇐ ∘ᵥ (α.η z ▷ β.commutator.⇒.η (g C.∘₁ f))) ∘ᵥ α⇒) ∘ᵥ (α.commutator.⇒.η (g C.∘₁ f) ◁ β.η x)) ∘ᵥ α⇐)
                     ∘ᵥ (H.Hom.η (g , f) ◁ (α.η x ∘₁ β.η x)) ∎
  
