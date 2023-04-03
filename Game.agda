{-# OPTIONS --type-in-type #-}
module Game where

open import Data.Unit
open import Data.Product
open import Function

open import ParaLens renaming (ParaLens to Arena)
open import Lenses

{-
is-maximal : {X : Set} → (_≤_ : X → X → Set) → X → Set
is-maximal {X} _≤_ x = (x' : X) → x' ≤ x
-}

is-argmax : {X Y : Set} → (_≤_ : Y → Y → Set) → (X → Y) → X → Set
is-argmax {X} _≤_ f x = (x' : X) → f x' ≤ f x

Pow : Set → Set₁
Pow X = X → Set

_∈_ : {X : Set} → X → Pow X → Set
x ∈ U = U x

fixed-points : {Ω : Set} → (Ω → Pow Ω) → Pow Ω
fixed-points f ω = ω ∈ f ω

ΠL : {ψ ψ' : Set} → Lens (ψ × ψ') (ψ × ψ' → Set) (ψ × ψ') ((ψ → Set) × (ψ' → Set))
view ΠL = id
update ΠL _ (P , Q) (x , y) = P x × Q y


Players : (Ω P : Set) → Set₁
Players Ω P = Σ[ Ω' ∈ Set ] (Lens Ω' (Ω' → Set) Ω (Ω → P))

Players-map : {Ω P Ω' P' : Set} → Lens Ω P Ω' P' → Players Ω P → Players Ω' P'
Players-map L (Ω'' , G) = (Ω'' , (G ；L (L *)))

Players-lax : {Ω P Ω' P' : Set} → Players Ω P × Players Ω' P' → Players (Ω × Ω') (P × P')
Players-lax ((ψ , G) , (ψ' , G')) = ((ψ × ψ') , (ΠL ；L ((G ⊠ G') ；L Nashator) ))

Game : (X S Y R : Set)(Ω P : Set) → Set₁
Game X S Y R Ω P = Arena Ω P X S Y R × Players Ω P

compGame : {X S Y R Ω P Y' R' Ω' P' : Set} → Game X S Y R Ω P → Game Y R Y' R' Ω' P' → Game X S Y' R' (Ω × Ω') (P × P')
compGame (A₁ , P₁) (A₂ , P₂) = (A₁ ; A₂) , Players-lax (P₁ , P₂)

state : {X S : Set} → X → Lens ⊤ ⊤ X S
view (state x) = λ _ → x
update (state x) = λ _ s → tt

costate : {Y R : Set} → (Y → R) → Lens Y R ⊤ ⊤
view (costate f) = λ y → tt
update (costate f) = λ y _ → f y

equilibria : ∀ {X S Y R Ω P} → Game X S Y R Ω P → X → (Y → R) → Ω → Set
equilibria (A , (Ω₀ , P)) x u = fixed-points λ ω → {!(state x L; A) ;L costate u!}
