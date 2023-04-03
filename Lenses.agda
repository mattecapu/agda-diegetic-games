module Lenses where

open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Function

_；_ : {X Y Z : Set} → (X → Y) → (Y → Z) → (X → Z)
f ； g = λ x → g (f x)

record Lens (X S Y R : Set) : Set₁ where
  field
    view   : X → Y
    update : X → R → S

open Lens public

_；L_ : {X S Y R Z T : Set}
      → Lens X S Y R
      → Lens Y R Z T
      → Lens X S Z T
view (ℓ ；L m) = view ℓ ； view m
update (ℓ ；L m) = λ x t → update ℓ x (update m (view ℓ x) t)

_⊠_ : {X S Y R X' S' Y' R' : Set}
      → Lens X S Y R
      → Lens X' S' Y' R'
      → Lens (X × X') (S × S') (Y × Y') (R × R')
view (ℓ ⊠ m) = λ { (x , x') → (view ℓ x , view m x') }
update (ℓ ⊠ m) = λ { (x , x') (r , r') → (update ℓ x r , update m x' r') }

_* : {X S Y R : Set} →
     Lens X S Y R →
     Lens X (X → S) Y (Y → R)
view (L *) = view L
update (L *) _ f x = update L x (f (view L x))

Nashator : {X S Y R : Set} →
           Lens (X × Y) ((X → S) × (Y → R)) (X × Y) ((X × Y) → (S × R))
view Nashator = id
update Nashator (x⁻ , y⁻) u = (λ x → fst (u (x , y⁻))) , (λ y → snd (u (x⁻ , y)))
