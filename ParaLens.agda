module ParaLens where

open import Data.Product
open import Data.Unit

open import Relation.Binary.PropositionalEquality

open import Lenses

record ParaLens (D O X S Y R : Set) : Set₁ where
  field
    play   : D → X → Y
    coplay : D → X → R → O × S

open ParaLens

fromLens : {X S Y R : Set} → Lens X S Y R → ParaLens ⊤ ⊤ X S Y R
play (fromLens L) _ = view L
coplay (fromLens L) _ x r = _ , update L x r

toLens : {D O X S Y R : Set} → ParaLens D O X S Y R → Lens (D × X) (O × S) Y R
view (toLens P) = uncurry (play P)
update (toLens P) = uncurry (coplay P)

toPara : {D O X S Y R : Set} → Lens (D × X) (O × S) Y R → ParaLens D O X S Y R
play (toPara L) = curry (view L)
coplay (toPara L) = curry (update L)

rewire : {D' O' D O X S Y R : Set}
         → Lens D' O' D O
         → ParaLens D  O  X S Y R
         → ParaLens D' O' X S Y R
play   (rewire ρ a) d' x   = play a (view ρ d') x
coplay (rewire ρ a) d' x r = map₁ (update ρ d') (coplay a (view ρ d') x r)

_*_ : {P Q : Set} →
      (f : P → Q) →
      (D : P → Set) → (Q → Set)
(f * D) q = ∀ p → f p ≡ q → D p


regroup : {P Q : Set} →
          (D O : P → Set){X S Y R : Set} →
          (f : P → Q) →
          ParaLens ((p : P) → D p) ((p : P) → O p) X S Y R →
          ParaLens ((q : Q) → (f * D) q) ((q : Q) → (f * O) q) X S Y R
regroup {P} {Q} D O f A = rewire w A where
  w : Lens ((q : Q) → (f * D) q) ((q : Q) → (f * O) q)
           ((p : P) → D p) ((p : P) → O p)
  view w d p = d (f p) p refl
  update w _ o .(f p) p refl = o p


_;_ : {D O X S Y R D' O' Z T : Set}
       → ParaLens D O X S Y R
       → ParaLens D' O' Y R Z T
       → ParaLens (D × D') (O × O') X S Z T
play   (ℓ ; m) (d , d') x   =
  play m d' (play ℓ d x)
coplay (ℓ ; m) (d , d') x t =
  let
    (o' , r) = coplay m d' (play ℓ d x) t
    (o  , s) = coplay ℓ d x r
  in
    ((o , o') , s)

_L;_ : {X S Y R D' O' Z T : Set}
     → Lens X S Y R
     → ParaLens D' O' Y R Z T
     → ParaLens D' O' X S Z T
L L; A = rewire removeTrivial (fromLens L ; A) where
  removeTrivial : Lens _ _ (⊤ × _) (⊤ × _)
  view removeTrivial d' = _ , d'
  update removeTrivial d' (_ , o') = o'

_;L_ : {X S Y R D' O' Z T : Set}
     → ParaLens D' O' X S Y R
     → Lens Y R Z T
     → ParaLens D' O' X S Z T
A ;L L = rewire removeTrivial (A ; fromLens L) where
  removeTrivial : Lens _ _ (_ × ⊤) (_ × ⊤)
  view removeTrivial d' = d' , _
  update removeTrivial d' (o' , _ ) = o'



_⊗_ : {D O X S Y R D' O' X' S' Y' R' : Set}
       → ParaLens D O X S Y R
       → ParaLens D' O' X' S' Y' R'
       → ParaLens (D × D') (O × O') (X × X') (S × S') (Y × Y') (R × R')
play (ℓ ⊗ m) (d , d') (x , x') =
  (play ℓ d x , play m d' x')
coplay (ℓ ⊗ m) (d , d') (x , x') (r , r') =
  let
    (o  , s ) = coplay ℓ d  x  r
    (o' , s') = coplay m d' x' r'
  in
    ((o , o') , (s , s'))

& : {I : Set}
  → {D O X Y S : I → Set} {R : Set}
  → ((i : I) → ParaLens (D i) (O i) (X i) (S i) (Y i) R)
  → ParaLens ((i : I) → D i) (Σ I O) (Σ I X) (Σ I S) (Σ I Y) R
play (& A) ϕ (i , x) =  (i , play (A i) (ϕ i) x)
coplay (& A) ϕ (i , x) r =
  let (o , s) = coplay (A i) (ϕ i) x r in (i , o) , (i , s)

⊕ : {I : Set}
  → {D O X Y S : I → Set} {R : Set}
  → ((i : I) → ParaLens (D i) (O i) (X i) (S i) (Y i) R)
  → ParaLens (Σ I D) (Σ I O) ((i : I) → X i) (Σ I S) (Σ I Y) R
play (⊕ A) (i , d) x = (i , play (A i) d (x i))
coplay (⊕ A) (i , d) x r =
  let (o , s) = coplay (A i) d (x i) r in (i , o) , (i , s)

decisison : (M R : Set) → ParaLens M R ⊤ R M R
play (decisison M R) m _ = m
coplay (decisison M R) m _ r = r , r

Para* : {D O X S Y R : Set} →
        ParaLens D O X S Y R →
        ParaLens D (D → O) X (X → S) Y (Y → R)
Para* P = toPara (Nashator ；L ((toLens P) *))
