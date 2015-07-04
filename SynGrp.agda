{-# OPTIONS --without-K #-}
open import Type.Eq
open import Function.Base
open import Data.Product.NP renaming (map to <_×_>)
open import FFI.JS.BigI
open import Crypto.JS.BigI.CyclicGroup
open import Crypto.JS.BigI.FiniteField
  hiding (_*_; _^I_)
open import Algebra.Group
open import Algebra.Group.Constructions
open import Algebra.Group.Homomorphism
open import Relation.Binary.PropositionalEquality

module SynGrp where

data SynGrp : Set where
  `ℤ[_]+ : (q : BigI) → SynGrp
  `ℤ[_]★ : (p : BigI) → SynGrp
  _`×_  : (𝔸 𝔹 : SynGrp) → SynGrp

ElGrp : SynGrp → Set
ElGrp `ℤ[ q ]+ = ℤ[ q ]
ElGrp `ℤ[ p ]★ = ℤ[ p ]★
ElGrp (`𝔸 `× `𝔹) = ElGrp `𝔸 × ElGrp `𝔹

El𝔾rp : ∀ `𝔾 → Group (ElGrp `𝔾)
El𝔾rp `ℤ[ q ]+ = ℤ[ q ]+-grp
El𝔾rp `ℤ[ p ]★ = ℤ[ p ]★-grp
El𝔾rp (`𝔸 `× `𝔹) = Product.×-grp (El𝔾rp `𝔸) (El𝔾rp `𝔹)

exp-× : ∀ {a b c}{A : Set a}{B : Set b}{C : Set c}
          (expA : A → C → A)
          (expB : B → C → B)
        → A × B → C → A × B
exp-× expA expB (b0 , b1) e = expA b0 e , expB b1 e

-- This iterate the group operation of 𝔸 based on the given
-- BigI value. Calling this operations exp(onential) makes
-- sense when the group is ℤp★, but for ℤq+ this corresponds
-- to multiplication.
expI : ∀ 𝔸 → ElGrp 𝔸 → BigI → ElGrp 𝔸
expI `ℤ[ q ]+  = _⊗I_ _
expI `ℤ[ p ]★  = _^I_ _
expI (𝔸 `× 𝔹) = exp-× (expI 𝔸) (expI 𝔹)

-- See the remark on expI
exp : ∀ {q} 𝔸 → ElGrp 𝔸 → ℤ[ q ] → ElGrp 𝔸
exp 𝔸 b e = expI 𝔸 b (ℤq▹BigI _ e)

module _ {q q'} where

  _*_ : ℤ[ q ] → ℤ[ q' ] → ℤ[ q ]
  x * y = _⊗I_ _ x (ℤq▹BigI _ y)

  -- TODO check on the assumptions on q,q'
  -- x * (y +{q'} z) = x * y +{q} x * z
  -- mod (x * (mod (y + z) q')) q = ((x * y) mod q + (x * z) mod q) mod q
  postulate *-hom : ∀ x → GroupHomomorphism ℤ[ q' ]+-grp ℤ[ q ]+-grp (_*_ x)

open module ^-hom-p-q {p q} = ^-hom p {q}

exp-hom : ∀ {q} 𝔸 (b : ElGrp 𝔸)
           → GroupHomomorphism ℤ[ q ]+-grp (El𝔾rp 𝔸) (exp 𝔸 b)
exp-hom `ℤ[ q ]+ b = *-hom b
exp-hom `ℤ[ p ]★ b = ^-hom b
exp-hom (𝔸 `× 𝔹) (b0 , b1) = < exp-hom 𝔸 b0 , exp-hom 𝔹 b1 >-hom

data SynHom : (𝔸 𝔹 : SynGrp) → Set where
  `id  : ∀{𝔸} → SynHom 𝔸 𝔸 
  _`∘_ : ∀{𝔸 𝔹 ℂ}(f : SynHom 𝔹 ℂ)(g : SynHom 𝔸 𝔹) → SynHom 𝔸 ℂ
  `<_×_> : ∀{𝔸₀ 𝔸₁ 𝔹₀ 𝔹₁}
            (f₀ : SynHom 𝔸₀ 𝔹₀)(f₁ : SynHom 𝔸₁ 𝔹₁)
           → SynHom (𝔸₀ `× 𝔸₁) (𝔹₀ `× 𝔹₁)
  `Δ : ∀{𝔸} → SynHom 𝔸 (𝔸 `× 𝔸) 
  _`^_ : ∀ {q 𝔸} → ElGrp 𝔸 → SynHom `ℤ[ q ]+ 𝔸

`<_,_> : ∀{𝔸 𝔹₀ 𝔹₁}
          (f₀ : SynHom 𝔸 𝔹₀)
          (f₁ : SynHom 𝔸 𝔹₁)
         → SynHom 𝔸 (𝔹₀ `× 𝔹₁)
`< f₀ , f₁ > = `< f₀ × f₁ > `∘ `Δ

ElHom : ∀{𝔸 𝔹 : SynGrp} → SynHom 𝔸 𝔹 → ElGrp 𝔸 → ElGrp 𝔹
ElHom `id        = id
ElHom (f `∘ g)   = ElHom f ∘ ElHom g
ElHom `< f × g > = < ElHom f × ElHom g >
ElHom `Δ         = Δ
ElHom (_`^_ {𝔸 = 𝔸} b) = exp 𝔸 b

Elℍom : ∀{𝔸 𝔹 : SynGrp}(φ : SynHom 𝔸 𝔹) → GroupHomomorphism (El𝔾rp 𝔸) (El𝔾rp 𝔹) (ElHom φ)
Elℍom `id = Identity.id-hom _
Elℍom (φ `∘ ψ) = Elℍom φ ∘-hom Elℍom ψ
Elℍom `< φ × ψ > = < Elℍom φ × Elℍom ψ >-hom
Elℍom `Δ = Delta.Δ-hom _
Elℍom (_`^_ {𝔸 = 𝔸} x) = exp-hom 𝔸 x

SynGrp-Eq? : (𝔸 : SynGrp) → Eq? (ElGrp 𝔸)
SynGrp-Eq? `ℤ[ q ]+ = ℤ[ q ]-Eq?
SynGrp-Eq? `ℤ[ p ]★ = ℤ[ p ]★-Eq?
SynGrp-Eq? (𝔸 `× 𝔹) = ×-Eq? {{SynGrp-Eq? 𝔸}} {{SynGrp-Eq? 𝔹}}

-- -}
-- -}
-- -}
-- -}
-- -}
