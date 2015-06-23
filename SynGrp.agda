{-# OPTIONS --without-K #-}
open import Type.Eq
open import Function.NP
open import Data.Product.NP renaming (map to <_×_>)
open import FFI.JS.BigI
import      Crypto.JS.BigI.CyclicGroup as 𝔾
import      Crypto.JS.BigI.FiniteField as 𝔽
open import Algebra.Group
open import Algebra.Group.Constructions
open import Algebra.Group.Homomorphism
-- open import Relation.Binary.PropositionalEquality

module SynGrp where

data SynGrp : Set where
  `ℤ[_]+ : (q : BigI) → SynGrp
  `ℤ[_]★ : (p : BigI) → SynGrp
  _`×_  : (𝔸 𝔹 : SynGrp) → SynGrp

ℤ[_]  = 𝔽.𝔽
ℤ[_]★ = 𝔾.𝔾

ℤ[_]+-grp = 𝔽.fld.+-grp
ℤ[_]★-grp = 𝔾.grp

ElGrp : SynGrp → Set
ElGrp `ℤ[ q ]+ = ℤ[ q ]
ElGrp `ℤ[ p ]★ = ℤ[ p ]★
ElGrp (`𝔸 `× `𝔹) = ElGrp `𝔸 × ElGrp `𝔹

El𝔾rp : ∀ `𝔾 → Group (ElGrp `𝔾)
El𝔾rp `ℤ[ q ]+ = ℤ[ q ]+-grp
El𝔾rp `ℤ[ p ]★ = ℤ[ p ]★-grp
El𝔾rp (`𝔸 `× `𝔹) = Product.×-grp (El𝔾rp `𝔸) (El𝔾rp `𝔹)

-- This iterate the group operation of 𝔸 based on the given
-- BigI value. Calling this operations exp(onential) makes
-- sense when the group is ℤp★, but for ℤq+ this corresponds
-- to multiplication.
expI : ∀ 𝔸 → ElGrp 𝔸 → BigI → ElGrp 𝔸
expI `ℤ[ q ]+ b e = 𝔽._⊗_ _ b e
expI `ℤ[ p ]★ b e = 𝔾._^_ _ b e
expI (𝔸 `× 𝔹) (b0 , b1) e = expI 𝔸 b0 e , expI 𝔹 b1 e

-- See the remark on expI
exp : ∀ {q} 𝔸 → ElGrp 𝔸 → ℤ[ q ] → ElGrp 𝔸
exp 𝔸 b e = expI 𝔸 b (𝔽.repr _ e)

module _ {q q'} where

  _*_ : ℤ[ q ] → ℤ[ q' ] → ℤ[ q ]
  x * y = 𝔽._⊗_ _ x (𝔽.repr _ y)

  -- TODO check on the assumptions on q,q'
  postulate
    *-hom : ∀ x → GroupHomomorphism ℤ[ q' ]+-grp ℤ[ q ]+-grp (_*_ x)

module _ {q p} where
  _^_ : ℤ[ p ]★ → ℤ[ q ] → ℤ[ p ]★
  b ^ e = 𝔾._^_ _ b (𝔽.repr _ e)

  -- TODO check on the assumptions on p,q
  postulate
    ^-hom : ∀ b → GroupHomomorphism ℤ[ q ]+-grp ℤ[ p ]★-grp (_^_ b)

    -- ^-comm : ∀ {α x y} → (α ^ x)^ y ≡ (α ^ y)^ x

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
SynGrp-Eq? `ℤ[ q ]+ = 𝔽.𝔽-Eq? q
SynGrp-Eq? `ℤ[ p ]★ = 𝔾.𝔾-Eq? p
SynGrp-Eq? (𝔸 `× 𝔹) = ×-Eq? {{SynGrp-Eq? 𝔸}} {{SynGrp-Eq? 𝔹}}

-- -}
-- -}
-- -}
-- -}
-- -}
