{-# OPTIONS --without-K #-}
open import Algebra.Group
open import Algebra.Group.Homomorphism
open import Data.Zero
open import Data.One
open import Data.Bool.Base using (true; false) renaming (T to ✓)
open import FFI.JS.BigI
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.Base
open import Relation.Nullary
open import Type using (Type)
open import Type.Eq
open import ZK.GroupHom.NumChal

module ZK.GroupHom.JSChal
  (q : BigI)
  {G+ G* : Type}
  (𝔾+ : Group G+)
  (𝔾* : Group G*)
  {{eq?-G* : Eq? G*}}
  (_⊗ⁿ_ : G+ → BigI → G+)
  (_^ⁿ_ : G* → BigI → G*)
  (φ : G+ → G*)
  (φ-hom : GroupHomomorphism 𝔾+ 𝔾* φ)
  (Y : G*)

  where

infixl 6 _+ⁿ_ _∸ⁿ_
infixl 7 _*ⁿ_

module 𝔾+ = Group 𝔾+
open module 𝔾* = Multiplicative-Group 𝔾*

postulate BigIPrime : BigI → Type

0ⁿ   = 0I
1ⁿ   = 1I
_+ⁿ_ = add
_∸ⁿ_ = subtract
_*ⁿ_ = multiply

_<BigI_ : (x y : BigI) → Type
x <BigI y = ✓ (x <I y)

_div-q _mod-q inv-mod-q : BigI → BigI
x div-q     = divide x q
x mod-q     = mod x q
inv-mod-q x = modInv x q

-- TODO: should be turned into a dynamic test!
postulate q-prime : BigIPrime q

-- TODO: should be turned into a dynamic test!
postulate G*-order : Y ^ⁿ q ≡ 𝔾*.1#

-- We can hope to reduce these two more basic facts
postulate 1^ⁿ : ∀ x → 𝔾*.1# ^ⁿ x ≡ 𝔾*.1#
postulate φ-hom-iterated : ∀ {x c} → φ (x ⊗ⁿ c) ≡ φ x ^ⁿ c

{-
post--ulate IMPOSSIBLE : (A : Set) → ¬ A

¬Tri𝟙A𝟙 : ∀ {A : Set} → ¬ Tri 𝟙 A 𝟙
¬Tri𝟙A𝟙 (tri< a ¬b ¬c) = ¬c 0₁
¬Tri𝟙A𝟙 (tri≈ ¬a b ¬c) = ¬c 0₁
¬Tri𝟙A𝟙 (tri> ¬a ¬b c) = ¬a 0₁

compare : Trichotomous _≡_ _<BigI_
compare x y with x <I y | y <I x
... | true  | false = tri< _ (IMPOSSIBLE (x ≡ y)) (λ())
... | false | true  = tri> (λ()) (IMPOSSIBLE (x ≡ y)) _
... | false | false = tri≈ (λ()) {!!} (λ())
... | true  | true  = {!!}
-}

postulate compare : Trichotomous _≡_ _<BigI_

postulate <-∸≢0 : ∀ x y → y <BigI x → x ∸ⁿ y ≢ 0ⁿ
postulate div-mod-q-propⁿ : ∀ d → d ≡ d mod-q +ⁿ (d div-q) *ⁿ q
postulate inv-mod-q-prop : ∀ x → x ≢ 0ⁿ → (inv-mod-q x *ⁿ x)mod-q ≡ 1ⁿ
postulate ^ⁿ1ⁿ+ⁿ : ∀ {x} → Y ^ⁿ(1ⁿ +ⁿ x) ≡ Y * Y ^ⁿ x
postulate ^ⁿ-* : ∀ {x y} → Y ^ⁿ(y *ⁿ x) ≡ (Y ^ⁿ x)^ⁿ y
postulate ^ⁿ-∸ⁿ : ∀ {c₀ c₁}(c> : ✓ (c₁ <I c₀)) → Y ^ⁿ(c₀ ∸ⁿ c₁) ≡ (Y ^ⁿ c₀) / (Y ^ⁿ c₁)

JSPackage : Package
JSPackage = record
              { Num = BigI
              ; Prime = BigIPrime
              ; _<_ = _<BigI_
              ; 0ⁿ = 0ⁿ
              ; 1ⁿ = 1ⁿ
              ; _+ⁿ_ = _+ⁿ_
              ; _∸ⁿ_ = _∸ⁿ_
              ; _*ⁿ_ = _*ⁿ_
              ; compare = compare
              ; <-∸≢0 = <-∸≢0
              ; G+ = G+
              ; G* = G*
              ; 𝔾+ = 𝔾+
              ; 𝔾* = 𝔾*
              ; _⊗ⁿ_ = _⊗ⁿ_
              ; _^ⁿ_ = _^ⁿ_
              ; 1^ⁿ = 1^ⁿ
              ; φ = φ
              ; φ-hom = φ-hom
              ; φ-hom-iterated = φ-hom-iterated
              ; q = q
              ; q-prime = q-prime
              ; _div-q = _div-q
              ; _mod-q = _mod-q
              ; div-mod-q-propⁿ = div-mod-q-propⁿ
              ; inv-mod-q = inv-mod-q
              ; inv-mod-q-prop = inv-mod-q-prop
              ; Y = Y
              ; G*-order = G*-order
              ; ^ⁿ1ⁿ+ⁿ = ^ⁿ1ⁿ+ⁿ
              ; ^ⁿ-* = ^ⁿ-*
              ; ^ⁿ-∸ⁿ = ^ⁿ-∸ⁿ
              }

open FromPackage JSPackage public
-- -}
-- -}
-- -}
