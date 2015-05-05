{-# OPTIONS --without-K #-}
open import Type using (Type; Type₁)
open import Type.Eq
open import Function using (flip)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum.NP
open import Data.Zero
open import Data.Fin.NP using (Fin▹ℕ)
open import Data.Bool.Base using (Bool) renaming (T to ✓)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.NP using (_≡_; _≢_; idp; ap; ap₂; !_; _∙_; module ≡-Reasoning)
open import Algebra.Group
open import Algebra.Group.Homomorphism
import Data.Nat.ModInv
import ZK.SigmaProtocol.KnownStatement
import ZK.GroupHom

module ZK.GroupHom.NumChal where

record Package : Type₁ where
  infixl 6 _+ⁿ_ _∸ⁿ_
  infixl 7 _*ⁿ_
  field
    Num : Type
    Prime : Num → Type
    _<_ : (x y : Num) → Type
    0ⁿ  : Num
    1ⁿ  : Num
    _+ⁿ_ : (x y : Num) → Num
    _∸ⁿ_ : (x y : Num) → Num
    _*ⁿ_ : (x y : Num) → Num
    compare : Trichotomous _≡_ _<_
    <-∸≢0 : ∀ x y → y < x → x ∸ⁿ y ≢ 0ⁿ

    G+ G* : Type
    𝔾+ : Group G+
    𝔾* : Group G*

  _>_ : (x y : Num) → Type
  _>_ = flip _<_

  open Additive-Group 𝔾+ public
  open Multiplicative-Group 𝔾* public

  field
    {{eq?-G*}} : Eq? G*

    _⊗ⁿ_ : G+ → Num → G+
    _^ⁿ_ : G* → Num → G*
    1^ⁿ : ∀ x → 1# ^ⁿ x ≡ 1#

    φ : G+ → G*
    φ-hom : GroupHomomorphism 𝔾+ 𝔾* φ
    φ-hom-iterated : ∀ {x c} → φ (x ⊗ⁿ c) ≡ φ x ^ⁿ c

    q : Num
    q-prime : Prime q

    _div-q : Num → Num
    _mod-q : Num → Num
    div-mod-q-propⁿ : ∀ d → d ≡ d mod-q +ⁿ (d div-q) *ⁿ q

    inv-mod-q : Num → Num
    inv-mod-q-prop : ∀ x → x ≢ 0ⁿ → (inv-mod-q x *ⁿ x)mod-q ≡ 1ⁿ

    Y : G*

    -- Can be turned into a dynamic test!
    G*-order : Y ^ⁿ q ≡ 1#

    ^ⁿ1ⁿ+ⁿ : ∀ {x} → Y ^ⁿ(1ⁿ +ⁿ x) ≡ Y * Y ^ⁿ x
    ^ⁿ-*  : ∀ {x y} → Y ^ⁿ(y *ⁿ x) ≡ (Y ^ⁿ x)^ⁿ y
    ^ⁿ-∸ⁿ : ∀ {c₀ c₁}(c> : c₀ > c₁) → Y ^ⁿ(c₀ ∸ⁿ c₁) ≡ (Y ^ⁿ c₀) / (Y ^ⁿ c₁)

module FromPackage (p : Package) where
  open Package p
  open ≡-Reasoning

  private
    module φ = GroupHomomorphism φ-hom
    module 𝔾* = Group 𝔾*

  Y^-^-1/-id : ∀ {x y} → x > y → (Y ^ⁿ(x ∸ⁿ y))^ⁿ(inv-mod-q(x ∸ⁿ y)) ≡ Y
  Y^-^-1/-id {x} {y} x>y
    = (Y ^ⁿ d)^ⁿ(inv-mod-q d) ≡⟨ ! ^ⁿ-* ⟩
      Y ^ⁿ(inv-mod-q d *ⁿ d)  ≡⟨ ap (_^ⁿ_ Y) (div-mod-q-propⁿ e) ⟩
      Y ^ⁿ(r +ⁿ m *ⁿ q)        ≡⟨ ap (λ z → Y ^ⁿ(z +ⁿ m *ⁿ q)) (inv-mod-q-prop d (<-∸≢0 x y x>y)) ⟩
      Y ^ⁿ(1ⁿ +ⁿ(m *ⁿ q))      ≡⟨ ^ⁿ1ⁿ+ⁿ ⟩
      Y * Y ^ⁿ(m *ⁿ q)        ≡⟨ *= idp ^ⁿ-* ⟩
      Y * (Y ^ⁿ q)^ⁿ m        ≡⟨ ap (λ z → Y * z ^ⁿ m) G*-order ⟩
      Y * 1# ^ⁿ m            ≡⟨ *= idp (1^ⁿ m) ⟩
      Y * 1#                 ≡⟨ *1-identity ⟩
      Y ∎
      where d = x ∸ⁿ y
            e = inv-mod-q d *ⁿ d
            m = e div-q
            r = e mod-q

  swap? : {c₀ c₁ : Num} → c₀ ≢ c₁ → (c₀ > c₁) ⊎ (c₁ > c₀)
  swap? {x} {y} i with compare x y
  swap? i | tri< a ¬b ¬c = inr a
  swap? i | tri> ¬a ¬b c = inl c
  swap? i | tri≈ ¬a b ¬c = 𝟘-elim (i b)

  open ZK.GroupHom 𝔾+ 𝔾* {{eq?-G*}} _>_ swap? _⊗ⁿ_ _^ⁿ_ _∸ⁿ_ inv-mod-q
                   φ φ-hom φ-hom-iterated
                   Y
                   ^ⁿ-∸ⁿ
                   Y^-^-1/-id
    public

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
