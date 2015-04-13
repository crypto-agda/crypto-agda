{-# OPTIONS --without-K #-}
open import Type using (Type)
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
open import Data.Nat.NP hiding (_==_; _^_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties
import ZK.SigmaProtocol.KnownStatement
import ZK.GroupHom

module ZK.GroupHom.NatChal
  where
postulate
  G+ G* : Type
  𝔾+ : Group G+
  𝔾* : Group G*
  _==_ : G* → G* → Bool
  ✓-== : ∀ {x y} → x ≡ y → ✓ (x == y)
  ==-✓ : ∀ {x y} → ✓ (x == y) → x ≡ y
  φ : G+ → G*
  φ-hom : GroupHomomorphism 𝔾+ 𝔾* φ
  Y : G*
  q : ℕ

open Additive-Group 𝔾+
open Multiplicative-Group 𝔾*

-- TODO
postulate
  _div_ : ℕ → ℕ → ℕ
  _mod_ : ℕ → ℕ → ℕ
  div-mod-spec : ∀ {n q} → n ≡ (n mod q) +ℕ q *ℕ (n div q)
  1/ : ℕ → ℕ
  1/-prop : ∀ n → (1/ n *ℕ n) mod q ≡ 1

  -- Can be turned into a dynamic test!
  G*-order : Y ^⁺ q ≡ 1#

open ≡-Reasoning

module φ = GroupHomomorphism φ-hom
module 𝔾* = Group 𝔾*

Y^-^-1/-id : ∀ {x y} → x > y → (Y ^⁺(x ∸ y))^⁺(1/(x ∸ y)) ≡ Y
Y^-^-1/-id {x} {y} x>y
  = (Y ^⁺ d)^⁺(1/ d)     ≡⟨ ! 𝔾*.^⁺-* (1/ d) ⟩
    Y ^⁺(1/ d *ℕ d)      ≡⟨ ap (_^⁺_ Y) div-mod-spec ⟩
    Y ^⁺(r +ℕ q *ℕ m)    ≡⟨ ap (λ z → Y ^⁺(z +ℕ q *ℕ m)) (1/-prop d) ⟩
    Y ^⁺(1+(q *ℕ m))     ≡⟨ ap (λ z → Y ^⁺(1+ z)) (ℕ°.*-comm q m) ⟩
    Y ^⁺(1+(m *ℕ q))     ≡⟨by-definition⟩
    Y * Y ^⁺(m *ℕ q)     ≡⟨ *= idp (𝔾*.^⁺-* m) ⟩
    Y * (Y ^⁺ q)^⁺ m     ≡⟨ ap (λ z → Y * z ^⁺ m) G*-order ⟩
    Y * 1# ^⁺ m          ≡⟨ *= idp (1^⁺ m) ⟩
    Y * 1#               ≡⟨ *1-identity ⟩
    Y ∎
    where d = x ∸ y
          e = 1/ d *ℕ d
          m = e div q
          r = e mod q

swap? : {c₀ c₁ : ℕ} → c₀ ≢ c₁ → (c₀ > c₁) ⊎ (c₁ > c₀)
swap? {x} {y} i with ℕcmp.compare x y
swap? i | tri< a ¬b ¬c = inr a
swap? i | tri> ¬a ¬b c = inl c
swap? i | tri≈ ¬a b ¬c = 𝟘-elim (i b)

open ZK.GroupHom 𝔾+ 𝔾* _==_ ✓-== ==-✓ _>_ swap? _⊗⁺_ _^⁺_ _∸_ 1/
                 φ φ-hom (λ {x} {n} → φ.hom-iterated⁺ n)
                 Y
                 (λ {x}{y}i → 𝔾*.^⁺-∸ {Y}{x}{y} (>→≥ i))
                 (λ{x}{y}i → Y^-^-1/-id{x}{y}i)
  public

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
