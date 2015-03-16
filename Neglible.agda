{-# OPTIONS --copatterns #-}
open import Algebra

open import Function

open import Data.Nat.NP
open import Data.Nat.Distance
open import Data.Nat.Properties
open import Data.Two
open import Data.Zero
open import Data.Product

open import Relation.Binary
open import Relation.Binary.PropositionalEquality.NP

open import HoTT
open Equivalences

open import Explore.Core
open import Explore.Universe.Type {𝟘}
open import Explore.Universe.Base

module Neglible where

module prop = CommutativeSemiring commutativeSemiring
module OR = Poset (DecTotalOrder.poset decTotalOrder)

≤-*-cancel : ∀ {x m n} → 1 ≤ x →  x * m ≤ x * n → m ≤ n
≤-*-cancel {suc x} {m} {n} (s≤s le) mn
  rewrite prop.*-comm (suc x) m | prop.*-comm (suc x) n = cancel-*-right-≤ _ _ _ mn

record ℕ→ℚ : Set where
  constructor _/_[_]
  field
    εN : (n : ℕ) → ℕ
    εD : (n : ℕ) → ℕ
    εD-pos : ∀ n → εD n > 0

record Is-Neg (ε : ℕ→ℚ) : Set where
  constructor mk
  open ℕ→ℚ ε
  field
    cₙ : (c : ℕ) → ℕ
    prf : ∀(c n : ℕ) → n > cₙ n → n ^ c * εN n ≤ εD n
open Is-Neg

0ℕℚ : ℕ→ℚ
ℕ→ℚ.εN 0ℕℚ _ = 0
ℕ→ℚ.εD 0ℕℚ _ = 1
ℕ→ℚ.εD-pos 0ℕℚ _ = s≤s z≤n

0ℕℚ-neg : Is-Neg 0ℕℚ
cₙ 0ℕℚ-neg _ = 0
prf 0ℕℚ-neg c n x = OR.trans (OR.reflexive (proj₂ prop.zero (n ^ c))) z≤n

_+ℕℚ_ : ℕ→ℚ → ℕ→ℚ → ℕ→ℚ
ℕ→ℚ.εN ((εN / εD [ _ ]) +ℕℚ (μN / μD [ _ ])) n = εN n * μD n + μN n * εD n
ℕ→ℚ.εD ((εN / εD [ _ ]) +ℕℚ (μN / μD [ _ ])) n = εD n * μD n
ℕ→ℚ.εD-pos ((εN / εD [ εD+ ]) +ℕℚ (μN / μD [ μD+ ])) n = εD+ n *-mono μD+ n


+ℕℚ-neg : {ε μ : ℕ→ℚ} → Is-Neg ε → Is-Neg μ → Is-Neg (ε +ℕℚ μ)
cₙ (+ℕℚ-neg ε μ) n = 1 + cₙ ε n + cₙ μ n
prf (+ℕℚ-neg {εM} {μM} ε μ) c n n>nc = ≤-*-cancel {x = n} (OR.trans (s≤s z≤n) n>nc) lemma
  where

  open ≤-Reasoning
  open ℕ→ℚ εM
  open ℕ→ℚ μM renaming (εN to μN; εD to μD; εD-pos to μD-pos)

  lemma =  n * (n ^ c * (εN n * μD n + μN n * εD n))
        ≡⟨ ! prop.*-assoc n (n ^ c) _
         ∙ proj₁ prop.distrib (n ^ (1 + c)) (εN n * μD n) (μN n * εD n)
         ∙ ap₂ _+_ (! prop.*-assoc (n ^ (1 + c)) (εN n) (μD n))
                   (! (prop.*-assoc (n ^ (1 + c)) (μN n) (εD n))) ⟩
           n ^ (1 + c) * εN n * μD n + n ^ (1 + c) * μN n * εD n
        ≤⟨     (prf ε (1 + c) n (OR.trans (s≤s (≤-step (m≤m+n (cₙ ε n) (cₙ μ n)))) n>nc) *-mono (μD n ∎))
        +-mono (prf μ (1 + c) n (OR.trans (s≤s (≤-step (n≤m+n (cₙ ε n) (cₙ μ n)))) n>nc) *-mono (εD n ∎)) ⟩
           εD n * μD n + μD n * εD n
        ≡⟨ ap₂ _+_ (refl {x = εD n * μD n}) (prop.*-comm (μD n) (εD n) ∙ ! proj₂ prop.+-identity (εD n * μD n)) ⟩
           2 * (εD n * μD n)
        ≤⟨ OR.trans (s≤s (s≤s z≤n)) n>nc *-mono (εD n * μD n ∎) ⟩
           n * (εD n * μD n)
        ∎


module _ (Rᵁ : ℕ → U)(let R = λ n → El (Rᵁ n)) where

  # : ∀ {n} → Count (R n)
  # {n} = count (Rᵁ n)

  record _~_ (f g : (x : ℕ) → R x → 𝟚) : Set where
    constructor mk
    field
      ε : ℕ→ℚ
    open ℕ→ℚ ε
    field
      ε-neg : Is-Neg ε
      bounded : ∀ k → εD k * dist (# (f k)) (# (g k)) ≤ Card (Rᵁ k) * εN k


  ~-trans : Transitive _~_
  _~_.ε (~-trans x x₁) = _
  _~_.ε-neg (~-trans x x₁) = +ℕℚ-neg (_~_.ε-neg x) (_~_.ε-neg x₁)
  _~_.bounded (~-trans {f}{g}{h}(mk ε₀ ε₀-neg fg) (mk ε₁ ε₁-neg gh)) k
      = (b * d) * dist #f #h
      ≤⟨ (b * d ∎) *-mono dist-sum #f #g #h ⟩
        (b * d) * (dist #f #g + dist #g #h)
      ≡⟨ proj₁ prop.distrib (b * d) (dist #f #g) (dist #g #h)
         ∙ ap₂ _+_ (ap₂ _*_ (prop.*-comm b d) refl
         ∙ prop.*-assoc d b (dist #f #g)) (prop.*-assoc b d (dist #g #h))
       ⟩
        d * (b * dist #f #g) + b * (d * dist #g #h)
      ≤⟨ ((d ∎) *-mono fg k) +-mono ((b ∎) *-mono gh k) ⟩
        d * (|R| * a) + b * (|R| * c)
      ≡⟨ ap₂ _+_ (rot d |R| a) (rot b |R| c) ∙ ! proj₁ prop.distrib |R| (a * d) (c * b) ⟩
        |R| * ℕ→ℚ.εN (ε₀ +ℕℚ ε₁) k
      ∎
   where
     open ≤-Reasoning
     rot : ∀ x y z → x * (y * z) ≡ y * (z * x)
     rot x y z = prop.*-comm x (y * z) ∙ prop.*-assoc y z x
     |R| = Card (Rᵁ k)
     #f = # (f k)
     #g = # (g k)
     #h = # (h k)
     a = ℕ→ℚ.εN ε₀ k
     b = ℕ→ℚ.εD ε₀ k
     c = ℕ→ℚ.εN ε₁ k
     d = ℕ→ℚ.εD ε₁ k
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
