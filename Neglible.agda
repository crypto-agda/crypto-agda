{-# OPTIONS --copatterns #-}
open import Algebra

open import Function
open import Function.Extensionality

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

infix 4 _≤→_
record _≤→_ (f g : ℕ→ℚ) : Set where
  constructor mk
  open ℕ→ℚ f renaming (εN to fN; εD to fD)
  open ℕ→ℚ g renaming (εN to gN; εD to gD)
  field
    -- fN k / fD k ≤ gN k / gD k
    ≤→ : ∀ k → fN k * gD k ≤ gN k * fD k

≤→-refl : ∀ {f} → f ≤→ f
_≤→_.≤→ ≤→-refl k = OR.refl

≤→-trans : ∀ {f g h} → f ≤→ g → g ≤→ h → f ≤→ h
_≤→_.≤→ (≤→-trans {fN / fD [ fD-pos ]} {gN / gD [ gD-pos ]} {hN / hD [ hD-pos ]} (mk fg) (mk gh)) k
  = ≤-*-cancel (gD-pos k) lemma
  where
    open ≤-Reasoning
    lemma : gD k * (fN k * hD k) ≤ gD k * (hN k * fD k)
    lemma = gD k * (fN k * hD k)
          ≡⟨ ! prop.*-assoc (gD k) (fN k) (hD k)
             ∙ ap (flip _*_ (hD k)) (prop.*-comm (gD k) (fN k))
           ⟩
            (fN k * gD k) * hD k
          ≤⟨ fg k *-mono OR.refl ⟩
            (gN k * fD k) * hD k
          ≡⟨ prop.*-assoc (gN k) (fD k) (hD k)
             ∙ ap (_*_ (gN k)) (prop.*-comm (fD k) (hD k))
             ∙ ! prop.*-assoc (gN k) (hD k) (fD k)
           ⟩
            (gN k * hD k) * fD k
          ≤⟨ gh k *-mono OR.refl ⟩
            (hN k * gD k) * fD k
          ≡⟨ ap (flip _*_ (fD k)) (prop.*-comm (hN k) (gD k))
             ∙ prop.*-assoc (gD k) (hN k) (fD k)
           ⟩
            gD k * (hN k * fD k)
          ∎

+ℕℚ-mono : ∀ {f f' g g'} → f ≤→ f' → g ≤→ g' → f +ℕℚ g ≤→ f' +ℕℚ g'
_≤→_.≤→ (+ℕℚ-mono {fN / fD [ _ ]} {f'N / f'D [ _ ]} {gN / gD [ _ ]} {g'N / g'D [ _ ]} (mk ff) (mk gg)) k
  = (fN k * gD k + gN k * fD k) * (f'D k * g'D k)
  ≡⟨ proj₂ prop.distrib (f'D k * g'D k) (fN k * gD k) (gN k * fD k)  ⟩
    fN k * gD k * (f'D k * g'D k) + gN k * fD k * (f'D k * g'D k)
  ≡⟨ ap₂ _+_ (*-interchange (fN k) (gD k) (f'D k) (g'D k) ∙ ap (_*_ (fN k * f'D k)) (prop.*-comm (gD k) (g'D k)))
             (ap (_*_ (gN k * fD k)) (prop.*-comm (f'D k) (g'D k)) ∙ *-interchange (gN k) (fD k) (g'D k) (f'D k))
   ⟩
    fN k * f'D k * (g'D k * gD k) + gN k * g'D k * (fD k * f'D k)
  ≤⟨ (ff k *-mono OR.refl) +-mono (gg k *-mono OR.refl) ⟩
    f'N k * fD k * (g'D k * gD k) + g'N k * gD k * (fD k * f'D k)
  ≡⟨ ap₂ _+_ (*-interchange (f'N k) (fD k) (g'D k) (gD k))
             (ap (_*_ (g'N k * gD k)) (prop.*-comm (fD k) (f'D k))
             ∙ *-interchange (g'N k) (gD k) (f'D k) (fD k)
             ∙ ap (_*_ (g'N k * f'D k)) (prop.*-comm (gD k) (fD k)))
   ⟩
    f'N k * g'D k * (fD k * gD k) + g'N k * f'D k * (fD k * gD k)
  ≡⟨ ! proj₂ prop.distrib (fD k * gD k) (f'N k * g'D k) (g'N k * f'D k) ⟩
    (f'N k * g'D k + g'N k * f'D k) * (fD k * gD k)
  ∎
  where
    open ≤-Reasoning

record NegBounded (f : ℕ→ℚ) : Set where
    constructor mk
    field
      ε : ℕ→ℚ
      ε-neg : Is-Neg ε
      bounded : f ≤→ ε

module _ where
  open NegBounded

  fromNeg : {f : ℕ→ℚ} → Is-Neg f → NegBounded f
  ε (fromNeg f-neg) = _
  ε-neg (fromNeg f-neg) = f-neg
  bounded (fromNeg f-neg) = ≤→-refl

  ≤-NB : {f g : ℕ→ℚ} → f ≤→ g → NegBounded g → NegBounded f
  ε (≤-NB le nb) = ε nb
  ε-neg (≤-NB le nb) = ε-neg nb
  bounded (≤-NB le nb) = ≤→-trans le (bounded nb)

  _+NB_ : {f g : ℕ→ℚ} → NegBounded f → NegBounded g → NegBounded (f +ℕℚ g)
  ε (fNB +NB gNB) = ε fNB +ℕℚ ε gNB
  ε-neg (fNB +NB gNB) = +ℕℚ-neg (ε-neg fNB) (ε-neg gNB)
  bounded (fNB +NB gNB) = +ℕℚ-mono (bounded fNB) (bounded gNB)

module ~-NegBounded (Rᵁ : ℕ → U)(let R = λ n → El (Rᵁ n))(inh : ∀ x → 0 < Card (Rᵁ x)) where

  # : ∀ {n} → Count (R n)
  # {n} = count (Rᵁ n)

  ~dist : (f g : (x : ℕ) → R x → 𝟚) → ℕ→ℚ
  ℕ→ℚ.εN (~dist f g) n = dist (# (f n)) (# (g n))
  ℕ→ℚ.εD (~dist f g) n = Card (Rᵁ n)
  ℕ→ℚ.εD-pos (~dist f g) n = inh n

  ~dist-sum : ∀ f g h → ~dist f h ≤→ ~dist f g +ℕℚ ~dist g h
  _≤→_.≤→ (~dist-sum f g h) k
      = #fh * (|R| * |R|)
      ≤⟨ dist-sum #f #g #h *-mono OR.refl ⟩
        (#fg + #gh) * (|R| * |R|)
      ≡⟨ ! prop.*-assoc (#fg + #gh) |R| |R| ∙ ap (flip _*_ |R|) (proj₂ prop.distrib |R| #fg #gh) ⟩
        (#fg * |R| + #gh * |R|) * |R|
      ∎
    where
      open ≤-Reasoning
      |R| = Card (Rᵁ k)
      #f = # (f k)
      #g = # (g k)
      #h = # (h k)
      #fh = dist #f #h
      #fg = dist #f #g
      #gh = dist #g #h

  record _~_ (f g : (x : ℕ) → R x → 𝟚) : Set where
    constructor mk
    field
      ~ : NegBounded (~dist f g)

  ~-trans : Transitive _~_
  _~_.~ (~-trans {f}{g}{h} (mk fg) (mk gh)) = ≤-NB (~dist-sum f g h) (fg +NB gh)

  ~-Inv : {{_ : FunExt}}{{_ : UA}}(π : ∀ n → R n ≃ R n)(f g : ∀ x → R x → 𝟚)
          (eq : ∀ x (r : R x) → f x r ≡ g x (proj₁ (π x) r)) → f ~ g
  _~_.~ (~-Inv π f g eq) = ≤-NB lemma (fromNeg 0ℕℚ-neg)
    where
      open ≤-Reasoning
      lemma : ~dist f g ≤→ 0ℕℚ
      _≤→_.≤→ lemma k = dist (# (f k)) (# (g k)) * 1
                      ≡⟨ proj₂ prop.*-identity _ ⟩
                        dist (# (f k)) (# (g k))
                      ≡⟨ ap (flip dist (# (g k))) (count-ext (Rᵁ k) (eq k)) ⟩
                        dist (# (g k ∘ proj₁ (π k))) (# (g k))
                      ≡⟨ ap (flip dist (# (g k))) (sumStableUnder (Rᵁ k) (π k) (𝟚▹ℕ ∘ g k)) ⟩
                        dist (# (g k)) (# (g k))
                      ≡⟨ dist-refl (# (g k)) ⟩
                        0
                      ∎

module ~-Inlined (Rᵁ : ℕ → U)(let R = λ n → El (Rᵁ n)) where

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
