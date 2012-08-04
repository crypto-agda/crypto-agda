module program-distance where

open import Data.Bool
open import Data.Vec.NP using (Vec; count; countᶠ)
open import Data.Nat.NP
open import Data.Nat.Properties
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.NP
import Data.Fin as Fin
open import Function

open import flipbased-implem
open import Data.Bits

-- Renaming Prg -> Exp?
record HomPrgDist : Set₁ where
  constructor mk

  field
    _]-[_ : ∀ {n} (f g : EXP n) → Set
    ]-[-irrefl : ∀ {n} (f : EXP n) → ¬ (f ]-[ f)
    ]-[-sym : ∀ {n} {f g : EXP n} → f ]-[ g → g ]-[ f
    ]-[-cong-left-≈↺ : ∀ {n} {f g h : EXP n} → f ≈↺ g → g ]-[ h → f ]-[ h

  ]-[-cong-left-≋↺ : ∀ {n} {f g h : EXP n} → f ≋↺ g → g ]-[ h → f ]-[ h
  ]-[-cong-left-≋↺ {f = f} {g} pf pf' = ]-[-cong-left-≈↺ (≋⇒≈↺ {f = f} {g} pf) pf'

  ]-[-cong-left-≗↺ : ∀ {n} {f g h : EXP n} → f ≗↺ g → g ]-[ h → f ]-[ h
  ]-[-cong-left-≗↺ {f = f} {g} pf pf' = ]-[-cong-left-≈↺ (≗⇒≈↺ {f = f} {g} pf) pf'

  ]-[-cong-right-≈↺ : ∀ {n} {f g h : EXP n} → f ]-[ g → g ≈↺ h → f ]-[ h
  ]-[-cong-right-≈↺ pf pf' = ]-[-sym (]-[-cong-left-≈↺ (sym pf') (]-[-sym pf))

  ]-[-cong-right-≋↺ : ∀ {n} {f g h : EXP n} → f ]-[ g → g ≋↺ h → f ]-[ h
  ]-[-cong-right-≋↺ {g = g} {h} pf pf' = ]-[-cong-right-≈↺ pf (≋⇒≈↺ {f = g} {h} pf')

  ]-[-cong-right-≗↺ : ∀ {n} {f g h : EXP n} → f ]-[ g → g ≗↺ h → f ]-[ h
  ]-[-cong-right-≗↺ {g = g} {h} pf pf' = ]-[-cong-right-≈↺ pf (≗⇒≈↺ {f = g} {h} pf')

  ]-[-cong-≋↺ : ∀ {n} {f g f' g' : EXP n} → f ≋↺ g → f' ≋↺ g' → f ]-[ f' → g ]-[ g'
  ]-[-cong-≋↺ {f = f} {g} pf₀ pf₁ pf₂ = ]-[-cong-left-≋↺ (≋↺.sym {i = f} {g} pf₀) (]-[-cong-right-≋↺ pf₂ pf₁)

  ]-[-cong-≈↺ : ∀ {n} {f g f' g' : EXP n} → f ≈↺ g → f' ≈↺ g' → f ]-[ f' → g ]-[ g'
  ]-[-cong-≈↺ {f = f} {g} pf₀ pf₁ pf₂ = ]-[-cong-left-≈↺ (≈↺.sym {i = f} {g} pf₀) (]-[-cong-right-≈↺ pf₂ pf₁)

  ]-[-cong-≗↺ : ∀ {n} {f g f' g' : EXP n} → f ≗↺ g → f' ≗↺ g' → f ]-[ f' → g ]-[ g'
  ]-[-cong-≗↺ pf₀ pf₁ pf₂ = ]-[-cong-left-≗↺ (≗↺.sym pf₀) (]-[-cong-right-≗↺ pf₂ pf₁)

  breaks : ∀ {n} → ⅁? n → Set
  breaks g = g 0b ]-[ g 1b

  -- An wining adversary for game g₀ reduces to a wining adversary for game g₁
  _⇓_ : ∀ {c₀ c₁} (g₀ : ⅁? c₀) (g₁ : ⅁? c₁) → Set
  g₀ ⇓ g₁ = breaks g₀ → breaks g₁

  extensional-reduction : ∀ {c} {g₀ g₁ : ⅁? c} → g₀ ≗⅁? g₁ → g₀ ⇓ g₁
  extensional-reduction same-games = ]-[-cong-≗↺ (same-games 0b) (same-games 1b)

  reversible-don't-break : ∀ {c} (g : ⅁? c) → Reversible⅁? g → ¬(breaks g)
  reversible-don't-break g g≈g∘not g0]-[g1 = ]-[-irrefl (g 1b) (]-[-cong-left-≈↺ (g≈g∘not 1b) g0]-[g1)

module HomImplem k where
  --  | Pr[ f ≡ 1 ] - Pr[ g ≡ 1 ] | ≥ ε            [ on reals ]
  --  dist Pr[ f ≡ 1 ] Pr[ g ≡ 1 ] ≥ ε             [ on reals ]
  --  dist (#1 f / 2^ c) (#1 g / 2^ c) ≥ ε          [ on reals ]
  --  dist (#1 f) (#1 g) ≥ ε * 2^ c where ε = 2^ -k [ on rationals ]
  --  dist (#1 f) (#1 g) ≥ 2^(-k) * 2^ c            [ on rationals ]
  --  dist (#1 f) (#1 g) ≥ 2^(c - k)                [ on rationals ]
  --  dist (#1 f) (#1 g) ≥ 2^(c ∸ k)               [ on natural ]
  _]-[_ : ∀ {n} (f g : EXP n) → Set
  _]-[_ {n} f g = dist (count↺ f) (count↺ g) ≥ 2^(n ∸ k)

  ]-[-irrefl : ∀ {n} (f : EXP n) → ¬ (f ]-[ f)
  ]-[-irrefl {n} f f]-[g rewrite dist-refl (count↺ f) with ℕ≤.trans (1≤2^ (n ∸ k)) f]-[g
  ... | ()

  ]-[-sym : ∀ {n} {f g : EXP n} → f ]-[ g → g ]-[ f
  ]-[-sym {n} {f} {g} f]-[g rewrite dist-sym (count↺ f) (count↺ g) = f]-[g

  ]-[-cong-left-≈↺ : ∀ {n} {f g h : EXP n} → f ≈↺ g → g ]-[ h → f ]-[ h
  ]-[-cong-left-≈↺ {n} {f} {g} f≈g g]-[h rewrite f≈g = g]-[h
  -- dist #g #h ≥ 2^(n ∸ k)
  -- dist #f #h ≥ 2^(n ∸ k)

  homPrgDist : HomPrgDist
  homPrgDist = mk _]-[_
                  ]-[-irrefl
                  (λ {_ f g} → ]-[-sym {f = f} {g})
                  (λ {_ f g h} → ]-[-cong-left-≈↺ {f = f} {g} {h})

record PrgDist : Set₁ where
  constructor mk
  field
    _]-[_ : ∀ {m n} → EXP m → EXP n → Set
    ]-[-irrefl : ∀ {n} (f : EXP n) → ¬ (f ]-[ f)
    ]-[-sym : ∀ {m n} {f : EXP m} {g : EXP n} → f ]-[ g → g ]-[ f
    ]-[-cong-left-≋↺ : ∀ {m n o} {f : EXP m} {g : EXP n} {h : EXP o} → f ≋↺ g → g ]-[ h → f ]-[ h

  ]-[-cong-left-≈↺ : ∀ {m n} {f g : EXP m} {h : EXP n} → f ≈↺ g → g ]-[ h → f ]-[ h
  ]-[-cong-left-≈↺ {f = f} {g} pf pf' = ]-[-cong-left-≋↺ (≈⇒≋↺ {f = f} {g} pf) pf'

  ]-[-cong-left-≗↺ : ∀ {m n} {f g : EXP m} {h : EXP n} → f ≗↺ g → g ]-[ h → f ]-[ h
  ]-[-cong-left-≗↺ {f = f} {g} pf pf' = ]-[-cong-left-≈↺ (≗⇒≈↺ {f = f} {g} pf) pf'

  ]-[-cong-right-≋↺ : ∀ {m n o} {f : EXP m} {g : EXP n} {h : EXP o} → f ]-[ g → g ≋↺ h → f ]-[ h
  ]-[-cong-right-≋↺ pf pf' = ]-[-sym (]-[-cong-left-≋↺ (sym pf') (]-[-sym pf))

  ]-[-cong-right-≈↺ : ∀ {m n} {f : EXP m} {g h : EXP n} → f ]-[ g → g ≈↺ h → f ]-[ h
  ]-[-cong-right-≈↺ {g = g} {h} pf pf' = ]-[-cong-right-≋↺ pf (≈⇒≋↺ {f = g} {h} pf')

  ]-[-cong-right-≗↺ : ∀ {m n} {f : EXP m} {g h : EXP n} → f ]-[ g → g ≗↺ h → f ]-[ h
  ]-[-cong-right-≗↺ {g = g} {h} pf pf' = ]-[-cong-right-≈↺ pf (≗⇒≈↺ {f = g} {h} pf')

  ]-[-cong-≋↺ : ∀ {n} {f g f' g' : EXP n} → f ≋↺ g → f' ≋↺ g' → f ]-[ f' → g ]-[ g'
  ]-[-cong-≋↺ {f = f} {g} pf₀ pf₁ pf₂ = ]-[-cong-left-≋↺ (≋↺.sym {i = f} {g} pf₀) (]-[-cong-right-≋↺ pf₂ pf₁)

  ]-[-cong-≈↺ : ∀ {n} {f g f' g' : EXP n} → f ≈↺ g → f' ≈↺ g' → f ]-[ f' → g ]-[ g'
  ]-[-cong-≈↺ {f = f} {g} pf₀ pf₁ pf₂ = ]-[-cong-left-≈↺ (≈↺.sym {i = f} {g} pf₀) (]-[-cong-right-≈↺ pf₂ pf₁)

  ]-[-cong-≗↺ : ∀ {c c'} {f g : EXP c} {f' g' : EXP c'} → f ≗↺ g → f' ≗↺ g' → f ]-[ f' → g ]-[ g'
  ]-[-cong-≗↺ pf₀ pf₁ pf₂ = ]-[-cong-left-≗↺ (≗↺.sym pf₀) (]-[-cong-right-≗↺ pf₂ pf₁)

  breaks : ∀ {c} → ⅁? c → Set
  breaks EXP = EXP 0b ]-[ EXP 1b

  -- An wining adversary for game g₀ reduces to a wining adversary for game g₁
  _⇓_ : ∀ {c₀ c₁} (g₀ : ⅁? c₀) (g₁ : ⅁? c₁) → Set
  g₀ ⇓ g₁ = breaks g₀ → breaks g₁

  extensional-reduction : ∀ {c} {g₀ g₁ : ⅁? c} → g₀ ≗⅁? g₁ → g₀ ⇓ g₁
  extensional-reduction same-games = ]-[-cong-≗↺ (same-games 0b) (same-games 1b)

module Implem k where
  _]-[_ : ∀ {m n} → EXP m → EXP n → Set
  _]-[_ {m} {n} f g = dist ⟨2^ n * count↺ f ⟩ ⟨2^ m * count↺ g ⟩ ≥ 2^((m + n) ∸ k)

  ]-[-irrefl : ∀ {n} (f : EXP n) → ¬ (f ]-[ f)
  ]-[-irrefl {n} f f]-[g rewrite dist-refl ⟨2^ n * count↺ f ⟩ with ℕ≤.trans (1≤2^ (n + n ∸ k)) f]-[g
  ... | ()

  ]-[-sym : ∀ {m n} {f : EXP m} {g : EXP n} → f ]-[ g → g ]-[ f
  ]-[-sym {m} {n} {f} {g} f]-[g rewrite dist-sym ⟨2^ n * count↺ f ⟩ ⟨2^ m * count↺ g ⟩ | ℕ°.+-comm m n = f]-[g

{- this is currently broken

  postulate
      helper : ∀ m n o k → m + ((n + o) ∸ k) ≡ n + ((m + o) ∸ k)
      helper′ : ∀ m n o k → ⟨2^ m * (2^((n + o) ∸ k))⟩ ≡ ⟨2^ n * (2^((m + o) ∸ k))⟩

  ]-[-cong-left-≋↺ : ∀ {m n o} {f : EXP m} {g : EXP n} {h : EXP o} → f ≋↺ g → g ]-[ h → f ]-[ h
  ]-[-cong-left-≋↺ {m} {n} {o} {f} {g} {h} f≋g g]-[h
      with 2^*-mono m g]-[h
           -- 2ᵐ(dist 2ᵒ#g 2ⁿ#h) ≤ 2ᵐ2ⁿ⁺ᵒ⁻ᵏ
  ... | q rewrite sym (dist-2^* m ⟨2^ o * count↺ g ⟩ ⟨2^ n * count↺ h ⟩)
           -- dist 2ᵐ2ᵒ#g 2ᵐ2ⁿ#h ≤ 2ᵐ2ⁿ⁺ᵒ⁻ᵏ
                | 2^-comm m o (count↺ g)
           -- dist 2ᵒ2ᵐ#g 2ᵐ2ⁿ#h ≤ 2ᵐ2ⁿ⁺ᵒ⁻ᵏ
                | sym f≋g
           -- dist 2ᵒ2ⁿ#f 2ᵐ2ⁿ#h ≤ 2ᵐ2ⁿ⁺ᵒ⁻ᵏ
                | 2^-comm o n (count↺ f)
           -- dist 2ⁿ2ᵒ#f 2ᵐ2ⁿ#h ≤ 2ᵐ2ⁿ⁺ᵒ⁻ᵏ
                | 2^-comm m n (count↺ h)
           -- dist 2ⁿ2ᵒ#f 2ⁿ2ᵐ#h ≤ 2ᵐ2ⁿ⁺ᵒ⁻ᵏ
                | dist-2^* n ⟨2^ o * count↺ f ⟩ ⟨2^ m * count↺ h ⟩
           -- 2ⁿ(dist 2ᵒ#f 2ᵐ#h) ≤ 2ᵐ2ⁿ⁺ᵒ⁻ᵏ
                | 2^-+ m (n + o ∸ k) 1
           -- 2ⁿ(dist 2ᵒ#f 2ᵐ#h) ≤ 2ᵐ⁺ⁿ⁺ᵒ⁻ᵏ
                | helper m n o k
           -- 2ⁿ(dist 2ᵒ#f 2ᵐ#h) ≤ 2ⁿ⁺ᵐ⁺ᵒ⁻ᵏ
                | sym (2^-+ n (m + o ∸ k) 1)
           -- 2ⁿ(dist 2ᵒ#f 2ᵐ#h) ≤ 2ⁿ2ᵐ⁺ᵒ⁻ᵏ
                = 2^*-mono′ n q
           -- dist 2ᵒ#f 2ᵐ#h ≤ 2ᵐ⁺ᵒ⁻ᵏ

  prgDist : PrgDist
  prgDist = mk _]-[_
               ]-[-irrefl
               (λ {m n f g} → ]-[-sym {f = f} {g})
               (λ {m n o f g h} → ]-[-cong-left-≋↺ {f = f} {g} {h})
-}
