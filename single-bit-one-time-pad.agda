module single-bit-one-time-pad where

open import Function.NP
open import Data.Bool.NP as Bool
open import Data.Product renaming (map to <_×_>)
open import Data.Nat.NP
import Data.Vec.NP as V
open V using (Vec; take; drop; drop′; take′; _++_) renaming (swap to vswap)
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_; _≗_; module ≡-Reasoning)

open import Data.Bits
open import flipbased-implem
open import program-distance

K = Bit
M = Bit
C = Bit

record Adv (S₀ S₁ S₂ : Set) ca : Set where
  constructor mk
  field
    step₀ : ↺ ca S₀
    step₁ : S₀ → (Bit → M) × S₁
    step₂ : C × S₁ → S₂
    step₃ : S₂ → Bit

record Adv₁ (S₀ S₁ : Set) ca : Set where
  constructor mk
  field
    step₀ : ↺ ca S₀
    -- step₁ s₀ = id , s₀
    step₂ : C × S₀ → S₁
    step₃ : S₁ → Bit

Adv₂ : ∀ ca → Set
Adv₂ ca = ↺ ca (C → Bit)

module Run⅁′ {S₀ S₁ S₂ ca} (A : Adv S₀ S₁ S₂ ca) where
  open Adv A
  E : M → ↺ 1 C
  E m = toss >>= λ k → return↺ (m xor k)
  run⅁′ : ⅁? (ca + 1)
  run⅁′ b = step₀ >>= λ s₀ →
            case step₁ s₀ of λ {(m , s₁) →
            E (m b) >>= λ c →
            return↺ (step₃ (step₂ (c , s₁)))}

module Run⅁ {S₀ S₁ S₂ ca} (E : K → M → C) (A : Adv S₀ S₁ S₂ ca) (b : Bit) where
  open Adv A

  kont₀ : ⅁? _
  kont₀ k =
    step₀ ▹↺ λ s₀ →
    case step₁ s₀ of λ {(m , s₁) →
    let c = E k (m b) in
    step₃ (step₂ (c , s₁))}

  run⅁ : EXP (1 + ca)
  run⅁ = toss >>= kont₀

  {- looks wrong
module Run⅁-Properties {S₀ S₁ S₂ ca} (A : Adv S₀ S₁ S₂ ca) (b k : Bit) where
  open Run⅁ A
  kont₀-not : kont₀ b k ≡ kont₀ (not b) (not k)
  kont₀-not rewrite xor-not-not b k = {!refl!}
  -}

module SymAdv (homPrgDist : HomPrgDist) {S₀ S₁ S₂ ca} (A : Adv S₀ S₁ S₂ ca) where
  open HomPrgDist homPrgDist
  open Adv A
  step₁′ : S₀ → (Bit → M) × S₁
  step₁′ s₀ = case step₁ s₀ of λ { (m , s₁) → (m ∘ not , s₁) }
  symA : Adv S₀ S₁ S₂ ca
  symA = mk step₀ step₁′ step₂ (not ∘ step₃)

  symA′ : Adv S₀ S₁ S₂ ca
  symA′ = mk step₀ step₁′ step₂ step₃

  open Run⅁ _xor_ A renaming (run⅁ to runA)
  open Run⅁ _xor_ symA renaming (run⅁ to runSymA)
  open Run⅁ _xor_ symA′ renaming (run⅁ to runSymA′)
  {-
  helper : ∀ {n} (g₀ g₁ : EXP n) → g₀ ]-[ g₁ → not↺ g₀ ]-[ not↺ g₁
  helper = {!!}
  lem : runA ⇓ runSymA
  lem A-breaks-E = {!helper (uunSymA′ 0b) (runSymA′ 1)!}
     where pf : breaks runSymA
           pf = {!!}
  -}

module Run⅁₂ {ca} (A : Adv₂ ca) (b : Bit) where
  E : Bit → M → C
  E k m = m xor k

  m : Bit → Bit
  m = id

  kont₀ : ⅁? _
  kont₀ k =
      A ▹↺ λ f →
      f (E k (m b))

      {-
    kont₀′ : ⅁? _
    kont₀′ k =
      conv-Adv A ▹↺ λ f →
      f (E k (m b))
      -}

  run⅁₂ : EXP (1 + ca)
  run⅁₂ = toss >>= kont₀

module Run⅁₂-Properties {ca} (A : Adv₂ ca) where
    open Run⅁₂ A renaming (run⅁₂ to runA)
    kont₀-not : ∀ b k → kont₀ b k ≡ kont₀ (not b) (not k)
    kont₀-not b k rewrite xor-not-not b k = ≡.refl

    open ≡-Reasoning

    lem₂ : ∀ b → count↺ (runA b) ≡ count↺ (runA (not b))
    lem₂ b = count↺ (runA b)
          ≡⟨ ≡.refl ⟩
            count↺ (kont₀ b 0b) + count↺ (kont₀ b 1b)
          ≡⟨ ≡.cong₂ (_+_ on count↺) (kont₀-not b 0b) (kont₀-not b 1b) ⟩
            count↺ (kont₀ (not b) 1b) + count↺ (kont₀ (not b) 0b)
          ≡⟨ ℕ°.+-comm (count↺ (kont₀ (not b) 1b)) _ ⟩
            count↺ (kont₀ (not b) 0b) + count↺ (kont₀ (not b) 1b)
          ≡⟨ ≡.refl ⟩
            count↺ (runA (not b)) ∎

    lem₃ : Safe⅁? runA
    lem₃ = lem₂ 0b

    -- A specialized version of lem₂ (≈lem₃)
    lem₄ : Safe⅁? (Run⅁₂.run⅁₂ A)
    lem₄    = count↺ (runA 0b)
            ≡⟨ ≡.refl ⟩
              count↺ (kont₀ 0b 0b) + count↺ (kont₀ 0b 1b)
            ≡⟨ ≡.cong₂ (_+_ on count↺) (kont₀-not 0b 0b) (kont₀-not 0b 1b) ⟩
              count↺ (kont₀ 1b 1b) + count↺ (kont₀ 1b 0b)
            ≡⟨ ℕ°.+-comm (count↺ (kont₀ 1b 1b)) _ ⟩
              count↺ (kont₀ 1b 0b) + count↺ (kont₀ 1b 1b)
            ≡⟨ ≡.refl ⟩
              count↺ (runA 1b) ∎

conv-Adv : ∀ {ca S₀ S₁ S₂} → Adv S₀ S₁ S₂ ca → Adv₂ ca
conv-Adv A = step₀ ▹↺ λ s₀ →
             case step₁ s₀ of λ {(m , s₁) →
             λ c → m (step₃ (step₂ (c , s₁)))}
  where open Adv A

module Conv-Adv-Props (homPrgDist : HomPrgDist) {ca S₀ S₁ S₂} (A : Adv S₀ S₁ S₂ ca) where
  open HomPrgDist homPrgDist
  open Adv A
  open Run⅁ _xor_ A renaming (run⅁ to runA)
  -- open Run⅁-Properties A

  A′ : Adv₂ ca
  A′ = conv-Adv A
  open Run⅁₂ A′ using () renaming (kont₀ to kont₀′; run⅁₂ to runA′)

  kont₀′′ : ∀ b k → EXP ca
  kont₀′′ b k =
      step₀ ▹↺ λ s₀ →
      case step₁ s₀ of λ {(m , s₁) →
      m (step₃ (step₂ ((m b) xor k , s₁)))}

  kont₀′′′ : ∀ b′ → EXP ca
  kont₀′′′ b′ =
      step₀ ▹↺ λ s₀ →
      case step₁ s₀ of λ {(m , s₁) →
      m (step₃ (step₂ (b′ , s₁)))}

  {-
  kont′′-lem : ∀ b k → count↺ (kont₀ b k) ≡ count↺ (kont₀′′ b k)
  kont′′-lem true true = {!!}
  kont′′-lem false true = {!!}
  kont′′-lem true false = {!!}
  kont′′-lem false false = {!!}

  kont-lem : ∀ b k → count↺ (kont₀ b k) ≡ count↺ (kont₀′ b k)
  kont-lem b true = {!!}
  kont-lem b false = {!!}

  conv-Adv-lem : runA ≈⅁? runA′
  conv-Adv-lem b = count↺ (runA b)
        ≡⟨ refl ⟩
          count↺ (kont₀ b 0b) + count↺ (kont₀ b 1b)
        ≡⟨ cong₂ _+_ (kont-lem b 0b) (kont-lem b 1b) ⟩
          count↺ (kont₀′ b 0b) + count↺ (kont₀′ b 1b)
        ≡⟨ refl ⟩
          count↺ (runA′ b) ∎

  conv-Adv-sound : runA ⇓ runA′
  conv-Adv-sound = ]-[-cong-≈↺ (conv-Adv-lem 0b) (conv-Adv-lem 1b)
  -}
-- Cute fact: this is true by computation!
count↺-toss->>= : ∀ {c} (f : ⅁? c) → count↺ (toss >>= f) ≡ count↺ (f 0b) + count↺ (f 1b)
count↺-toss->>= f = ≡.refl

{-
module Run⅁-Properties' {S₀ S₁ S₂ ca} (A : Adv S₀ S₁ S₂ ca) (b : Bit) where
    open Run⅁ _xor_ A renaming (run⅁ to runA)
    lem : count↺ (runA b) ≡ count↺ (runA (not b))
    lem = count↺ (runA b)
        ≡⟨ refl ⟩
          count↺ (kont₀ b 0b) + count↺ (kont₀ b 1b)
        ≡⟨ cong₂ (_+_ on count↺) {x = kont₀ b 0b} {kont₀ (not b) 1b} {kont₀ b 1b} {kont₀ (not b) 0b} {!!} {!!} ⟩
          count↺ (kont₀ (not b) 1b) + count↺ (kont₀ (not b) 0b)
        ≡⟨ ℕ°.+-comm (count↺ (kont₀ (not b) 1b)) _ ⟩
          count↺ (kont₀ (not b) 0b) + count↺ (kont₀ (not b) 1b)
        ≡⟨ refl ⟩
          count↺ (runA (not b)) ∎
-}
open import program-distance
open import Relation.Nullary

⁇ : ∀ {n} → ↺ n (Bits n)
-- ⁇ = random
⁇ = mk id


lem'' : ∀ {k} (f : Bits k → Bit) → #⟨ f ∘ tail ⟩ ≡ 2* #⟨ f ⟩
lem'' f = ≡.refl

lem' : ∀ {k} (f g : Bits k → Bit) → #⟨ f ∘ tail ⟩ ≡ #⟨ g ∘ tail ⟩ → #⟨ f ⟩ ≡ #⟨ g ⟩
lem' f g pf = 2*-inj (≡.trans (lem'' f) (≡.trans pf (≡.sym (lem'' g))))

drop-tail : ∀ k {n a} {A : Set a} → drop (suc k) {n} ≗ drop k ∘ tail {A = A}
drop-tail k (x ∷ xs) = V.drop-∷ k x xs

lemdrop′ : ∀ {k n} (f : Bits n → Bit) → #⟨ f ∘ drop′ k ⟩ ≡ ⟨2^ k * #⟨ f ⟩ ⟩
lemdrop′ {zero} f = ≡.refl
lemdrop′ {suc k} f = #⟨ f ∘ drop′ k ∘ tail ⟩
                   ≡⟨ lem'' (f ∘ drop′ k) ⟩
                     2* #⟨ f ∘ drop′ k ⟩
                   ≡⟨ ≡.cong 2*_ (lemdrop′ {k} f) ⟩
                     2* ⟨2^ k * #⟨ f ⟩ ⟩ ∎
                    where open ≡-Reasoning







-- exchange to independant statements
lem-flip$-⊕ : ∀ {m n a} {A : Set a} (f : ↺ m (A → Bit)) (x : ↺ n A) →
               count↺ ⟪ flip _$_ · x · f ⟫ ≡ count↺ (f ⊛ x)
lem-flip$-⊕ {m} {n} f x = ≡.sym (
               count↺ fx
              ≡⟨ #-+ {m} {n} (run↺ fx) ⟩
               sum {m} (λ xs → #⟨_⟩ {n} (λ ys → run↺ fx (xs ++ ys)))
              ≡⟨ sum-sum {m} {n} (Bool.toℕ ∘ run↺ fx) ⟩
               sum {n} (λ ys → #⟨_⟩ {m} (λ xs → run↺ fx (xs ++ ys)))
              ≡⟨ sum-≗₂ (λ ys xs → Bool.toℕ (run↺ fx (xs ++ ys)))
                        (λ ys xs → Bool.toℕ (run↺ ⟪ flip _$_ · x · f ⟫ (ys ++ xs)))
                        (λ ys xs → ≡.cong Bool.toℕ (lem₁ xs ys)) ⟩
               sum {n} (λ ys → #⟨_⟩ {m} (λ xs → run↺ ⟪ flip _$_ · x · f ⟫ (ys ++ xs)))
              ≡⟨ ≡.sym (#-+ {n} {m} (run↺ ⟪ flip _$_ · x · f ⟫)) ⟩
               count↺ ⟪ flip _$_ · x · f ⟫
              ∎ )
    where open ≡-Reasoning
          fx = f ⊛ x
          lem₁ : ∀ xs ys → run↺ f (take m (xs ++ ys)) (run↺ x (drop m (xs ++ ys)))
                         ≡ run↺ f (drop n (ys ++ xs)) (run↺ x (take n (ys ++ xs)))
          lem₁ xs ys rewrite V.take-++ m xs ys | V.drop-++ m xs ys
                           | V.take-++ n ys xs | V.drop-++ n ys xs = ≡.refl

≈ᴬ′-toss : ∀ b → ⟪ b ⟫ᴰ ⟨xor⟩ toss ≈ᴬ′ toss
≈ᴬ′-toss true Adv = ℕ°.+-comm (count↺ (Adv true)) _
≈ᴬ′-toss false Adv = ≡.refl

≈ᴬ-toss : ∀ b → ⟪ b ⟫ᴰ ⟨xor⟩ toss ≈ᴬ toss
≈ᴬ-toss b Adv = ≈ᴬ′-toss b (returnᴰ ∘ Adv)

-- should be equivalent to #-comm if ⟪ m ⟫ᴰ ⟨⊕⟩ x were convertible to ⟪ _⊕_ m · x ⟫
≈ᴬ-⁇ : ∀ {k} (m : Bits k) → ⟪ m ⟫ᴰ ⟨⊕⟩ ⁇ ≈ᴬ ⁇
≈ᴬ-⁇ {zero}  _       _ = ≡.refl
≈ᴬ-⁇ {suc k} (h ∷ m) Adv
  rewrite ≈ᴬ-⁇ m (Adv ∘ _∷_ (h xor 0b))
        | ≈ᴬ-⁇ m (Adv ∘ _∷_ (h xor 1b))
        = ≈ᴬ′-toss h (λ x → ⟪ Adv ∘ _∷_ x · ⁇ ⟫)

open OperationSyntax

_⟨∙⟩_ : Op → ∀ {m n} → Endo (↺ m (Bits n))
f ⟨∙⟩ g = ⟪ _∙_ f · g ⟫

≈ᴬ-op-⁇ : ∀ {k} f → f ⟨∙⟩ ⁇ ≈ᴬ ⁇ {k}
≈ᴬ-op-⁇ = flip #-op

≈ᴬ-⁇₂ : ∀ {k} (m₀ m₁ : Bits k) → ⟪ m₀ ⟫ᴰ ⟨⊕⟩ ⁇ ≈ᴬ ⟪ m₁ ⟫ᴰ ⟨⊕⟩ ⁇
≈ᴬ-⁇₂ {k} m₀ m₁ = ≈ᴬ.trans {k} (≈ᴬ-⁇ m₀) (≈ᴬ.sym {k} (≈ᴬ-⁇ m₁))

≈ᴬ-⁇₃ : ∀ {k} (m : Bit → Bits k) (b : Bit) → ⟪ m b ⟫ᴰ ⟨⊕⟩ ⁇ ≈ᴬ ⟪ m (not b) ⟫ᴰ ⟨⊕⟩ ⁇
≈ᴬ-⁇₃ m b = ≈ᴬ-⁇₂ (m b) (m (not b))

≈ᴬ-⁇₄ : ∀ {k} (m : Bits k × Bits k) (b : Bit) → ⟪ proj m b ⟫ᴰ ⟨⊕⟩ ⁇ ≈ᴬ ⟪ proj m (not b) ⟫ᴰ ⟨⊕⟩ ⁇
≈ᴬ-⁇₄ = ≈ᴬ-⁇₃ ∘ proj
