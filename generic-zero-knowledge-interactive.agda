open import Data.Bool.NP as Bool hiding (check)
open import Data.Nat
open import Data.Maybe
open import Data.Product.NP
open import Data.Bits
open import Function.NP
open import Relation.Binary.PropositionalEquality.NP

open import sum

module generic-zero-knowledge-interactive where

private
  ★ : Set₁
  ★ = Set

-- A random argument, this is only a formal notation to
-- indicate that the argument is supposed to be picked
-- at random uniformly. (do not confuse with our randomness
-- monad).
record ↺ (A : ★) : ★ where
  constructor rand
  field get : A

module M (Permutation : ★)
         (_⁻¹         : Endo Permutation)
         (sumπ        : Sum Permutation)
         (μπ          : SumProp sumπ)

         (Rₚ-xtra     : ★) -- extra prover/adversary randomness
         (sumRₚ-xtra  : Sum Rₚ-xtra)
         (μRₚ-xtra    : SumProp sumRₚ-xtra)

         (Problem     : ★)
         (_==_        : Problem → Problem → Bit)
         (==-refl     : ∀ {pb} → (pb == pb) ≡ true)
         (_∙P_        : Permutation → Endo Problem)
         (⁻¹-inverseP : ∀ π x → π ⁻¹ ∙P (π ∙P x) ≡ x)

         (Solution    : ★)
         (_∙S_        : Permutation → Endo Solution)
         (⁻¹-inverseS : ∀ π x → π ⁻¹ ∙S (π ∙S x) ≡ x)

         (check       : Problem → Solution → Bit)
         (check-∙     : ∀ p s π → check (π ∙P p) (π ∙S s) ≡ check p s)

         (easy-pb     : Permutation → Problem)
         (easy-sol    : Permutation → Solution)
         (check-easy  : ∀ π → check (π ∙P easy-pb π) (π ∙S easy-sol π) ≡ true)
    where

    -- prover/adversary randomness
    Rₚ : ★
    Rₚ = Permutation × Rₚ-xtra

    sumRₚ : Sum Rₚ
    sumRₚ = sumπ ×Sum sumRₚ-xtra

    μRₚ : SumProp sumRₚ
    μRₚ = μπ ×μ μRₚ-xtra

    R = Bit × Rₚ

    sumR : Sum R
    sumR = sumBit ×Sum sumRₚ

    μR : SumProp sumR
    μR = μBit ×μ μRₚ

    check-π : Problem → Solution → Rₚ → Bit
    check-π p s (π , _) = check (π ∙P p) (π ∙S s)

    otp-∙-check : let #_ = count μRₚ
                  in
                  ∀ p₀ s₀ p₁ s₁ →
                    check p₀ s₀ ≡ check p₁ s₁ →
                    #(check-π p₀ s₀) ≡ #(check-π p₁ s₁)
    otp-∙-check p₀ s₀ p₁ s₁ check-pf =
      count-ext μRₚ {f = check-π p₀ s₀} {check-π p₁ s₁} (λ π,r →
        check-π p₀ s₀ π,r ≡⟨ check-∙ p₀ s₀ (proj₁ π,r) ⟩
        check p₀ s₀       ≡⟨ check-pf ⟩
        check p₁ s₁       ≡⟨ sym (check-∙ p₁ s₁ (proj₁ π,r)) ⟩
        check-π p₁ s₁ π,r ∎)
        where open ≡-Reasoning

    #_ : (↺ (Bit × Permutation × Rₚ-xtra) → Bit) → ℕ
    # f = count μR (f ∘ rand)

    _≡#_ : (f g : ↺ (Bit × Rₚ) → Bit) → ★
    f ≡# g = # f ≡ # g

{-
    otp-∙ : let otp = λ O pb s → count μRₚ (λ { (π , _) → O (π ∙P pb) (π ∙S s) }) in
            ∀ pb₀ s₀ pb₁ s₁ →
              check pb₀ s₀ ≡ check pb₁ s₁ →
              (O : _ → _ → Bit) → otp O pb₀ s₀ ≡ otp O pb₁ s₁
    otp-∙ pb₀ s₀ pb₁ s₁ check-pf O = {!(μπ ×Sum-proj₂ μRₚ-xtra    ?!}
-}
    Answer : Bit → ★
    Answer false{-0b-} = Permutation
    Answer true {-1b-} = Solution

    answer : Permutation → Solution → ∀ b → Answer b
    answer π _ false = π
    answer _ s true  = s

    -- The prover is the advesary in the generic terminology,
    -- and the verifier is the challenger.
    DepProver : ★
    DepProver = Problem → ↺ Rₚ → (b : Bit) → Problem × Answer b

    Prover₀ : ★
    Prover₀ = Problem → ↺ Rₚ → Problem × Permutation

    Prover₁ : ★
    Prover₁ = Problem → ↺ Rₚ → Problem × Solution

    Prover : ★
    Prover = Prover₀ × Prover₁

    prover : DepProver → Prover
    prover dpr = (λ pb r → dpr pb r 0b) , (λ pb r → dpr pb r 1b)

    depProver : Prover → DepProver
    depProver (pr₀ , pr₁) pb r false = pr₀ pb r
    depProver (pr₀ , pr₁) pb r true  = pr₁ pb r

    -- Here we show that the explicit commitment step seems useless given
    -- the formalization. The verifier can "trust" the prover on the fact
    -- that any choice is going to be govern only by the problem and the
    -- randomness.
    module WithCommitment (Commitment : ★)
                          (AnswerWC   : Bit → ★)
                          (reveal     : ∀ b → Commitment → AnswerWC b → Problem × Answer b) where
        ProverWC = (Problem → Rₚ → Commitment)
                 × (Problem → Rₚ → (b : Bit) → AnswerWC b)

        depProver' : ProverWC → DepProver
        depProver' (pr₀ , pr₁) pb (rand rₚ) b = reveal b (pr₀ pb rₚ) (pr₁ pb rₚ b)

    Verif : Problem → ∀ b → Problem × Answer b → Bit
    Verif pb false{-0b-} (π∙pb , π)   = (π ∙P pb) == π∙pb
    Verif pb true {-1b-} (π∙pb , π∙s) = check π∙pb π∙s

    _⇄′_ : Problem → DepProver → Bit → ↺ Rₚ → Bit
    (pb ⇄′ pr) b (rand rₚ) = Verif pb b (pr pb (rand rₚ) b)

    _⇄_ : Problem → DepProver → ↺ (Bit × Rₚ) → Bit
    (pb ⇄ pr) (rand (b , rₚ)) = (pb ⇄′ pr) b (rand rₚ)

    _⇄''_ : Problem → Prover → ↺ (Bit × Rₚ) → Bit
    pb ⇄'' pr = pb ⇄ depProver pr

    honest : (Problem → Maybe Solution) → DepProver
    honest solve pb (rand (π , rₚ)) b = (π ∙P pb , answer π sol b)
      module Honest where
        sol : Solution
        sol with solve pb
        ...    | just sol = π ∙S sol
        ...    | nothing  = π ∙S easy-sol π

    module WithCorrectSolver (pb      : Problem)
                             (s       : Solution)
                             (check-s : check pb s ≡ true)
                             where

        -- When the honest prover has a solution, he gets accepted
        -- unconditionally by the verifier.
        honest-accepted : ∀ r → (pb ⇄ honest (const (just s))) r ≡ 1b
        honest-accepted (rand (true  , π , rₚ)) rewrite check-∙ pb s π = check-s
        honest-accepted (rand (false , π , rₚ)) = ==-refl

    honest-⅁ = λ pb s → (pb ⇄ honest (const (just s)))

    module HonestLeakZeroKnowledge (pb₀ pb₁  : Problem)
                                   (s₀ s₁    : Solution)
                                   (check-pf : check pb₀ s₀ ≡ check pb₁ s₁) where

        helper : ∀ rₚ → Bool.toℕ ((pb₀ ⇄′ honest (const (just s₀))) 0b (rand rₚ))
                      ≡ Bool.toℕ ((pb₁ ⇄′ honest (const (just s₁))) 0b (rand rₚ))
        helper (π , rₚ) rewrite ==-refl {π ∙P pb₀} | ==-refl {π ∙P pb₁} = refl

        honest-leak : honest-⅁ pb₀ s₀ ≡# honest-⅁ pb₁ s₁
        honest-leak rewrite otp-∙-check pb₀ s₀ pb₁ s₁ check-pf | sum-ext μRₚ helper = refl

    module HonestLeakZeroKnowledge' (pb       : Problem)
                                    (s₀ s₁    : Solution)
                                    (check-pf : check pb s₀ ≡ check pb s₁) where

        honest-leak : honest-⅁ pb s₀ ≡# honest-⅁ pb s₁
        honest-leak = HonestLeakZeroKnowledge.honest-leak pb pb s₀ s₁ check-pf

    -- Predicts b=b′
    cheater : ∀ b′ → DepProver
    cheater b′ pb (rand (π , _)) b = π ∙P (case b′ 0→ pb 1→ easy-pb π)
                                   , answer π (π ∙S easy-sol π) b

    -- If cheater predicts correctly, verifer accepts him
    cheater-accepted : ∀ b pb rₚ → (pb ⇄′ cheater b) b rₚ ≡ 1b
    cheater-accepted true  pb (rand (π , rₚ)) = check-easy π
    cheater-accepted false pb (rand (π , rₚ)) = ==-refl

    -- If cheater predicts incorrecty, verifier rejects him
    module CheaterRejected (pb : Problem)
                           (not-easy-sol : ∀ π → check (π ∙P pb) (π ∙S easy-sol π) ≡ false)
                           (not-easy-pb  : ∀ π → ((π ∙P pb) == (π ∙P easy-pb π)) ≡ false) where

        cheater-rejected : ∀ b rₚ → (pb ⇄′ cheater (not b)) b rₚ ≡ 0b
        cheater-rejected true  (rand (π , rₚ)) = not-easy-sol π
        cheater-rejected false (rand (π , rₚ)) = not-easy-pb π

module DLog (ℤq  : ★)
            (_⊞_ : ℤq → ℤq → ℤq)
            (⊟_  : ℤq → ℤq)
            (G   : ★)
            (g   : G)
            (_^_ : G → ℤq → G)
            (_∙_ : G → G → G)
            (⊟-⊞ : ∀ π x → (⊟ π) ⊞ (π ⊞ x) ≡ x)
            (^⊟-∙ : ∀ α β x → ((α ^ (⊟ x)) ∙ ((α ^ x) ∙ β)) ≡ β)
            -- (∙-assoc : ∀ α β γ → α ∙ (β ∙ γ) ≡ (α ∙ β) ∙ γ)
            (dist-^-⊞ : ∀ α x y → α ^ (x ⊞ y) ≡ (α ^ x) ∙ (α ^ y))
            (_==_ : G → G → Bool)
            (==-refl  : ∀ {α} → (α == α) ≡ true)
            (==-true  : ∀ {α β} → α == β ≡ true → α ≡ β)
            (==-false : ∀ {α β} → α == β ≡ false → α ≢ β)
            (sumℤq      : Sum ℤq)
            (μℤq        : SumProp sumℤq)
            (Rₚ-xtra    : ★) -- extra prover/adversary randomness
            (sumRₚ-xtra : Sum Rₚ-xtra)
            (μRₚ-xtra   : SumProp sumRₚ-xtra)
            (some-ℤq    : ℤq)
   where

   Permutation = ℤq
   Problem = G
   Solution = ℤq

   _⁻¹ : Endo Permutation
   π ⁻¹ = ⊟ π

   g^_ : ℤq → G
   g^ x = g ^ x

   _∙P_ : Permutation → Endo Problem
   π ∙P p = g^ π ∙ p

   ⁻¹-inverseP : ∀ π x → π ⁻¹ ∙P (π ∙P x) ≡ x
   ⁻¹-inverseP π x rewrite ^⊟-∙ g x π = refl

   _∙S_ : Permutation → Endo Solution
   π ∙S s = π ⊞ s

   ⁻¹-inverseS : ∀ π x → π ⁻¹ ∙S (π ∙S x) ≡ x
   ⁻¹-inverseS = ⊟-⊞

   check : Problem → Solution → Bit
   check p s = p == g^ s

   check-∙' : ∀ p s π b → check p s ≡ b → check (π ∙P p) (π ∙S s) ≡ b
   check-∙' p s π true  check-p-s rewrite dist-^-⊞ g π s | ==-true check-p-s = ==-refl
   check-∙' p s π false check-p-s rewrite dist-^-⊞ g π s
      with ==-false check-p-s ?
   ... | ()

   check-∙ : ∀ p s π → check (π ∙P p) (π ∙S s) ≡ check p s
   check-∙ p s π = check-∙' p s π (check p s) refl

   easy-sol : Permutation → Solution
   easy-sol π = some-ℤq

   easy-pb : Permutation → Problem
   easy-pb π = g^(easy-sol π)

   check-easy : ∀ π → check (π ∙P easy-pb π) (π ∙S easy-sol π) ≡ true
   check-easy π rewrite dist-^-⊞ g π (easy-sol π) = ==-refl

   open M Permutation _⁻¹ sumℤq μℤq Rₚ-xtra sumRₚ-xtra μRₚ-xtra
          Problem _==_ ==-refl _∙P_ ⁻¹-inverseP Solution _∙S_ ⁻¹-inverseS check check-∙ easy-pb easy-sol check-easy
-- -}
-- -}
-- -}
-- -}
-- -}
