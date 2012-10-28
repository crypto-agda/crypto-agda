open import Data.Bool.NP as Bool
open import Data.Nat
open import Data.Maybe
open import Data.Product.NP
open import Data.Bits
open import Function.NP
open import Relation.Binary.PropositionalEquality

open import sum

module generic-zero-knowledge-interactive where

private
  ★ : Set₁
  ★ = Set

-- record VerifiableProblem :

-- A random argument, this is only a formal notation to
-- indicate that the argument is supposed to be picked
-- at random uniformly. (do not confuse with our randomness
-- monad).
record ↺ (A : ★) : ★ where
  constructor rand
  field get : A

⟨0,⟩ : ∀ {A} → ↺ A → ↺ (Bit × A)
⟨0,⟩ (rand x) = rand (0b , x)

⟨1,⟩ : ∀ {A} → ↺ A → ↺ (Bit × A)
⟨1,⟩ (rand x) = rand (1b , x)

module G (Permutation : ★)
         (sumπ        : Sum Permutation)
         (sumπ-ext    : SumExt sumπ)
         -- (_⁻¹         : Endo Permutation)

         (Rₚ-xtra     : ★) -- extra prover/adversary randomness
         (sumRₚ-xtra  : Sum Rₚ-xtra)
         (sumRₚ-xtra-ext : SumExt sumRₚ-xtra)

         (Problem     : ★)
         (_==_        : Problem → Problem → Bit)
         (==-refl     : ∀ {pb} → (pb == pb) ≡ true)
         (_∙P_        : Permutation → Endo Problem)

         (Solution    : ★)
         (_∙S_        : Permutation → Endo Solution)

         (otp-∙       : let otp = λ A pb s → (sumToCount (sumProd sumπ sumRₚ-xtra)) (λ { (π , _) → A (π ∙P pb) (π ∙S s) }) in
                        ∀ pb₀ s₀ pb₁ s₁ (A : _ → _ → Bit) → otp A pb₀ s₀ ≡ otp A pb₁ s₁)
                        {-
                        -- is this enough
         (otp-∙′      : let otp = λ A pb s → sumπ (λ π → A (π ∙P pb) (π ∙S s)) in
                        ∀ pb₀ s₀ pb₁ s₁ (A : _ → _ → ℕ) → otp A pb₀ s₀ ≡ otp A pb₁ s₁)
                        -}

         (check       : Problem → Solution → Bit)
         (check-∙     : ∀ p s π → check p s ≡ check (π ∙P p) (π ∙S s))

         (easy-pb     : Permutation → Problem)
         (easy-sol    : Permutation → Solution)
         (check-easy  : ∀ π → check (easy-pb π) (easy-sol π) ≡ true)
    where

    -- prover/adversary randomness
    Rₚ : ★
    Rₚ = Permutation × Rₚ-xtra

    sumRₚ : Sum Rₚ
    sumRₚ = sumProd sumπ sumRₚ-xtra

    #Rₚ : Count Rₚ
    #Rₚ = sumToCount sumRₚ

    sumRₚ-ext : SumExt sumRₚ
    sumRₚ-ext = sumProd-ext sumπ-ext sumRₚ-xtra-ext

    sum : Sum (Bit × Rₚ)
    sum = sumProd sumBit sumRₚ

    sum-ext : SumExt sum
    sum-ext = sumProd-ext sumBit-ext sumRₚ-ext

    #_ : (↺ (Bit × Permutation × Rₚ-xtra) → Bit) → ℕ
    # f = sumToCount sum (f ∘ rand)

    _≡#_ : (f g : ↺ (Bit × Rₚ) → Bit) → ★
    f ≡# g = # f ≡ # g

    {-
    otp-∙ : let otp = λ A pb s → #Rₚ(λ { (π , _) → A (π ∙P pb) (π ∙S s) }) in
            ∀ pb₀ s₀ pb₁ s₁ (A : _ → _ → Bit) → otp A pb₀ s₀ ≡ otp A pb₁ s₁
    otp-∙ pb₀ s₀ pb₁ s₁ A = ?
    -}

    Answer : Bit → ★
    Answer false{-0b-} = Permutation
    Answer true {-1b-} = Solution

    -- The prover is the advesary in the generic terminology,
    -- and the verifier is the challenger.
    Prover : ★
    Prover = Problem → ↺ Rₚ → (b : Bit) → Problem × Answer b

    -- Here we show that the explicit commitment step seems useless given
    -- the formalization. The verifier can "trust" the prover on the fact
    -- that any choice is going to be govern only by the problem and the
    -- randomness.
    module WithCommitment (Commitment : ★)
                          (AnswerWC   : Bit → ★)
                          (reveal     : ∀ b → Commitment → AnswerWC b → Problem × Answer b) where
        ProverWC = (Problem → Rₚ → Commitment)
                 × (Problem → Rₚ → (b : Bit) → AnswerWC b)
        prover : ProverWC → Prover
        prover (pr₀ , pr₁) pb (rand rₚ) b = reveal b (pr₀ pb rₚ) (pr₁ pb rₚ b)

    Verif : Problem → ∀ b → Problem × Answer b → Bit
    Verif pb false{-0b-} (π∙pb , π) = (π ∙P pb) == π∙pb
    Verif pb true {-1b-} (π∙pb , s) = check π∙pb s

    _⇄′_ : Problem → Prover → Bit → ↺ Rₚ → Bit
    (pb ⇄′ pr) b (rand rₚ) = Verif pb b (pr pb (rand rₚ) b)

    _⇄_ : Problem → Prover → ↺ (Bit × Rₚ) → Bit
    (pb ⇄ pr) (rand (b , rₚ)) = (pb ⇄′ pr) b (rand rₚ)

    honest : (Problem → Maybe Solution) → Prover
    honest solve pb (rand (π , rₚ)) b = (π ∙P pb , ans b)
      module Honest where
        ans : ∀ b → Answer b
        ans false = π
        ans true  with solve pb
        ...          | just sol = π ∙S sol
        ...          | nothing  = easy-sol π

    module WithCorrectSolver (pb      : Problem)
                             (s       : Solution)
                             (check-s : check pb s ≡ true)
                             where

        -- When the honest prover has a solution, he gets accepted
        -- unconditionally by the verifier.
        honest-accepted : ∀ r → (pb ⇄ honest (const (just s))) r ≡ 1b
        honest-accepted (rand (true  , π , rₚ)) rewrite sym (check-∙ pb s π) = check-s
        honest-accepted (rand (false , π , rₚ)) = ==-refl

    honest-⅁ = λ pb s → (pb ⇄ honest (const (just s)))

    module HonestLeakZeroKnowledge (pb₀ pb₁ : Problem)
                                   (s₀ s₁   : Solution) where

        helper : ∀ rₚ → Bool.toℕ ((pb₀ ⇄′ honest (const (just s₀))) 0b (rand rₚ))
                      ≡ Bool.toℕ ((pb₁ ⇄′ honest (const (just s₁))) 0b (rand rₚ))
        helper (π , rₚ) rewrite ==-refl {π ∙P pb₀} | ==-refl {π ∙P pb₁} = refl

        honest-leak : honest-⅁ pb₀ s₀ ≡# honest-⅁ pb₁ s₁
        honest-leak rewrite otp-∙ pb₀ s₀ pb₁ s₁ check | sumRₚ-ext helper = refl

    -- Predicts b=b′
    cheater : ∀ b′ → Prover
    cheater b′ pb (rand (π , _)) b = pb′ b′ , ans b
      module Cheater where
        pb′ : ∀ b′ → Problem
        pb′ true  = easy-pb π
        pb′ false = π ∙P pb
        ans : ∀ b → Answer b
        ans true  = easy-sol π
        ans false = π

    -- If cheater predicts correctly, verifer accepts him
    cheater-accepted : ∀ b pb rₚ → (pb ⇄′ cheater b) b rₚ ≡ 1b
    cheater-accepted true  pb (rand (π , rₚ)) = check-easy π
    cheater-accepted false pb (rand (π , rₚ)) = ==-refl

    -- If cheater predicts incorrecty, verifier rejects him
    module CheaterRejected (pb : Problem)
                           (not-easy-sol : ∀ π → check (π ∙P pb) (easy-sol π) ≡ false)
                           (not-easy-pb  : ∀ π → ((π ∙P pb) == easy-pb π) ≡ false) where

        cheater-rejected : ∀ b rₚ → (pb ⇄′ cheater (not b)) b rₚ ≡ 0b
        cheater-rejected true  (rand (π , rₚ)) = not-easy-sol π
        cheater-rejected false (rand (π , rₚ)) = not-easy-pb π

-- -}
-- -}
-- -}
-- -}
-- -}
