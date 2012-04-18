module game where

open import Level using (Lift) renaming (_⊔_ to _L⊔_)
open import Function.NP
open import Data.Nat.NP hiding (_==_)
open import Data.Product
open import Data.Maybe.NP
open import Data.List
open import Data.List.Any
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open Membership-≡

{-
-- Game
data ⅁ ...
-}

{-
- cost
- non-det
- queries
- partial (like decryption with a mac)
-}

open import Data.Bits
open import flipbased-implem

Bits⟨_⟩→_ : ∀ {a} → ℕ → Set a → Set a
Bits⟨ n ⟩→ A = Bits n → A

data Strategy (☐_ : Set → Set) (R : Set) : ∀ k → Set₁ where
  say : R → Strategy ☐_ R 0
  ask : ∀ {k} {A : Set} → ☐ A → (A → Strategy ☐_ R k) → Strategy ☐_ R k
  rnd : ∀ {n k} {A : Set} → ↺ n A → (A → Strategy ☐_ R k) → Strategy ☐_ R (n + k)

run : ∀ {k R} → Strategy id R k → ↺ k R
run (say r)    = ⟪ r ⟫
run (ask a f)  = run (f a)
run (rnd nd f) = nd >>= (λ xs → run (f xs))

postulate
      Proba : Set
      Pr[_≡1] : ∀ {k} (EXP : ↺ k Bit) → Proba
      _≡1/2^_ : Proba → ℕ → Set
      Pr[toss≡1] : Pr[ toss ≡1] ≡1/2^ 1
      Pr[random≡_] : ∀ {n} (x : Bits n) → Pr[ ⟪ _==_ x · random ⟫ ≡1] ≡1/2^ n
      negligible-proba : Proba
      negligible-advantage-proba : Proba → Proba → Set

_is-negligible : Proba → Set
p is-negligible = negligible-advantage-proba p negligible-proba

negligible-advantage : ∀ {k} (EXP : Bit → ↺ k Bit) → Set
negligible-advantage EXP = negligible-advantage-proba Pr[ EXP 0b ≡1] Pr[ EXP 1b ≡1]

postulate
  negligible-advantage-xor : ∀ {k} (EXP₁ EXP₂ : ↺ k Bit) → EXP₁ ≡ ⟪ _xor_ 1b · EXP₂ ⟫ → negligible-advantage-proba Pr[ EXP₁ ≡1] Pr[ EXP₂ ≡1]

  -- whatch out
  negligible-advantage-trans : ∀ {p₁ p₂ p₃} → negligible-advantage-proba p₁ p₂ → negligible-advantage-proba p₂ p₃ → negligible-advantage-proba p₁ p₃

pattern looks-random = 0b
pattern not-random   = 1b

EXP : ∀ {a b} {A : Set a} {B : Set b} → Bit → (A → B) → (A × A → B)
EXP 0b f (x₀ , x₁) = f x₀
EXP 1b f (x₀ , x₁) = f x₁

module CryptoGames where

  module CipherGames (|K| |M| |C| : ℕ) where
    K = Bits |K|
    M = Bits |M|
    C = Bits |C|

    record SemSecAdv k : Set where
      constructor mk
      field
        {k₀ k₁}   : ℕ
        k≡k₀+k₁  : k ≡ k₀ + k₁
        gen-m₀m₁  : ↺ k₀ (M × M)
        stat-test : C → ↺ k₁ Bit

    mk′ : ∀ {k₀ k₁} → ↺ k₀ (M × M) → (C → ↺ k₁ Bit) → SemSecAdv (k₀ + k₁)
    mk′ = mk refl

    module DeterministicSemanticSecurity where
      runDetSemSec : ∀ {k} (enc : M → C) → SemSecAdv k → Bit → ↺ k Bit
      runDetSemSec enc (mk refl gen-m₀m₁ f) b = gen-m₀m₁ >>= λ m₀m₁ → f (EXP b enc m₀m₁)

      DetSemSecWinner : ∀ (enc : M → C) b {k} (Adv : SemSecAdv k) → ↺ k Set
      DetSemSecWinner enc b Adv = T↺ (runDetSemSec enc Adv b)

      DetSemSec : ∀ k (enc : M → C) → Set
      DetSemSec k enc = ∀ (Adv : SemSecAdv k) → negligible-advantage (runDetSemSec enc Adv)

      luckySemSec : SemSecAdv 1
      luckySemSec = mk′ ⟪ 0ⁿ , 0ⁿ ⟫ᴰ (λ _ → toss)

      -- see OTPDetSemSec

    module DeterministicCPASecurity where
      DetCPAAdv : ∀ k → Set₁
      DetCPAAdv k = ∀ {☐_} (enc : M × M → ☐ C) → Strategy ☐_ Bit k

      data DetCPAWinner (enc : M × M → C) b (ms : List (M × M)) : ∀ {k} (q : ℕ) → Strategy id Bit k → Set₁ where
        win : ∀ {q} → DetCPAWinner enc b ms q (say b)
        ask : ∀ {k q m₀m₁ f} → m₀m₁ ∉ ms → DetCPAWinner enc b (m₀m₁ ∷ ms) q (f (enc m₀m₁)) →
              DetCPAWinner enc b ms {k} (suc q) (ask (enc m₀m₁) f)
        rnd : ∀ {A : Set} {n k q bs} {r : ↺ n A} {f : A → _}
              → DetCPAWinner enc b ms {k} q (f bs) → DetCPAWinner enc b ms q (rnd r f)

      runDetCPA : ∀ {k} (enc : M → C) (Adv : DetCPAAdv k) → Bit → ↺ k Bit
      runDetCPA enc Adv b = run (Adv (EXP b enc))

      -- no use of CPAWinner
      DetCPASec : ∀ k (enc : M → C) → Set₁
      DetCPASec k enc = ∀ (Adv : DetCPAAdv k) → negligible-advantage (runDetCPA enc Adv)

    CPAAdv : ∀ k → Set₁
    CPAAdv k = ∀ {☐_} (enc : M × M → ☐ (↺ |K| C)) → Strategy ☐_ Bit k

    sem2CPAAdv : ∀ {k} → SemSecAdv k → CPAAdv (|K| + k)
    sem2CPAAdv (mk {k₀} {k₁} refl gen-m₀m₁ f) {☐_} enc =
      subst (Strategy ☐_ Bit) helper
        (rnd gen-m₀m₁ (λ m₀m₁ →
          ask (enc m₀m₁) (λ c →
            rnd c (λ c' → rnd (f c') say))))
      where open import Data.Nat.Properties
            open SemiringSolver
            helper : k₀ + (|K| + (k₁ + 0)) ≡ |K| + (k₀ + k₁)
            helper = solve 3 (λ k₀ |K| k₁ → k₀ :+ (|K| :+ (k₁ :+ con 0)) := |K| :+ (k₀ :+ k₁))
                             refl k₀ |K| k₁

    data CPAWinner (enc : M × M → ↺ |K| C) b : ∀ {k} q → Strategy id Bit k → Set₁ where
      win : ∀ {q} → CPAWinner enc b q (say b)
      ask : ∀ {k q m₀m₁ f} → CPAWinner enc b {k} q (f (enc m₀m₁)) →
            CPAWinner enc b (suc q) (ask (enc m₀m₁) f)
      rnd : ∀ {A : Set} {n k q bs} {r : ↺ n A} {f : A → _}
            → CPAWinner enc b {k} q (f bs) → CPAWinner enc b q (rnd r f)

    det : ∀ {k a b} {A : Set a} {B : Set b} → (A → B) → A → ↺ k B
    det f x = ⟪ f x ⟫

    runCPA : ∀ {k} (enc : M → ↺ |K| C) (Adv : CPAAdv k) → Bit → ↺ k Bit
    runCPA enc Adv b = run (Adv (EXP b enc))

    -- no use of CPAWinner
    CPASec : ∀ k (enc : M → ↺ |K| C) → Set₁
    CPASec k enc = ∀ (Adv : CPAAdv k) → negligible-advantage (runCPA enc Adv)

    SemSecWinner : ∀ (enc : M × M → ↺ |K| C) b k → SemSecAdv k → Set₁
    SemSecWinner enc b k Adv = CPAWinner enc b 1 (sem2CPAAdv Adv enc)

    runSemSec : ∀ {k} (enc : M → ↺ |K| C) → SemSecAdv k → Bit → ↺ (|K| + k) Bit
    runSemSec enc Adv = runCPA enc (sem2CPAAdv Adv)

    -- no use of SemSecWinner
    SemSec : ∀ k (enc : M → ↺ |K| C) → Set
    SemSec k enc = ∀ (Adv : SemSecAdv k) → negligible-advantage (runSemSec enc Adv)

    weakenWinner : ∀ {enc b k q₀ q₁} {s : Strategy id Bit k} → CPAWinner enc b q₀ s → CPAWinner enc b (q₀ + q₁) s
    weakenWinner win     = win
    weakenWinner (ask w) = ask (weakenWinner w)
    weakenWinner (rnd {n = n} {k} {bs = bs} w) = rnd {n = n} {k} {bs = bs} (weakenWinner w)

    CPA2Sem-correct : ∀ {enc b k q} {semAdv : SemSecAdv k}
                      → SemSecWinner enc b k semAdv → CPAWinner enc b (suc q) (sem2CPAAdv semAdv enc)
    CPA2Sem-correct = weakenWinner

  record Forgery {a} {A : Set a} (P : A → Set) (queries : List A) : Set a where
    field
      forgery         : A
      fresh-forgery   : forgery ∉ queries
      correct-forgery : P forgery
  open Forgery public

  module MACGames (|M| |Tag| : ℕ) where
    M = Bits |M|
    Tag = Bits |Tag|

    -- One might also want that the adversary sends the trials to the challenger.
    -- The challenger might then either end the game or maybe return the info to
    -- the adversary.
    MACAdv : Set₁
    MACAdv = ∀ {☐_} (mac : M → ☐ Tag) → Strategy ☐_ (M × Tag) 0

    -- or
    -- MACAdv = ∀ {☐_ Done} (mac : M → ☐ Tag) (submit : M × Tag → ☐ Done) → Strategy ☐_ Done

    -- or
    -- MACAdv = ∀ {☐_ Done} (mac : M → ☐ Tag)
    --                       (try : M × Tag → ☐ Bool)
    --                       (submit : M × Tag → ☐ Done) → Strategy ☐_ Done

    module MACGames' (mac : M → Tag) where
      CorrectMAC : M × Tag → Set
      CorrectMAC (m , t) = mac m ≡ t

      correctMAC? : M × Tag → Bool
      correctMAC? (m , t) = mac m == t

      data MACWinner (mts : List (M × Tag)) : (q : ℕ) → Strategy id (M × Tag) 0 → Set₁ where
        win : ∀ {q} (f : Forgery CorrectMAC mts) → MACWinner mts q (say (forgery f))
        ask : ∀ {m f q} → MACWinner ((m , mac m) ∷ mts) q (f (mac m))
                        → MACWinner mts (suc q) (ask (mac m) f)

      SecMAC : Set₁
      SecMAC = ∀ (A : MACAdv) → Pr[ ⟪ correctMAC? · run (A mac) ⟫ ≡1] ≡1/2^ |Tag| -- check that bound

  module CiphertextIntegrity (M C : Set) where
    CIAdv : Set₁
    CIAdv = ∀ {☐_} (enc : M → ☐ C) → Strategy ☐_ C 0

    module CiphertextIntegrity' (enc : M → C) (dec : C →? M) where
      CorrectCiphertext : C → Set
      CorrectCiphertext c = IsJust (dec c)

      data CIWinner (cs : List C) : (q : ℕ) → Strategy id C 0 → Set₁ where
        win : ∀ {q} (f : Forgery CorrectCiphertext cs) → CIWinner cs q (say (forgery f))
        ask : ∀ {m f q} → CIWinner (enc m ∷ cs) q (f (enc m))
                        → CIWinner cs (suc q) (ask (enc m) f)

  module AuthenticatedEncryption (|K| |M| |C| : ℕ) where
    open CipherGames |K| |M| |C|
    open CiphertextIntegrity M C

    data AERes : Set where
      distinguish   : Bit → AERes
      found-forgery : C → AERes

    AEAdv : Set₁
    AEAdv = ∀ {☐_} (enc : M × M → ☐ C) → Strategy ☐_ AERes 0

    CCAAdv : Set₁
    CCAAdv = ∀ {☐_} (enc : M × M → ☐ C) (dec : C → ☐ (Maybe M)) → Strategy ☐_ Bit 0

    module AE' (enc : M × M → C) (dec : C →? M) where
      open CiphertextIntegrity' (λ m → enc (m , m)) dec

      data AEWinner (cs : List C) b : (q : ℕ) → Strategy id AERes 0 → Set₁ where
        win-distinguish : ∀ {q} → AEWinner cs b q (say (distinguish b))
        win-forgery : ∀ {q} (f : Forgery CorrectCiphertext cs)
                       → AEWinner cs b q (say (found-forgery (forgery f)))
        ask : ∀ {m₀m₁ f q} → AEWinner cs b q (f (enc m₀m₁)) →
              AEWinner cs b (suc q) (ask (enc m₀m₁) f)

      data CCAWinner b : (q : ℕ) → Strategy id Bit 0 → Set₁ where
        win : ∀ {q} → CCAWinner b q (say b)
        ask-enc : ∀ {m₀m₁ f q} → CCAWinner b q (f (enc m₀m₁)) →
                    CCAWinner b (suc q) (ask (enc m₀m₁) f)
        ask-dec : ∀ {c f q} → CCAWinner b q (f (dec c)) →
                    CCAWinner b (suc q) (ask (dec c) f)

  -- CBC with rand IV is not CCA secure

      -- AE ⇒ CCA Secure

  module OTPDetSemSec {n} (key : Bits n) where
    open CipherGames n n n
    open DeterministicSemanticSecurity

    postulate
      OTPDetSemSec : ∀ {k} → DetSemSec k (OTP key)
{-
    OTPDetSemSec (mk refl gen-m₀m₁ stat-test) = {!!}
    -- DetSemSec k enc = ∀ (Adv : SemSecAdv k) → negligible-advantage (runDetSemSec enc Adv)
    -- runDetSemSec enc (mk refl gen-m₀m₁ f) b = gen-m₀m₁ >>= λ m₀m₁ → f (EXP b enc m₀m₁)

Pr[ runDetSemSec enc Adv b ≡ b ]
-}

  Enc : ∀ |K| |M| |C| → Set
  Enc |K| |M| |C| = Bits |K| → Bits |M| → Bits |C|

  module DerivedBlockCiphers
    {|K| |M| |C|} {E : Enc |K| |M| |C|}
    (E-sec : ∀ {k} key → CipherGames.DeterministicSemanticSecurity.DetSemSec |K| |M| |C| k (E key)) where

    open module CipherGames' {|M| |C|} = CipherGames |K| |M| |C|
    open DeterministicSemanticSecurity

    E₀ : Enc |K| |M| |C|
    E₀ k m = 1ⁿ ⊕ E k m

    postulate
      lem' : ∀ {k} (Adv : SemSecAdv k) b (f : Bits k → Bits |C|) → runDetSemSec {k} (_⊕_ 1ⁿ ∘ f) Adv b ≡ ⟪ _xor_ 1b · runDetSemSec f Adv b ⟫
    -- lem' Adv b f = {!!}

      lem'' : ∀ {k} (Adv : SemSecAdv k) b (f : Bits k → Bits |C|) → ⟪ _xor_ 1b · runDetSemSec {k} (_⊕_ 1ⁿ ∘ f) Adv b ⟫ ≡ runDetSemSec f Adv b
    -- lem'' Adv b f = {!!}

    -- postulate
    E₀-sec : ∀ key → DetSemSec |M| (E₀ key)
    E₀-sec key Adv = negligible-advantage-trans (negligible-advantage-xor (runDetSemSec (E₀ key) Adv 0b) (runDetSemSec (E key) Adv 0b) (lem' Adv 0b (E key))) (negligible-advantage-trans (E-sec key Adv) (negligible-advantage-xor (runDetSemSec (E key) Adv 1b) (runDetSemSec (E₀ key) Adv 1b) (sym (lem'' Adv 1b (E key)))))

    E₁ : Enc |K| |M| (1 + |C|)
    E₁ k m = 0∷ E k m

    -- E₁-adv : ∀ {k} key → SemSecAdv k (E key) → SemSecAdv k (E₁ key)
    -- E₁-adv key Adv = {!E-sec!}

    postulate
      E₁-sec : ∀ {k} key → DetSemSec k (E₁ key)
    -- E₁-sec key Adv = {!E-sec key ?!}

    -- runDetSemSec enc adv b ≈ runDetSemSec enc' adv b
