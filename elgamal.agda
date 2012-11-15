{-# OPTIONS --copatterns #-}
open import Type
open import Function
open import Data.Product
open import Data.Bool.NP as Bool
open import Data.Unit
open import Data.Maybe.NP
import Data.Fin.NP as Fin
open Fin using (Fin; zero; suc) renaming (#_ to ##_)
open import Data.Nat.NP hiding (_^_)
open import Data.Bits
import Data.Vec.NP as Vec
open Vec using (Vec; []; _∷_; _∷ʳ_; allFin; lookup) renaming (map to vmap)
open import Algebra.FunctionProperties
open import Relation.Binary.PropositionalEquality as ≡
import cont as cont
open cont using (Cont; ContA)
open import sum

module elgamal where

data `★ : ★ where
  `⊤   : `★
  `X   : `★
  _`×_ : `★ → `★ → `★
infixr 2 _`×_

module Univ (X : ★) where
    El : `★ → ★
    El `⊤         = ⊤
    El `X         = X
    El (u₀ `× u₁) = El u₀ × El u₁

    record ↺ (R : `★) (A : ★) : ★ where
      constructor mk
      field
        run↺ : El R → A
    open ↺ public

    EXP : (R : `★) → ★
    EXP R = ↺ R Bit

    Det : ★ → ★
    Det = ↺ `⊤

    μU : SumProp X → ∀ u → SumProp (El u)
    μU μX `⊤         = μ⊤
    μU μX `X         = μX
    μU μX (u₀ `× u₁) = μU μX u₀ ×μ μU μX u₁

module EntropySmoothing
  (M    : ★)        -- Message
  (Hash : ★)
  (ℋ   : M → Hash) -- Hashing function
  (Rₐ   : ★)        -- Adversary randomness
  where

  -- Entropy smoothing adversary
  ESAdv : ★
  ESAdv = Rₐ → Hash → Bit

  -- The randomness universe needed for the following games
  R : ★
  R = M × Hash × Rₐ

  -- In this game we always use ℋ on a random message
  ES⅁₀ : ESAdv → R → Bit
  ES⅁₀ A (m , _ , rₐ) = A rₐ (ℋ m)

  -- In this game we just retrun a random Hash value
  ES⅁₁ : ESAdv → R → Bit
  ES⅁₁ A (_ , h , rₐ) = A rₐ h

  ES⅁ : ESAdv → Bit → R → Bit
  ES⅁ A b r = (case b 0→ ES⅁₀ 1→ ES⅁₁) A r

module EntropySmoothingWithKey
  (M    : ★)
  (Key  : ★)
  (Hash : ★)
  (ℋ   : Key → M → Hash) -- Hashing function
  (Rₐ   : ★)              -- Adversary randomness
  where

  -- Entropy smoothing adversary
  ESAdv : ★
  ESAdv = Rₐ → Key → Hash → Bit

  -- The randomness universe needed for the following games
  R : ★
  R = Key × M × Hash × Rₐ

  -- In this game we always use ℋ on a random message
  ES⅁₀ : ESAdv → R → Bit
  ES⅁₀ A (k , m , _ , rₐ) = A rₐ k (ℋ k m)

  -- In this game we just retrun a random Hash value
  ES⅁₁ : ESAdv → R → Bit
  ES⅁₁ A (k , _ , h , rₐ) = A rₐ k h

  ES⅁ : ESAdv → Bit → R → Bit
  ES⅁ A b r = (case b 0→ ES⅁₀ 1→ ES⅁₁) A r

module ℤq-count
  (ℤq : ★)
  (_⊞_ : ℤq → ℤq → ℤq)
  (μℤq : SumProp ℤq)
  (sumℤq-⊞-lem : ∀ x f → sum μℤq (f ∘ _⊞_ x) ≡ sum μℤq f)
  where

  -- open Sum
  open Univ ℤq public
  open `★ public renaming (`X to `ℤq)

  #_ : ∀ {u} → ↺ u Bit → ℕ
  #_ {u} f = sum (μU μℤq u) (Bool.toℕ ∘ run↺ f)

  #q_ : Count ℤq
  #q_ = count μℤq

  ⁇ : ∀ R → ↺ R (El R)
  run↺ (⁇ _) = id

  pure↺ : ∀ {R A} → A → ↺ R A
  run↺ (pure↺ x) r = x -- turning r to _ produce an error

  ⟪_⟫ : ∀ {R A} → A → ↺ R A
  ⟪_⟫ = pure↺

  {-
  ⟪_⟫ᴰ : ∀ {a} {A : Set a} → A → Det A
  ⟪_⟫ᴰ = pureᴰ
  -}

  map↺ : ∀ {A B R} → (A → B) → ↺ R A → ↺ R B
  run↺ (map↺ f x) r = f (run↺ x r)

  infixl 4 _⊛_
  _⊛_ : ∀ {R S A B} → ↺ R (A → B) → ↺ S A → ↺ (R `× S) B
  run↺ (af ⊛ ax) rs = run↺ af (proj₁ rs) (run↺ ax (proj₂ rs))

  ⟪_·_⟫ : ∀ {A B R} → (A → B) → ↺ R A → ↺ R B
  ⟪ f · x ⟫ = map↺ f x

  ⟪_·_·_⟫ : ∀ {A B C} {R S} →
              (A → B → C) → ↺ R A → ↺ S B → ↺ (R `× S) C
  ⟪ f · x · y ⟫ = map↺ f x ⊛ y

  _⟨⊞⟩_ : ∀ {R S} → ↺ R ℤq → ↺ S ℤq → ↺ (R `× S) ℤq
  x ⟨⊞⟩ y = ⟪ _⊞_ · x · y ⟫

  ⟨_⊞⟩_ : ∀ {R} → ℤq → ↺ R ℤq → ↺ R ℤq
  ⟨ x ⊞⟩ y = ⟪ _⊞_ x · y ⟫

  infix 4 _≈↺_ _≈ᴬ_
  _≈↺_ : ∀ {R : `★} (f g : EXP R) → ★
  _≈↺_ = _≡_ on #_

  _≈ᴬ_ : ∀ {A R} (f g : ↺ R A) → Set _
  _≈ᴬ_ {A} f g = ∀ (Adv : A → Bit) → ⟪ Adv · f ⟫ ≈↺ ⟪ Adv · g ⟫

  lem : ∀ x → ⟨ x ⊞⟩ (⁇ `ℤq) ≈ᴬ ⁇ _
  lem x Adv = sumℤq-⊞-lem x (Bool.toℕ ∘ Adv)

  -- ∀ (A : ℤq → Bit) → # (A ⁇)

open Fin.Modulo renaming (sucmod to [suc])

{-
module ℤq-implem (q-2 : ℕ) where
  q : ℕ
  q = 2 + q-2

  ℤq : ★
  ℤq = Fin q

  [0] : ℤq
  [0] = zero

  [1] : ℤq
  [1] = suc zero
-}
module ℤq-implem (q : ℕ) ([0]' [1]' : Fin q) where
  -- open Sum
  ℤq : ★
  ℤq = Fin q

  [0] : ℤq
  [0] = [0]'

  [1] : ℤq
  [1] = [1]'

  _ℕ⊞_ : ℕ → ℤq → ℤq
  zero  ℕ⊞ n = n
  suc m ℕ⊞ n = m ℕ⊞ ([suc] n)
  {-
  zero  ℕ⊞ n = n
  suc m ℕ⊞ n = [suc] (m ℕ⊞ n)
  -}

  _⊞_ : ℤq → ℤq → ℤq
  m ⊞ n = Fin.toℕ m ℕ⊞ n

  _ℕ⊠_ : ℕ → ℤq → ℤq
  zero  ℕ⊠ n = [0]
  suc m ℕ⊠ n = n ⊞ (m ℕ⊠ n)

  _⊠_ : ℤq → ℤq → ℤq
  m ⊠ n = Fin.toℕ m ℕ⊠ n

  _[^]ℕ_ : ℤq → ℕ → ℤq
  m [^]ℕ zero  = [1]
  m [^]ℕ suc n = m ⊠ (m [^]ℕ n)

  _[^]_ : ℤq → ℤq → ℤq
  m [^] n = m [^]ℕ (Fin.toℕ n)

  μℤq : SumProp ℤq
  μℤq = μFin q

  allℤq : Vec ℤq q
  allℤq = allFin q

  {-
  sumℤq : Sum ℤq
  sumℤq f = Vec.sum (vmap f allℤq)
  -}

  sumℤq-[suc]-lem : ∀ f → sum μℤq (f ∘ [suc]) ≡ sum μℤq f
  sumℤq-[suc]-lem f rewrite ≡.sym (Vec.sum-map-rot₁ f allℤq)
                          | Vec.map-∘ f [suc] allℤq
                          | rot₁-map-sucmod q
                          = refl

  --  comm-[suc]-ℕ⊞ : ∀ m n → [suc] (m ℕ⊞ n) ≡ m ℕ⊞ ([suc] n)

  sumℤq-ℕ⊞-lem : ∀ m f → sum μℤq (f ∘ _ℕ⊞_ m) ≡ sum μℤq f
  sumℤq-ℕ⊞-lem zero f = refl
  sumℤq-ℕ⊞-lem (suc m) f rewrite sumℤq-[suc]-lem (f ∘ _ℕ⊞_ m)
                               | sumℤq-ℕ⊞-lem m f = refl

  sumℤq-⊞-lem : ∀ m f → sum μℤq (f ∘ _⊞_ m) ≡ sum μℤq f
  sumℤq-⊞-lem = sumℤq-ℕ⊞-lem ∘ Fin.toℕ

  {-
module G-implem (p q : ℕ) (g' : Fin p) (0[p] 1[p] : Fin p) (0[q] 1[q] : Fin q) where
  open ℤq-implem q 0[q] 1[q] public
  open ℤq-implem p 0[p] 1[p] public using () renaming (ℤq to G; _⊠_ to _∙_; _[^]ℕ_ to _^[p]_)

  g : G
  g = g'

  _^_ : G → ℤq → G
  x ^ n = x ^[p] Fin.toℕ n

  g^_ : ℤq → G
  g^ n = g ^ n

  {-
  g^-inj : ∀ m n → g^ m ≡ g^ n → m ≡ n
  g^-inj = {!!}
  -}

module G-count
  (ℤq : ★)
  (_⊞_ : ℤq → ℤq → ℤq)
  (μℤq : SumProp ℤq)
  (sumℤq-⊞-lem : ∀ x f → sum μℤq (f ∘ _⊞_ x) ≡ sum μℤq f)
  (G : ★)
  (g : G)
  (_^_ : G → ℤq → G)
  (_∙_ : G → G → G)
  where

  g^_ : ℤq → G
  g^ n = g ^ n

  open ℤq-count ℤq _⊞_ μℤq sumℤq-⊞-lem

  ⁇G : ↺ `ℤq G
  run↺ ⁇G x = g^ x

  #G : Count G
  #G f = #q (f ∘ g^_)

  {-
  #G-∙ : ∀ f m → #G (f ∘ _∙_ m) ≡ #G f
  #G-∙ f m = {!!}
  -}

module DDH
  (ℤq  : ★)
  (_⊠_ : ℤq → ℤq → ℤq)
  (G   : ★)
  (g^_ : ℤq → G)
  where
    DDHAdv : ★ → ★
    DDHAdv R = R → G → G → G → Bit

    DDH⅁₀ : ∀ {R} {_I : ★} → DDHAdv R → (R × ℤq × ℤq × _I) → Bit
    DDH⅁₀ d (r , x , y , _) = d r (g^ x) (g^ y) (g^ (x ⊠ y))

    DDH⅁₁ : ∀ {R} → DDHAdv R → (R × ℤq × ℤq × ℤq) → Bit
    DDH⅁₁ d (r , x , y , z) = d r (g^ x) (g^ y) (g^ z)

    DDH⅁ : ∀ {R} → DDHAdv R → Bit → (R × ℤq × ℤq × ℤq) → Bit
    DDH⅁ d b = (case b 0→ DDH⅁₀ 1→ DDH⅁₁) d

    -- DDH⅁′ : ∀ {R} → DDHAdv R → (Bit × ℤq × ℤq × ℤq × R) → Bit
    -- DDH⅁′ d (b , x , y , z , r) = DDH⅁ d b (x , y , z , r)

    module With↺ where
        open Univ ℤq
        open `★ public renaming (`X to `ℤq)
        DDHAdv↺ : `★ → ★
        DDHAdv↺ R = G → G → G → ↺ R Bit
        DDH⅁₀↺ : ∀ {R _I} → DDHAdv↺ R → ↺ (R `× `ℤq `× `ℤq `× _I) Bit
        run↺ (DDH⅁₀↺ d) = DDH⅁₀ (λ a b c d → run↺ (d b c d) a)

module El-Gamal-Generic
  (ℤq : ★)
  (_⊠_ : ℤq → ℤq → ℤq)
  (G : ★)
  (g : G)
  (_^_ : G → ℤq → G)
  (Message : ★)
  (_∙_ : G → Message → Message)

  -- Required for decryption
  (_/_ : Message → G → Message)

  -- Required for the correctness proof
  (/-∙ : ∀ x y → (x ∙ y) / x ≡ y)
  (comm-^   : ∀ α x y → (α ^ x)^ y ≡ (α ^ y)^ x)

  -- Required for the security proof
  (dist-^-⊠ : ∀ α x y → α ^ (x ⊠ y) ≡ (α ^ x) ^ y)
  (μℤq : SumProp ℤq)
  (Rₐ : ★)
  (μRₐ : SumProp Rₐ)
  where

    g^_ : ℤq → G
    g^ x = g ^ x

    -- gˣ is the pk
    -- x is the sk

    PubKey = G
    SecKey = ℤq
    KeyPair = PubKey × SecKey
    CipherText = G × Message

    M = Message
    C = CipherText

    KeyGen : ℤq → KeyPair
    KeyGen x = (g^ x , x)

    -- KeyGen↺ : ↺ ℤq KeyPair
    -- KeyGen↺ = mk KeyGen

    Enc : PubKey → Message → ℤq → CipherText
    Enc gˣ m y = gʸ , ζ where
      gʸ = g^ y
      δ = gˣ ^ y
      ζ = δ ∙ m

    -- Enc↺ : PubKey → Message → ↺ ℤq CipherText
    -- Enc↺ gˣ m = mk (Enc gˣ m)

    Dec : SecKey → CipherText → Message
    Dec x (gʸ , ζ) = ζ / (gʸ ^ x)

    EncAdv : ★ → ★
    EncAdv Rₐ = (Rₐ → PubKey → Bit → M)
              × (Rₐ → PubKey → C → Bit)

    SS⅁ : ∀ {Rₐ _I : ★} → EncAdv Rₐ → Bit → (Rₐ × ℤq × ℤq × _I) → Bit
    SS⅁ (m , d) b (rₐ , x , y , z) =
      let pk = proj₁ (KeyGen x) in
      d rₐ pk (Enc pk (m rₐ pk b) y)

      -- Unused
    Game : (i : Bit) → ∀ {Rₐ} → EncAdv Rₐ → (Bit × Rₐ × ℤq × ℤq × ℤq) → Bit
    Game i (m , d) (b , rₐ , x , y , z) = b ==ᵇ d rₐ gˣ (gʸ , ζ)
      where gˣ = g^ x
            gʸ = g^ y
            δ  = gˣ ^ case i 0→ y 1→ z
            ζ  = δ ∙ m rₐ gˣ b

    {-
    Game-0b≡Game0 : ∀ {Rₐ} → Game 0b ≡ Game0 {Rₐ}
    Game-0b≡Game0 = refl
      -}

    open DDH ℤq _⊠_ G g^_ public

    OTP⅁ : ∀ {R : ★} → (R → G → Message) → (R → G → G → Message → Bit)
                     → (R × ℤq × ℤq × ℤq) → Bit
    OTP⅁ M d (r , x , y , z) = d r gˣ gʸ (gᶻ ∙ M r gˣ)
      where gˣ = g^ x
            gʸ = g^ y
            gᶻ = g^ z

    TrA : ∀ {Rₐ} → Bit → EncAdv Rₐ → DDHAdv Rₐ
    TrA b (m , d) rₐ gˣ gʸ gˣʸ = d rₐ gˣ (gʸ , gˣʸ ∙ m rₐ gˣ b)

    projM : ∀ {Rₐ} → EncAdv Rₐ → Bit → Rₐ → G → Message
    projM (m , _) b rₐ gˣ = m rₐ gˣ b

    projD : ∀ {Rₐ} → EncAdv Rₐ → Rₐ → G → G → Message → Bit
    projD (_ , d) rₐ gˣ gʸ gᶻ∙M = d rₐ gˣ (gʸ , gᶻ∙M)

    like-SS⅁ : ∀ {Rₐ _I : ★} → EncAdv Rₐ → Bit → (Rₐ × ℤq × ℤq × _I) → Bit
    like-SS⅁ (m , d) b (rₐ , x , y , _z) =
      d rₐ gˣ (gʸ , (gˣ ^ y) ∙ m rₐ gˣ b)
      where gˣ = g^ x
            gʸ = g^ y

    SS⅁≡like-SS⅁ : ∀ {R _I} → SS⅁ {R} {_I} ≡ like-SS⅁
    SS⅁≡like-SS⅁ = refl

    -- open Sum

    R = Rₐ × ℤq × ℤq × ℤq
    μR : SumProp R
    μR = μRₐ ×μ μℤq ×μ μℤq ×μ μℤq

    #R_ : Count R
    #R_ = count μR

    #q_ : Count ℤq
    #q_ = count μℤq

    _≈q_ : (f g : ℤq → Bit) → ★
    f ≈q g = #q f ≡ #q g

    _≈R_ : (f g : R → Bit) → ★
    f ≈R g = #R f ≡ #R g

    functional-correctness : ∀ x y m → Dec x (Enc (g^ x) m y) ≡ m
    functional-correctness x y m rewrite comm-^ g x y | /-∙ (g^ y ^ x) m = refl

    module Proof
        (ddh-hyp : (A : DDHAdv Rₐ) → DDH⅁ A 0b ≈R DDH⅁ A 1b)
        (otp-lem : ∀ (A : Message → Bit) m₀ m₁ → (λ x → A (g^ x ∙ m₀)) ≈q (λ x → A (g^ x ∙ m₁)))
        (A : EncAdv Rₐ) (b : Bit)
      where

        OTP⅁-lem : ∀ d M₀ M₁ → OTP⅁ M₀ d ≈R OTP⅁ M₁ d
        OTP⅁-lem d M₀ M₁ = sum-ext μRₐ (λ r →
                             sum-ext μℤq (λ x →
                               sum-ext μℤq (λ y →
                                 pf r x y)))
          where
          f0 = λ M r x y z → OTP⅁ M d (r , x , y , z)
          f1 = λ M r x y → sum μℤq (Bool.toℕ ∘ f0 M r x y)
          f2 = λ M r x → sum μℤq (f1 M r x)
          f3 = λ M r → sum μℤq (f2 M r)
          pf : ∀ r x y → f1 M₀ r x y ≡ f1 M₁ r x y
          pf r x y = pf'
            where gˣ = g^ x
                  gʸ = g^ y
                  m₀ = M₀ r gˣ
                  m₁ = M₁ r gˣ
                  f5 = λ M z → d r gˣ gʸ (g^ z ∙ M)
                  pf' : f5 m₀ ≈q f5 m₁
                  pf' rewrite otp-lem (d r gˣ gʸ) m₀ m₁ = refl

        Aᵇ = TrA b A
        A¬ᵇ = TrA (not b) A

        pf0,5 : SS⅁ A b ≗ DDH⅁ Aᵇ 0b
        pf0,5 (r , x , y , z) rewrite dist-^-⊠ g x y = refl

        pf1 : SS⅁ A b ≈R DDH⅁ Aᵇ 0b
        pf1 = sum-ext μR (cong Bool.toℕ ∘ pf0,5)

        pf2 : DDH⅁ Aᵇ 0b ≈R DDH⅁ Aᵇ 1b
        pf2 = ddh-hyp Aᵇ

        pf2,5 : DDH⅁ Aᵇ 1b ≡ OTP⅁ (projM A b) (projD A)
        pf2,5 = refl

        pf3 : DDH⅁ Aᵇ 1b ≈R DDH⅁ A¬ᵇ 1b
        pf3 = OTP⅁-lem (projD A) (projM A b) (projM A (not b))

        pf4 : DDH⅁ A¬ᵇ 1b ≈R DDH⅁ A¬ᵇ 0b
        pf4 = ≡.sym (ddh-hyp A¬ᵇ)

        pf4,5 : SS⅁ A (not b) ≗ DDH⅁ A¬ᵇ 0b
        pf4,5 (r , x , y , z) rewrite dist-^-⊠ g x y = refl

        pf5 : SS⅁ A (not b) ≈R DDH⅁ A¬ᵇ 0b
        pf5 = sum-ext μR (cong Bool.toℕ ∘ pf4,5)

        final : SS⅁ A b ≈R SS⅁ A (not b)
        final rewrite pf1 | pf2 | pf3 | pf4 | pf5 = refl

module El-Gamal-Base
    (ℤq : ★)
    (_⊠_ : ℤq → ℤq → ℤq)
    (G : ★)
    (g : G)
    (_^_ : G → ℤq → G)
    (_∙_ : G → G → G)

    -- Required for decryption
    (_/_ : G → G → G)

    -- Required for the correctness proof
    (/-∙ : ∀ x y → (x ∙ y) / x ≡ y)
    (comm-^   : ∀ α x y → (α ^ x)^ y ≡ (α ^ y)^ x)
    
    {-
    (_⁻¹ : G → G)
    (⁻¹-inverse : ∀ x → x ⁻¹ ∙ x ≡ 1G)
    -}

    -- Required for the proof
    (dist-^-⊠ : ∀ α x y → α ^ (x ⊠ y) ≡ (α ^ x) ^ y)
    (μℤq : SumProp ℤq)
    (Rₐ : ★)
    (μRₐ : SumProp Rₐ)
    where

    open El-Gamal-Generic ℤq _⊠_ G g _^_ G _∙_
           _/_ /-∙ comm-^
           dist-^-⊠ μℤq Rₐ μRₐ public

    module OTP⅁-LEM
            (otp-lem1 : ∀ (A : G → Bit) m → (λ x → A (g^ x ∙ m)) ≈q (λ x → A (g^ x)))
      where

        otp-lem : ∀ (A : G → Bit) m₀ m₁ → (λ x → A (g^ x ∙ m₀)) ≈q (λ x → A (g^ x ∙ m₁))
        otp-lem A m₀ m₁ rewrite otp-lem1 A m₀ | otp-lem1 A m₁ = refl

module El-Gamal-Hashed
    (ℤq : ★)
    (_⊠_ : ℤq → ℤq → ℤq)
    (G : ★)
    (g : G)
    (_^_ : G → ℤq → G)
    -- (HKey : ★)
    (|M| : ℕ)
    (ℋ : {-HKey →-} G → Bits |M|)

    -- (/-∙ : ∀ x y → (x ∙ y) / x ≡ y)
    (comm-^   : ∀ α x y → (α ^ x)^ y ≡ (α ^ y)^ x)

    -- Required for the proof
    (dist-^-⊠ : ∀ α x y → α ^ (x ⊠ y) ≡ (α ^ x) ^ y)
    (μℤq : SumProp ℤq)
    (Rₐ : ★)
    (μRₐ : SumProp Rₐ)
    where

    Message = Bits |M|

    ℋ⟨_⟩⊕_ : G → Message → Message
    ℋ⟨ δ ⟩⊕ m = ℋ δ ⊕ m

    _/_ : Message → G → Message
    _/_ = {!!}

    {-
    /-∙ : ∀ x y → (x ∙ y) / x ≡ y
    /-∙ x y = ?

    open El-Gamal-Generic ℤq _⊠_ G g _^_ Message ℋ⟨_⟩⊕_ _/_ {!!} {!!}
           dist-^-⊠ sumℤq sumℤq-ext Rₐ sumRₐ sumRₐ-ext public
           -}

           {-
    OTP⅁-lem : ∀ d M₀ M₁ → OTP⅁ M₀ d ≈R OTP⅁ M₁ d
    OTP⅁-lem = ?
    -}

module ⟨ℤp⟩★ p-3 {- p is prime -} (`Rₐ : `★) where
  p : ℕ
  p = 3 + p-3

  q : ℕ
  q = p ∸ 1

  module G = G-implem p q (## 2) (## 0) (## 1) (## 0) (## 1)
  open G

  postulate
    _⁻¹ : G → G
    dist-^-⊠ : ∀ α x y → α ^ (x ⊠ y) ≡ (α ^ x) ^ y

  open ℤq-count ℤq _⊞_ μℤq sumℤq-⊞-lem

  Rₐ = El `Rₐ
  sumRₐ = sum `Rₐ
  sumRₐ-ext = sum-ext `Rₐ

  module EB = El-Gamal-Base _ _⊠_ G g _^_ _∙_ _⁻¹ dist-^-⊠ sumℤq sumℤq-ext Rₐ sumRₐ sumRₐ-ext
  open EB hiding (g^_)

  postulate
    ddh-hyp : (A : DDHAdv Rₐ) → DDH⅁ A 0b ≈R DDH⅁ A 1b
    otp-lem : ∀ (A : G → Bit) m → (λ x → A (g^ x ∙ m)) ≈q (λ x → A (g^ x))

  open OTP⅁-LEM otp-lem

  {-
  final : ∀ A → SS⅁ A 0b ≈R SS⅁ A 1b
  final A = Proof.final ddh-hyp OTP⅁-lem A 0b
  -}

module ⟨ℤ11⟩★ = ⟨ℤp⟩★ (11 ∸ 3)
                   `X -- the amount of adversary randomness

        -- -}
        -- -}
        -- -}
        -- -}
        -- -}
        -- -}
