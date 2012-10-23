{-# OPTIONS --copatterns #-}
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

module elgamal where

private
    ★₁ : Set₂
    ★₁ = Set₁

    ★ : ★₁
    ★ = Set

[0→_,1→_] : ∀ {a} {A : Set a} → A → A → Bit → A
[0→ e₀ ,1→ e₁ ] b = if b then e₁ else e₀

case_0→_1→_ : ∀ {a} {A : Set a} → Bit → A → A → A
case b 0→ e₀ 1→ e₁ = if b then e₁ else e₀

module Sum where
    Sum : ★ → ★
    Sum A = (A → ℕ) → ℕ 

    Count : ★ → ★
    Count A = (A → Bit) → ℕ 

    SumExt : ∀ {A} → Sum A → ★
    SumExt sumA = ∀ {f g} → f ≗ g → sumA f ≡ sumA g

    sumToCount : ∀ {A} → Sum A → Count A
    sumToCount sumA f = sumA (Bool.toℕ ∘ f)

    sum⊤ : Sum ⊤
    sum⊤ f = f _

    sum⊤-ext : SumExt sum⊤
    sum⊤-ext f≗g = f≗g _

    sumBit : Sum Bit
    sumBit f = f 0b + f 1b

    sumBit-ext : SumExt sumBit
    sumBit-ext f≗g rewrite f≗g 0b | f≗g 1b = refl

    -- liftM2 _,_ in the continuation monad
    sumProd : ∀ {A B} → Sum A → Sum B → Sum (A × B)
    sumProd sumA sumB f = sumA (λ x₀ →
                           sumB (λ x₁ →
                             f (x₀ , x₁)))

    sumProd-ext : ∀ {A B} {sumA : Sum A} {sumB : Sum B} →
                  SumExt sumA → SumExt sumB → SumExt (sumProd sumA sumB)
    sumProd-ext sumA-ext sumB-ext f≗g = sumA-ext (λ x → sumB-ext (λ y → f≗g (x , y)))

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
  (sumℤq : Sum.Sum ℤq)
  (sumℤq-ext : Sum.SumExt sumℤq)
  (sumℤq-⊞-lem : ∀ x f → sumℤq (f ∘ _⊞_ x) ≡ sumℤq f)
  where

  open Sum
  open Univ ℤq public
  open `★ public renaming (`X to `ℤq)

  sum : ∀ u → Sum (El u)
  sum `⊤         = sum⊤
  sum `X         = sumℤq
  sum (u₀ `× u₁) = sumProd (sum u₀) (sum u₁)

  sum-ext : ∀ u → SumExt (sum u)
  sum-ext `⊤         = sum⊤-ext
  sum-ext `X         = sumℤq-ext
  sum-ext (u₀ `× u₁) = sumProd-ext (sum-ext u₀) (sum-ext u₁)

  #_ : ∀ {u} → ↺ u Bit → ℕ
  #_ {u} f = sum u (Bool.toℕ ∘ run↺ f)

  #q_ : Count ℤq
  #q_ = sumToCount sumℤq

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
  open Sum
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

  allℤq : Vec ℤq q
  allℤq = allFin q

  sumℤq : Sum ℤq
  sumℤq f = Vec.sum (vmap f allℤq)

  sumℤq-[suc]-lem : ∀ f → sumℤq (f ∘ [suc]) ≡ sumℤq f
  sumℤq-[suc]-lem f rewrite ≡.sym (Vec.sum-map-rot₁ f allℤq)
                          | Vec.map-∘ f [suc] allℤq
                          | rot₁-map-sucmod q
                          = refl

  --  comm-[suc]-ℕ⊞ : ∀ m n → [suc] (m ℕ⊞ n) ≡ m ℕ⊞ ([suc] n)

  sumℤq-ℕ⊞-lem : ∀ m f → sumℤq (f ∘ _ℕ⊞_ m) ≡ sumℤq f
  sumℤq-ℕ⊞-lem zero f = refl
  sumℤq-ℕ⊞-lem (suc m) f rewrite sumℤq-[suc]-lem (f ∘ _ℕ⊞_ m)
                               | sumℤq-ℕ⊞-lem m f = refl

  sumℤq-⊞-lem : ∀ m f → sumℤq (f ∘ _⊞_ m) ≡ sumℤq f
  sumℤq-⊞-lem = sumℤq-ℕ⊞-lem ∘ Fin.toℕ

  vmap-ext : ∀ {A B : ★} {f g : A → B} {n} → f ≗ g → vmap f ≗ vmap {n = n} g
  vmap-ext f≗g [] = refl
  vmap-ext f≗g (x ∷ xs) rewrite f≗g x | vmap-ext f≗g xs = refl

  sumℤq-ext : SumExt sumℤq
  sumℤq-ext f≗g rewrite vmap-ext f≗g allℤq = refl

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
  (sumℤq : Sum.Sum ℤq)
  (sumℤq-ext : Sum.SumExt sumℤq)
  (sumℤq-⊞-lem : ∀ x f → sumℤq (f ∘ _⊞_ x) ≡ sumℤq f)
  (G : ★)
  (g : G)
  (_^_ : G → ℤq → G)
  (_∙_ : G → G → G)
  where

  g^_ : ℤq → G
  g^ n = g ^ n

  open Sum
  open ℤq-count ℤq _⊞_ sumℤq sumℤq-ext sumℤq-⊞-lem

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
    DDH⅁₀ D (r , x , y , _) = D r (g^ x) (g^ y) (g^ (x ⊠ y))

    DDH⅁₁ : ∀ {R} → DDHAdv R → (R × ℤq × ℤq × ℤq) → Bit
    DDH⅁₁ D (r , x , y , z) = D r (g^ x) (g^ y) (g^ z)

    DDH⅁ : ∀ {R} → DDHAdv R → Bit → (R × ℤq × ℤq × ℤq) → Bit
    DDH⅁ D b = (case b 0→ DDH⅁₀ 1→ DDH⅁₁) D

    -- DDH⅁′ : ∀ {R} → DDHAdv R → (Bit × ℤq × ℤq × ℤq × R) → Bit
    -- DDH⅁′ D (b , x , y , z , r) = DDH⅁ D b (x , y , z , r)

    module With↺ where
        open Univ ℤq
        open `★ public renaming (`X to `ℤq)
        DDHAdv↺ : `★ → ★
        DDHAdv↺ R = G → G → G → ↺ R Bit
        DDH⅁₀↺ : ∀ {R _I} → DDHAdv↺ R → ↺ (R `× `ℤq `× `ℤq `× _I) Bit
        run↺ (DDH⅁₀↺ D) = DDH⅁₀ (λ a b c d → run↺ (D b c d) a)

module El-Gamal-Generic
  (ℤq : ★)
  (_⊠_ : ℤq → ℤq → ℤq)
  (G : ★)
  (g : G)
  (_^_ : G → ℤq → G)
  (Message : ★)
  (_⊕_ : G → Message → Message)
  (_⊕⁻¹_ : G → Message → Message)
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
      ζ = δ ⊕ m

    -- Enc↺ : PubKey → Message → ↺ ℤq CipherText
    -- Enc↺ gˣ m = mk (Enc gˣ m)

    Dec : SecKey → CipherText → Message
    Dec x (gʸ , ζ) = (gʸ ^ x) ⊕⁻¹ ζ

    EncAdv : ★ → ★
    EncAdv R = (R → PubKey → Bit → M) × (R → PubKey → C → Bit)

    SS⅁ : ∀ {R _I : ★} → EncAdv R → Bit → (R × ℤq × ℤq × _I) → Bit
    SS⅁ (m , D) b (r , x , y , z) =
      let pk = proj₁ (KeyGen x) in
      D r pk (Enc pk (m r pk b) y)

    Game : (i : Bit) → ∀ {R} → EncAdv R → (Bit × R × ℤq × ℤq × ℤq) → Bit
    Game i (m , D) (b , r , x , y , z) =
      let gˣ = g^ x
          gʸ = g^ y
          δ  = gˣ ^ case i 0→ y 1→ z
          ζ  = δ ⊕ m r gˣ b
      in b ==ᵇ D r gˣ (gʸ , ζ)

    {-
    Game-0b≡Game0 : ∀ {R} → Game 0b ≡ Game0 {R}
    Game-0b≡Game0 = refl
      -}

    open DDH ℤq _⊠_ G g^_ public

    -- Game0 ≈ Game 0b
    -- Game1 = Game 1b

    -- Game0 ≤ ε
    -- Game1 ≡ 0

    OTP⅁ : ∀ {R : ★} → (R → G → Message) → (R → G → G → Message → Bit)
                     → (R × ℤq × ℤq × ℤq) → Bit
    OTP⅁ M D (r , x , y , z) = D r gˣ gʸ (gᶻ ⊕ M r gˣ)
      where gˣ = g^ x
            gʸ = g^ y
            gᶻ = g^ z

    TrA : ∀ {R} → Bit → EncAdv R → DDHAdv R
    TrA b (m , D) r gˣ gʸ gˣʸ = D r gˣ (gʸ , gˣʸ ⊕ m r gˣ b)

module El-Gamal-Base
    (ℤq : ★)
    (_⊠_ : ℤq → ℤq → ℤq)
    (G : ★)
    (g : G)
    (_^_ : G → ℤq → G)
    (_⁻¹ : G → G)
    (_∙_ : G → G → G)
    where

    _/_ : G → G → G
    x / y = x ∙ (y ⁻¹)
    open El-Gamal-Generic ℤq _⊠_ G g _^_ G _∙_ (flip _/_) public

    like-SS⅁ : ∀ {R _I : ★} → EncAdv R → Bit → (R × ℤq × ℤq × _I) → Bit
    like-SS⅁ (m , D) b (r , x , y , _z) =
      D r gˣ (gʸ , (gˣ ^ y) ∙ m r gˣ b)
      where gˣ = g^ x
            gʸ = g^ y

    SS⅁≡like-SS⅁ : ∀ {R _I} → SS⅁ {R} {_I} ≡ like-SS⅁
    SS⅁≡like-SS⅁ = refl

    open Sum
    module WithSumRAndℤqProps
        (Rₐ : ★)
        (sumRₐ : Sum Rₐ)
        (sumRₐ-ext : SumExt sumRₐ)
        (dist-^-⊠ : ∀ α x y → α ^ (x ⊠ y) ≡ (α ^ x) ^ y)
        (sumℤq : Sum ℤq)
        (sumℤq-ext : SumExt sumℤq)
        where

        module SumR where
          R = Rₐ × ℤq × ℤq × ℤq
          sumR : Sum R
          sumR = sumProd sumRₐ (sumProd sumℤq (sumProd sumℤq sumℤq))
          #R_ : Count R
          #R_ = sumToCount sumR
          sumR-ext : SumExt sumR
          sumR-ext = sumProd-ext sumRₐ-ext (sumProd-ext sumℤq-ext (sumProd-ext sumℤq-ext sumℤq-ext))
        private
            #q_ : Count ℤq
            #q_ = sumToCount sumℤq

        open SumR

        _≈q_ : (f g : ℤq → Bit) → ★
        f ≈q g = #q f ≡ #q g

        _≈R_ : (f g : R → Bit) → ★
        f ≈R g = #R f ≡ #R g

        module EvenMoreProof
            (ddh-hyp : (A : DDHAdv Rₐ) → DDH⅁ A 0b ≈R DDH⅁ A 1b)
            (otp-lem : ∀ (A : G → Bit) m → (λ x → A (g^ x ∙ m)) ≈q (λ x → A (g^ x)))
            where

                otp-lem' : ∀ D M₀ M₁ → OTP⅁ M₀ D ≈R OTP⅁ M₁ D
                otp-lem' D M₀ M₁ = sumRₐ-ext (λ r →
                                     sumℤq-ext (λ x →
                                       sumℤq-ext (λ y →
                                         pf r x y)))
                  where
                  f0 = λ M r x y z → OTP⅁ M D (r , x , y , z)
                  f1 = λ M r x y → sumℤq (Bool.toℕ ∘ f0 M r x y)
                  f2 = λ M r x → sumℤq (f1 M r x)
                  f3 = λ M r → sumℤq (f2 M r)
                  pf : ∀ r x y → f1 M₀ r x y ≡ f1 M₁ r x y
                  pf r x y = pf'
                    where gˣ = g^ x
                          gʸ = g^ y
                          m₀ = M₀ r gˣ
                          m₁ = M₁ r gˣ
                          f5 = λ M z → D r gˣ gʸ (g^ z ∙ M)
                          pf' : f5 m₀ ≈q f5 m₁
                          pf' rewrite otp-lem (D r gˣ gʸ) m₀
                                    | otp-lem (D r gˣ gʸ) m₁ = refl

                projM : EncAdv Rₐ → Bit → Rₐ → G → G
                projM (m , _) b r gˣ = m r gˣ b

                projD : EncAdv Rₐ → Rₐ → G → G → G → Bit
                projD (_ , D) r gˣ gʸ gᶻ∙M = D r gˣ (gʸ , gᶻ∙M)

                module WithAdversary (A : EncAdv Rₐ) b where
                    Aᵇ = TrA b A
                    A¬ᵇ = TrA (not b) A

                    pf0,5 : SS⅁ A b ≗ DDH⅁ Aᵇ 0b
                    pf0,5 (r , x , y , z) rewrite dist-^-⊠ g x y = refl

                    pf1 : SS⅁ A b ≈R DDH⅁ Aᵇ 0b
                    pf1 = sumR-ext (cong Bool.toℕ ∘ pf0,5)

                    pf2 : DDH⅁ Aᵇ 0b ≈R DDH⅁ Aᵇ 1b
                    pf2 = ddh-hyp Aᵇ

                    pf2,5 : DDH⅁ Aᵇ 1b ≡ OTP⅁ (projM A b) (projD A)
                    pf2,5 = refl

                    pf3 : DDH⅁ Aᵇ 1b ≈R DDH⅁ A¬ᵇ 1b
                    pf3 = otp-lem' (projD A) (projM A b) (projM A (not b))

                    pf4 : DDH⅁ A¬ᵇ 1b ≈R DDH⅁ A¬ᵇ 0b
                    pf4 = ≡.sym (ddh-hyp A¬ᵇ)

                    pf4,5 : SS⅁ A (not b) ≗ DDH⅁ A¬ᵇ 0b
                    pf4,5 (r , x , y , z) rewrite dist-^-⊠ g x y = refl

                    pf5 : SS⅁ A (not b) ≈R DDH⅁ A¬ᵇ 0b
                    pf5 = sumR-ext (cong Bool.toℕ ∘ pf4,5)

                    final : SS⅁ A b ≈R SS⅁ A (not b)
                    final rewrite pf1 | pf2 | pf3 | pf4 | pf5 = refl

module El-Gamal-Hashed
    (ℤq : ★)
    (_⊠_ : ℤq → ℤq → ℤq)
    (G : ★)
    (g : G)
    (_^_ : G → ℤq → G)
    -- (HKey : ★)
    (|M| : ℕ)
    (ℋ : {-HKey →-} G → Bits |M|) where

    Message = Bits |M|

    ℋ⟨_⟩⊕_ : G → Message → Message
    ℋ⟨ δ ⟩⊕ m = ℋ δ ⊕ m

    open El-Gamal-Generic ℤq _⊠_ G g _^_ Message ℋ⟨_⟩⊕_

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

  module EB = El-Gamal-Base _ _⊠_ G g _^_ _⁻¹ _∙_
  open EB hiding (g^_)

  open ℤq-count ℤq _⊞_ sumℤq sumℤq-ext sumℤq-⊞-lem

  Rₐ = El `Rₐ
  sumRₐ = sum `Rₐ
  sumRₐ-ext = sum-ext `Rₐ

  open WithSumRAndℤqProps Rₐ sumRₐ sumRₐ-ext dist-^-⊠ sumℤq sumℤq-ext

  open SumR
  postulate
    ddh-hyp : (A : DDHAdv Rₐ) → DDH⅁ A 0b ≈R DDH⅁ A 1b
    otp-lem : ∀ (A : G → Bit) m → (λ x → A (g^ x ∙ m)) ≈q (λ x → A (g^ x))

  open EvenMoreProof ddh-hyp otp-lem

  final : ∀ A → SS⅁ A 0b ≈R SS⅁ A 1b
  final A = WithAdversary.final A 0b

module ⟨ℤ11⟩★ = ⟨ℤp⟩★ (11 ∸ 3)
                   `X -- the amount of adversary randomness

        -- -}
        -- -}
        -- -}
        -- -}
        -- -}
        -- -}
