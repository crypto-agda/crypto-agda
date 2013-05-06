{-# OPTIONS --copatterns #-}
open import Type
open import Function
open import Data.Product
open import Data.Unit
import Data.Fin.NP as Fin
open Fin using (Fin; zero; suc) renaming (#_ to ##_; toℕ to Fin▹ℕ)
open import Data.Nat.NP hiding (_^_; _==_)
open import Data.Bit
open import Data.Bits hiding (_==_)
open import Relation.Binary.PropositionalEquality.NP as ≡
import Game.DDH
import Game.IND-CPA
import Cipher.ElGamal.Generic
open import Search.Type
open import Search.Searchable renaming (Searchable to Explorable)
open import Search.Searchable.Product
open import Search.Searchable.Fin
open import Relation.Binary.NP

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

    μU : Explorable X → ∀ u → Explorable (El u)
    μU μX `⊤         = μ⊤
    μU μX `X         = μX
    μU μX (u₀ `× u₁) = μU μX u₀ ×-μ μU μX u₁

module ℤq-count
  (ℤq : ★)
  (_⊞_ : ℤq → ℤq → ℤq)
  (μℤq : Explorable ℤq)
  (⊞-stable : ∀ x → SumStableUnder (sum μℤq) (_⊞_ x))
  where

  -- open Sum
  open Univ ℤq public
  open `★ public renaming (`X to `ℤq)

  #_ : ∀ {u} → ↺ u Bit → ℕ
  #_ {u} f = count (μU μℤq u) (run↺ f)

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
  lem x Adv = sym (⊞-stable x (Bit▹ℕ ∘ Adv))

  -- ∀ (A : ℤq → Bit) → # (A ⁇)

open Fin.Modulo renaming (sucmod to [suc]; sucmod-inj to [suc]-inj)

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
module ℤq-implem (q-1 : ℕ) ([0]' [1]' : Fin (suc q-1)) where
  -- open Sum
  q : ℕ
  q = suc q-1

  ℤq : ★
  ℤq = Fin q

  μℤq : Explorable ℤq
  μℤq = μFinSuc q-1

  sumℤq : Sum ℤq
  sumℤq = sum μℤq

  [0] : ℤq
  [0] = [0]'

  [1] : ℤq
  [1] = [1]'

  [suc]-stable : SumStableUnder (sum μℤq) [suc]
  [suc]-stable = μFinSUI [suc] [suc]-inj

  _ℕ⊞_ : ℕ → ℤq → ℤq
  zero  ℕ⊞ n = n
  suc m ℕ⊞ n = m ℕ⊞ ([suc] n)

  ℕ⊞-inj : ∀ n {x y} → n ℕ⊞ x ≡ n ℕ⊞ y → x ≡ y
  ℕ⊞-inj zero    eq = eq
  ℕ⊞-inj (suc n) eq = [suc]-inj (ℕ⊞-inj n eq)

  ℕ⊞-stable : ∀ m → SumStableUnder (sum μℤq) (_ℕ⊞_ m)
  ℕ⊞-stable m = μFinSUI (_ℕ⊞_ m) (ℕ⊞-inj m)

  _⊞_ : ℤq → ℤq → ℤq
  m ⊞ n = Fin▹ℕ m ℕ⊞ n

  ⊞-inj : ∀ m {x y} → m ⊞ x ≡ m ⊞ y → x ≡ y
  ⊞-inj m = ℕ⊞-inj (Fin▹ℕ m)

  ⊞-stable : ∀ m → SumStableUnder (sum μℤq) (_⊞_ m)
  ⊞-stable m = μFinSUI (_⊞_ m) (⊞-inj m)

  _ℕ⊠_ : ℕ → ℤq → ℤq
  zero  ℕ⊠ n = [0]
  suc m ℕ⊠ n = n ⊞ (m ℕ⊠ n)

  _⊠_ : ℤq → ℤq → ℤq
  m ⊠ n = Fin▹ℕ m ℕ⊠ n

  _[^]ℕ_ : ℤq → ℕ → ℤq
  m [^]ℕ zero  = [1]
  m [^]ℕ suc n = m ⊠ (m [^]ℕ n)

  _[^]_ : ℤq → ℤq → ℤq
  m [^] n = m [^]ℕ (Fin▹ℕ n)

module G-implem (p-1 q-1 : ℕ) (g' 0[p] 1[p] : Fin (suc p-1)) (0[q] 1[q] : Fin (suc q-1)) where
  open ℤq-implem q-1 0[q] 1[q] public
  open ℤq-implem p-1 0[p] 1[p] public using () renaming (ℤq to G; _⊠_ to _∙_; _[^]ℕ_ to _^[p]_)

  g : G
  g = g'

  _^_ : G → ℤq → G
  x ^ n = x ^[p] Fin▹ℕ n

  g^_ : ℤq → G
  g^ n = g ^ n

  {-
  g^-inj : ∀ m n → g^ m ≡ g^ n → m ≡ n
  g^-inj = {!!}
  -}

module G-count
  (ℤq : ★)
  (_⊞_ : ℤq → ℤq → ℤq)
  (μℤq : Explorable ℤq)
  (⊞-stable : ∀ x → SumStableUnder (sum μℤq) (_⊞_ x))
  (G : ★)
  (g : G)
  (_^_ : G → ℤq → G)
  (_∙_ : G → G → G)
  where

  g^_ : ℤq → G
  g^ n = g ^ n

  open ℤq-count ℤq _⊞_ μℤq ⊞-stable

  ⁇G : ↺ `ℤq G
  run↺ ⁇G x = g^ x

  #G : Count G
  #G f = #q (f ∘ g^_)

  {-
  #G-∙ : ∀ f m → #G (f ∘ _∙_ m) ≡ #G f
  #G-∙ f m = {!!}
  -}

module El-Gamal-Generic
  (ℤq       : ★)
  (_⊠_      : ℤq → ℤq → ℤq)
  (G        : ★)
  (g        : G)
  (_^_      : G → ℤq → G)
  (Message  : ★)
  (_∙_      : G → Message → Message)

  -- Required for decryption
  (_/_      : Message → G → Message)

  -- Required for the correctness proof
  (/-∙      : ∀ x y → (x ∙ y) / x ≡ y)
  (comm-^   : ∀ α x y → (α ^ x)^ y ≡ (α ^ y)^ x)

  -- Required for the security proof
  (dist-^-⊠ : ∀ α x y → α ^ (x ⊠ y) ≡ (α ^ x) ^ y)
  (μℤq      : Explorable ℤq)
  (Rₐ       : ★)
  (μRₐ      : Explorable Rₐ)
  where

    g^_ : ℤq → G
    g^ x = g ^ x

    -- gˣ is the pk
    -- x is the sk

    Rₓ : ★
    Rₓ = ℤq

    open Cipher.ElGamal.Generic Message ℤq G g _^_ _∙_ _/_

    functional-correctness : ∀ x y m → Dec x (Enc (g^ x) m y) ≡ m
    functional-correctness x y m rewrite comm-^ g x y | /-∙ (g^ y ^ x) m = refl

    module IND-CPA = Game.IND-CPA PubKey SecKey Message CipherText Rₑ Rₖ Rₐ Rₓ KeyGen Enc
    open IND-CPA using (R)

    UnusedGame : (i : Bit) → IND-CPA.Adv → (Bit × Rₐ × ℤq × ℤq × ℤq) → Bit
    UnusedGame i (m , d) (b , rₐ , x , y , z) = b == d rₐ gˣ (gʸ , ζ)
      where gˣ = g^ x
            gʸ = g^ y
            δ  = gˣ ^ case i 0→ y 1→ z
            ζ  = δ ∙ m rₐ gˣ b

    module DDH = Game.DDH ℤq G g _^_ Rₐ

    OTP⅁ : (Rₐ → G → Message) → (Rₐ → G → G → Message → Bit) → R → Bit
    OTP⅁ M d (r , x , y , z) = d r gˣ gʸ (gᶻ ∙ M r gˣ)
      where gˣ = g^ x
            gʸ = g^ y
            gᶻ = g^ z

    TrA : Bit → IND-CPA.Adv → DDH.Adv
    TrA b (m , d) rₐ gˣ gʸ gˣʸ = d rₐ gˣ (gʸ , gˣʸ ∙ m rₐ gˣ b)

    projM : IND-CPA.Adv → Bit → Rₐ → G → Message
    projM (m , _) b rₐ gˣ = m rₐ gˣ b

    projD : IND-CPA.Adv → Rₐ → G → G → Message → Bit
    projD (_ , d) rₐ gˣ gʸ gᶻ∙M = d rₐ gˣ (gʸ , gᶻ∙M)

    module Unused where
        like-⅁ : Bit → IND-CPA.Game
        like-⅁ b (m , d) (rₐ , x , y , _z) =
          d rₐ gˣ (gʸ , (gˣ ^ y) ∙ m rₐ gˣ b)
          where gˣ = g^ x
                gʸ = g^ y

        IND-CPA-⅁≡like-⅁ : IND-CPA.⅁ ≡ like-⅁
        IND-CPA-⅁≡like-⅁ = refl

    -- R = Rₐ × ℤq × ℤq × ℤq
    μR : Explorable R
    μR = μRₐ ×-μ μℤq ×-μ μℤq ×-μ μℤq

    #ᴿ_ : Count R
    #ᴿ_ = count μR

    #q_ : Count ℤq
    #q_ = count μℤq

    _≈q_ : (f g : ℤq → Bit) → ★
    f ≈q g = #q f ≡ #q g

    Re = (f g : R → Bit) → ★
    record Tra (_≈₀_ _≈₁_ : Re) (f g : R → Bit) : ★ where
      field
        h : R → Bit
        f≈₀h : f ≈₀ h
        h≈₁g : h ≈₁ g

    record _≈ᴿ_ (f g : R → Bit) : ★ where
      constructor mk
      field
        un-≈ᴿ : #ᴿ f ≡ #ᴿ g
    open _≈ᴿ_ public

    ≈ᴿ-trans : Transitive _≈ᴿ_
    ≈ᴿ-trans (mk p) (mk q) = mk (≡.trans p q)

    module ≈ᴿ-Reasoning where
      open Trans-Reasoning _≈ᴿ_ ≈ᴿ-trans public using () renaming (_≈⟨_⟩_ to _≈ᴿ⟨_⟩_)
      infix  2 _∎

      _∎ : ∀ x → x ≈ᴿ x
      _ ∎ = mk refl

    module Proof
        (ddh-hyp : ∀ A → DDH.⅁₀ A ≈ᴿ DDH.⅁₁ A)
        (otp-lem : ∀ A m₀ m₁ → (λ x → A (g^ x ∙ m₀)) ≈q (λ x → A (g^ x ∙ m₁)))
        (A : IND-CPA.Adv) (b : Bit)
      where
        OTP⅁-lem : ∀ d M₀ M₁ → OTP⅁ M₀ d ≈ᴿ OTP⅁ M₁ d
        OTP⅁-lem d M₀ M₁ = mk (
                           sum-ext μRₐ (λ r →
                             sum-ext μℤq (λ x →
                               sum-ext μℤq (λ y →
                                 pf r x y))))
          where
          pf : ∀ r x y → count μℤq (λ z → OTP⅁ M₀ d (r , x , y , z))
                       ≡ count μℤq (λ z → OTP⅁ M₁ d (r , x , y , z))
          pf r x y rewrite otp-lem (d r (g^ x) (g^ y)) (M₀ r (g^ x)) (M₁ r (g^ x)) = refl

        -- moving this definition above OTP⅁-lem breaks type-checking: ???
        ¬b : Bit
        ¬b = not b

        Aᵇ = TrA b A
        A¬ᵇ = TrA ¬b A

        pf0,5 : IND-CPA.⅁ b A ≗ DDH.⅁₀ Aᵇ
        pf0,5 (r , x , y , z) rewrite dist-^-⊠ g x y = refl

        pf2,5 : DDH.⅁₁ Aᵇ ≡ OTP⅁ (projM A b) (projD A)
        pf2,5 = refl

        pf4,5 : IND-CPA.⅁ ¬b A ≗ DDH.⅁₀ A¬ᵇ
        pf4,5 (r , x , y , z) rewrite dist-^-⊠ g x y = refl

        open ≈ᴿ-Reasoning

        final : IND-CPA.⅁ b A ≈ᴿ IND-CPA.⅁ ¬b A
        final = IND-CPA.⅁ b A
              ≈ᴿ⟨ mk (sum-ext μR (cong Bit▹ℕ ∘ pf0,5)) ⟩
                DDH.⅁₀ Aᵇ
              ≈ᴿ⟨ ddh-hyp Aᵇ ⟩
                DDH.⅁₁ Aᵇ
              ≈ᴿ⟨ OTP⅁-lem (projD A) (projM A b) (projM A ¬b) ⟩
                DDH.⅁₁ A¬ᵇ
              ≈ᴿ⟨ mk (≡.sym (un-≈ᴿ (ddh-hyp A¬ᵇ))) ⟩
                DDH.⅁₀ A¬ᵇ
              ≈ᴿ⟨ mk (≡.sym (sum-ext μR (cong Bit▹ℕ ∘ pf4,5))) ⟩
                IND-CPA.⅁ ¬b A
              ∎

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
    (μℤq : Explorable ℤq)
    (Rₐ : ★)
    (μRₐ : Explorable Rₐ)
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
    (μℤq : Explorable ℤq)
    (Rₐ : ★)
    (μRₐ : Explorable Rₐ)
    where

    Message = Bits |M|

    ℋ⟨_⟩⊕_ : G → Message → Message
    ℋ⟨ δ ⟩⊕ m = ℋ δ ⊕ m

    _/_ : Message → G → Message
    _/_ m δ = ℋ δ ⊕ m
{-

    /-∙ : ∀ x y → ℋ⟨ x ⟩⊕ y / x ≡ y
    /-∙ x y = {!!}

    open El-Gamal-Generic ℤq _⊠_ G g _^_ Message ℋ⟨_⟩⊕_ _/_ {!!} {!!}
           dist-^-⊠ sumℤq sumℤq-ext Rₐ sumRₐ sumRₐ-ext public
           -}

           {-
    OTP⅁-lem : ∀ d M₀ M₁ → OTP⅁ M₀ d ≈ᴿ OTP⅁ M₁ d
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

  _/_ : G → G → G
  x / y = x ∙ (y ⁻¹)

  postulate
    /-• : ∀ x y → (x ∙ y) / x ≡ y
    dist-^-⊠ : ∀ α x y → α ^ (x ⊠ y) ≡ (α ^ x) ^ y
    ⊠-comm : ∀ x y → x ⊠ y ≡ y ⊠ x

  comm-^ : ∀ α x y → (α ^ x)^ y ≡ (α ^ y)^ x
  comm-^ α x y = (α ^ x)^ y
               ≡⟨ sym (dist-^-⊠ α x y) ⟩
                  α ^ (x ⊠ y)
               ≡⟨ cong (_^_ α) (⊠-comm x y) ⟩
                  α ^ (y ⊠ x)
               ≡⟨ dist-^-⊠ α y x ⟩
                  (α ^ y)^ x
               ∎
    where open ≡-Reasoning

  open ℤq-count ℤq _⊞_ μℤq ⊞-stable

  μRₐ : Explorable (El `Rₐ)
  μRₐ = μU μℤq `Rₐ

  Rₐ = El `Rₐ
  sumRₐ = sum μRₐ
  sumRₐ-ext = sum-ext μRₐ

  module EB = El-Gamal-Base _ _⊠_ G g _^_ _∙_ _/_ /-• comm-^ dist-^-⊠ μℤq Rₐ μRₐ
  open EB hiding (g^_)

  otp-base-lem : ∀ (A : G → Bit) m → (A ∘ g^_) ≈q (A ∘ g^_ ∘ _⊞_ m)
  otp-base-lem A m = ⊞-stable m (Bit▹ℕ ∘ A ∘ g^_)

  postulate
    ddh-hyp : (A : DDH.Adv) → DDH.⅁₀ A ≈ᴿ DDH.⅁₁ A
    otp-lem : ∀ (A : G → Bit) m → (λ x → A (g^ x ∙ m)) ≈q (λ x → A (g^ x))


  open OTP⅁-LEM otp-lem

  {-
  final : ∀ A → IND-CPA.⅁ A 0b ≈ᴿ IND-CPA.⅁ A 1b
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
