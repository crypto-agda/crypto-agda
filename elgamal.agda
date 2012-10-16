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
--import Data.Vec.Properties as Vec
open import Algebra.FunctionProperties
open import Relation.Binary.PropositionalEquality as ≡

module elgamal where

★₁ : Set₂
★₁ = Set₁

★ : Set₁
★ = Set

[0→_,1→_] : ∀ {a} {A : Set a} → A → A → Bool → A
[0→ e₀ ,1→ e₁ ] b = if b then e₁ else e₀

case_0→_1→_ : ∀ {a} {A : Set a} → Bool → A → A → A
case b 0→ e₀ 1→ e₁ = if b then e₁ else e₀

sumBit : (Bit → ℕ) → ℕ
sumBit f = f 0b + f 1b

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

module ℤq-count
  (ℤq : ★)
  (_⊞_ : ℤq → ℤq → ℤq)
  (sumℤq : (ℤq → ℕ) → ℕ)
  (sumℤq-lem : ∀ f x → sumℤq (f ∘ _⊞_ x) ≡ sumℤq f)
  where

  open Univ ℤq
  open `★ public renaming (`X to `ℤq)

  sum : (u : `★) → (El u → ℕ) → ℕ
  sum `⊤         f = f _
  sum `X         f = sumℤq f
  sum (u₀ `× u₁) f = sum u₀ (λ x₀ →
                       sum u₁ (λ x₁ →
                         f (x₀ , x₁)))

  #_ : ∀ {u} → ↺ u Bit → ℕ
  #_ {u} f = sum u (Bool.toℕ ∘ run↺ f)

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
  lem x Adv = sumℤq-lem (Bool.toℕ ∘ Adv) x

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

  sumℤq : (ℤq → ℕ) → ℕ
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

module G-implem (p q : ℕ) (g' : Fin p) (0[p] 1[p] : Fin p) (0[q] 1[q] : Fin q) where
  open ℤq-implem q 0[q] 1[q] public
  open ℤq-implem p 0[p] 1[p] public using () renaming (ℤq to G; _⊠_ to _∙_; _[^]ℕ_ to _^[p]_)

  g : G
  g = g'

  _^_ : G → ℤq → G
  x ^ n = x ^[p] Fin.toℕ n

  g^_ : ℤq → G
  g^ n = g ^ n

  postulate
    g^-inj : ∀ m n → g^ m ≡ g^ n → m ≡ n

module G-count
  (ℤq : ★)
  (_⊞_ : ℤq → ℤq → ℤq)
  (sumℤq : (ℤq → ℕ) → ℕ)
  (sumℤq-lem : ∀ f x → sumℤq (f ∘ _⊞_ x) ≡ sumℤq f)
  (G : ★)
  (g : G)
  (_^_ : G → ℤq → G)
  where

  open Univ ℤq
  open ℤq-count ℤq _⊞_ sumℤq sumℤq-lem

  ⁇G : ↺ `ℤq G
  run↺ ⁇G x = g ^ x

module DDH
  (ℤq  : ★)
  (_⊠_ : ℤq → ℤq → ℤq)
  (G   : ★)
  (g^_ : ℤq → G)
  where
    DDHAdv : ★ → ★
    DDHAdv R = G → G → G → R → Bool

    DDH⅁₀ : ∀ {R} {_I : ★} → DDHAdv R → (ℤq × ℤq × _I × R) → Bool
    DDH⅁₀ D (x , y , _ , r) = D (g^ x) (g^ y) (g^ (x ⊠ y)) r

    DDH⅁₁ : ∀ {R} → DDHAdv R → (ℤq × ℤq × ℤq × R) → Bool
    DDH⅁₁ D (x , y , z , r) = D (g^ x) (g^ y) (g^ z) r

    DDH⅁ : ∀ {R} → DDHAdv R → Bool → (ℤq × ℤq × ℤq × R) → Bool
    DDH⅁ D b = (case b 0→ DDH⅁₀ 1→ DDH⅁₁) D

    -- ⅁′ : ∀ {R} → DDHAdv R → (Bool × ℤq × ℤq × ℤq × R) → Bool
    -- ⅁′ D (b , x , y , z , r) = DDH⅁ D b (x , y , z , r)

    module With↺ where
        open Univ ℤq
        open `★ public renaming (`X to `ℤq)
        DDHAdv↺ : `★ → ★
        DDHAdv↺ R = G → G → G → ↺ R Bool
        ⅁₀↺ : ∀ {R _I} → DDHAdv↺ R → ↺ (`ℤq `× `ℤq `× _I `× R) Bool
        run↺ (⅁₀↺ D) = ⅁₀ (λ a b c → run↺ (D a b c))

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

    -- α is the pk
    -- α = g ^ x
    -- x is the sk

    PubKey = G
    SecKey = ℤq
    KeyPair = PubKey × SecKey
    CipherText = G × Message

    M = Message
    C = CipherText

    KeyGen : ℤq → KeyPair
    KeyGen x = (g ^ x , x)

    -- KeyGen↺ : ↺ ℤq KeyPair
    -- KeyGen↺ = mk KeyGen

    Enc : PubKey → Message → ℤq → CipherText
    Enc α m y = β , ζ where
      β = g ^ y
      δ = α ^ y
      ζ = δ ⊕ m

    -- Enc↺ : PubKey → Message → ↺ ℤq CipherText
    -- Enc↺ α m = mk (Enc α m)

    Dec : SecKey → CipherText → Message
    Dec x (β , ζ) = (β ^ x) ⊕⁻¹ ζ

    EncAdv : ★ → ★
    EncAdv R = PubKey → R → (Bool → M) × (C → Bool)

    {-
    Game0 : ∀ {R _I : Set} → EncAdv R → (Bool × ℤq × ℤq × _I × R) → Bool
    Game0 A (b , x , y , z , r) =
      let (pk , sk) = KeyGen x
          (m , D) = A pk r in
      D (Enc pk (m b) y)

    Game : (i : Bool) → ∀ {R} → EncAdv R → (Bool × ℤq × ℤq × ℤq × R) → Bool
    Game i A (b , x , y , z , r) =
      let (α , sk) = KeyGen x
          (m , D) = A α r
          β = g ^ y
          δ = α ^ case i 0→ y 1→ z
          ζ = δ ⊕ m b
      in {-b ==ᵇ-} D (β , ζ)

    Game-0b≡Game0 : ∀ {R} → Game 0b ≡ Game0 {R}
    Game-0b≡Game0 = refl
      -}

    SS⅁ : ∀ {R _I : Set} → EncAdv R → Bool → (ℤq × ℤq × _I × R) → Bool
    SS⅁ A b (x , y , z , r) =
      let -- (pk , sk) = KeyGen x
          (m , D) = A pk r in
      D (Enc pk (m b) y)
         where pk = g ^ x

    open DDH ℤq _⊠_ G (_^_ g) public

    -- Game0 ≈ Game 0b
    -- Game1 = Game 1b

    -- Game0 ≤ ε
    -- Game1 ≡ 0

    -- ⁇ ⊕ x ≈ ⁇

    -- g ^ ⁇ ∙ x ≈ g ^ ⁇

module El-Gamal-Base
    (ℤq : ★)
    (_⊠_ : ℤq → ℤq → ℤq)
    (G : ★)
    (g : G)
    (_^_ : G → ℤq → G)
    (_⁻¹ : G → G)
    (_∙_ : G → G → G)
    where

    g^_ : ℤq → G
    g^ x = g ^ x

    _/_ : G → G → G
    x / y = x ∙ (y ⁻¹)
    open El-Gamal-Generic ℤq _⊠_ G g _^_ G _∙_ (flip _/_) public

    TrA : ∀ {R} → Bool → EncAdv R → DDHAdv R
    TrA b A gˣ gʸ gˣʸ r = d (gʸ , gˣʸ ∙ m b)
       where m,d = A gˣ r
             m = proj₁ m,d
             d = proj₂ m,d

    like-SS⅁ : ∀ {R _I : Set} → EncAdv R → Bool → (ℤq × ℤq × _I × R) → Bool
    like-SS⅁ A b (x , y , z , r) =
      let -- gˣ = g ^ x
          -- gʸ = g ^ y
          (m , D) = A gˣ r in
      D (gʸ , (gˣ ^ y) ∙ m b)
      where gˣ = g ^ x
            gʸ = g ^ y

    SS⅁≡like-SS⅁ : ∀ {R _I} → SS⅁ {R} {_I} ≡ like-SS⅁
    SS⅁≡like-SS⅁ = refl

    module Proof
      -- (⊠-comm : Commutative _≡_ _⊠_)
      (dist-^-⊠ : ∀ α x y → α ^ (x ⊠ y) ≡ (α ^ x) ^ y)
      -- (^-comm : ∀ α x y → (α ^ x) ^ y ≡ (α ^ y) ^ x)

      (#_ : ∀ {R} → (R → Bit) → ℕ)
      (ddh-hyp : ∀ {R} (A : DDHAdv R) → # (DDH⅁ A 0b) ≡ # (DDH⅁ A 1b))
      (otp-lem : ∀ (A : G → Bit) m → #(λ x → A (g^ x ∙ m)) ≡ #(λ x → A (g ^ x)))
      -- (wk≈ : ∀ {R1 R2} (f : R2 → R1)(x y : R1 → Bit) (z t : R2 → Bit) → x ≈ y → z ≈ t)
      where

        _≈_ : ∀ {R} → (f g : R → Bit) → Set
        f ≈ g = # f ≡ # g

        pf1 : ∀ {R} A b r → SS⅁ {R} A b r ≡ DDH⅁ (TrA b A) 0b r
        pf1 A b (x , y , z , r) rewrite dist-^-⊠ g x y = refl

        pf2 : ∀ {R} A b → DDH⅁ {R} (TrA b A) 0b ≈ DDH⅁ (TrA b A) 1b
        pf2 A b = ddh-hyp (TrA b A)

        pf3 : ∀ {R} A b → DDH⅁ {R} (TrA b A) 1b ≈ DDH⅁ (TrA (not b) A) 1b
        pf3 {R} A b = pf3'
          where
            Aᵇ = TrA b A

            -- pf3'' : # (DDH⅁₁ {R} Aᵇ) ≈ DDH⅁₁ (TrA (not b) A)
            -- pf3'' = ?

            pf3' : DDH⅁₁ {R} Aᵇ ≈ DDH⅁₁ (TrA (not b) A)
            pf3' = {!wk≈ (λ { (x , y , z , r) → {!!} }) _ _ _ _ (otp-lem {!!} {!!})!}

      {-
        pf1 : ∀ {R} A r → Game 0b {R} A r ≡ ⅁′ (TrA 1b A) r
        pf1 A (true , x , y , z , r) rewrite dist-^-⊠ g x y = refl
        pf1 A (false , x , y , z , r) = {!!}

        pf2 : ∀ {R} A r → Game 1b {R} A r ≡ ⅁′ (TrA 0b A) r
        pf2 A (true , x , y , z , r)  = {!!}
        pf2 A (false , x , y , z , r) = {!!}
-}
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

    module Proof
      -- (⊠-comm : Commutative _≡_ _⊠_)
      -- (^-lem : ∀ α x y → α ^ (x ⊠ y) ≡ (α ^ x) ^ y)
      (^-comm : ∀ α x y → (α ^ x) ^ y ≡ (α ^ y) ^ x)
      -- (x ∙ x ⁻¹ ≡ 0)
      (ℚ : ★)
      (dist : ℚ → ℚ → ℚ)
      (1/2 : ℚ)
      (_≤_ : ℚ → ℚ → ★)
      (ε-DDH : ℚ)
      where

        Pr[S_] : Bool → ℚ
        Pr[S b ] = {!!}

        -- SS
        -- SS = dist Pr[

        Pr[S₀] = Pr[S 0b ]
        Pr[S₁] = Pr[S 1b ]

        pf1 : Pr[S₁] ≡ 1/2
        pf1 = {!!}

        pf2 : dist Pr[S₀] 1/2 ≡ dist Pr[S₀] Pr[S₁]
        pf2 = {!!}

        pf3 : dist Pr[S₀] Pr[S₁] ≤ ε-DDH
        pf3 = {!!}

        pf4 : dist Pr[S₀] 1/2 ≤ ε-DDH
        pf4 = {!!}

module G11 = G-implem 11 10 (## 2) (## 0) (## 1) (## 0) (## 1)
open G11
module E11 = El-Gamal-Base _ _⊠_ G g _^_ {!!} _∙_
open E11
open Proof {!!}

        -- -}
        -- -}
        -- -}
        -- -}
        -- -}
        -- -}
