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

[0→_,1→_] : ∀ {a} {A : Set a} → A → A → Bit → A
[0→ e₀ ,1→ e₁ ] b = if b then e₁ else e₀

case_0→_1→_ : ∀ {a} {A : Set a} → Bit → A → A → A
case b 0→ e₀ 1→ e₁ = if b then e₁ else e₀

Sum : ★ → ★
Sum A = (A → ℕ) → ℕ

Count : ★ → ★
Count A = (A → Bit) → ℕ

SumExt : ∀ {A} → Sum A → ★
SumExt sumA = ∀ f g → f ≗ g → sumA f ≡ sumA g

sumToCount : ∀ {A} → Sum A → Count A
sumToCount sumA f = sumA (Bool.toℕ ∘ f)

sumBit : Sum Bit
sumBit f = f 0b + f 1b

-- liftM2 _,_ in the continuation monad
sumProd : ∀ {A B : Set} → Sum A → Sum B → Sum (A × B)
sumProd sumA sumB f = sumA (λ x₀ →
                       sumB (λ x₁ →
                         f (x₀ , x₁)))

sumProd-ext : ∀ {A B : Set} {sumA : Sum A} {sumB : Sum B} →
              SumExt sumA → SumExt sumB → SumExt (sumProd sumA sumB)
sumProd-ext sumA-ext sumB-ext f g f≗g = sumA-ext _ _ (λ x → sumB-ext _ _ (λ y → f≗g (x , y)))

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
  (sumℤq : Sum ℤq)
  (sumℤq-lem : ∀ f x → sumℤq (f ∘ _⊞_ x) ≡ sumℤq f)
  where

  open Univ ℤq
  open `★ public renaming (`X to `ℤq)

  sum : (u : `★) → Sum (El u)
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
  (sumℤq : Sum ℤq)
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
    DDHAdv R = R → G → G → G → Bit

    DDH⅁₀ : ∀ {R} {_I : ★} → DDHAdv R → (R × ℤq × ℤq × _I) → Bit
    DDH⅁₀ D (r , x , y , _) = D r (g^ x) (g^ y) (g^ (x ⊠ y))

    DDH⅁₁ : ∀ {R} → DDHAdv R → (R × ℤq × ℤq × ℤq) → Bit
    DDH⅁₁ D (r , x , y , z) = D r (g^ x) (g^ y) (g^ z)

    DDH⅁ : ∀ {R} → DDHAdv R → Bit → (R × ℤq × ℤq × ℤq) → Bit
    DDH⅁ D b = (case b 0→ DDH⅁₀ 1→ DDH⅁₁) D

    -- ⅁′ : ∀ {R} → DDHAdv R → (Bit × ℤq × ℤq × ℤq × R) → Bit
    -- ⅁′ D (b , x , y , z , r) = DDH⅁ D b (x , y , z , r)

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
    EncAdv R = PubKey → R → (Bit → M) × (C → Bit)

    {-
    Game0 : ∀ {R _I : Set} → EncAdv R → (Bit × ℤq × ℤq × _I × R) → Bit
    Game0 A (b , x , y , z , r) =
      let (pk , sk) = KeyGen x
          (m , D) = A pk r in
      D (Enc pk (m b) y)

    Game : (i : Bit) → ∀ {R} → EncAdv R → (Bit × ℤq × ℤq × ℤq × R) → Bit
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

    SS⅁ : ∀ {R _I : Set} → EncAdv R → Bit → (R × ℤq × ℤq × _I) → Bit
    SS⅁ A b (r , x , y , z) =
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

    TrA : ∀ {R} → Bit → EncAdv R → DDHAdv R
    TrA b A r gˣ gʸ gˣʸ = d (gʸ , gˣʸ ∙ m b)
       where m,d = A gˣ r
             m = proj₁ m,d
             d = proj₂ m,d

    like-SS⅁ : ∀ {R _I : Set} → EncAdv R → Bit → (R × ℤq × ℤq × _I) → Bit
    like-SS⅁ A b (r , x , y , _z) =
      let -- gˣ = g ^ x
          -- gʸ = g ^ y
          (m , D) = A gˣ r in
      D (gʸ , (gˣ ^ y) ∙ m b)
      where gˣ = g ^ x
            gʸ = g ^ y

    SS⅁≡like-SS⅁ : ∀ {R _I} → SS⅁ {R} {_I} ≡ like-SS⅁
    SS⅁≡like-SS⅁ = refl

    OTP⅁ : ∀ {R : Set} → (R → G → G) → (R → G → G → G → Bit) → (R × ℤq × ℤq × ℤq) → Bit
    OTP⅁ M D (r , x , y , z) = D r gˣ gʸ (gᶻ ∙ M r gˣ)
      where gˣ = g ^ x
            gʸ = g ^ y
            gᶻ = g ^ z

    module WithℤqProps
        (dist-^-⊠ : ∀ α x y → α ^ (x ⊠ y) ≡ (α ^ x) ^ y)
      -- (⊠-comm : Commutative _≡_ _⊠_)
      -- (^-comm : ∀ α x y → (α ^ x) ^ y ≡ (α ^ y) ^ x)
        (sumℤq : Sum ℤq)
        (sumℤq-ext : SumExt sumℤq) where
        #q_ : Count ℤq
        #q_ = sumToCount sumℤq

        module SumU
          (R : Set)
          (sumR : Sum R)
          (sumR-ext : SumExt sumR)
          where
          U = R × ℤq × ℤq × ℤq
          sumU : Sum U
          sumU = sumProd sumR (sumProd sumℤq (sumProd sumℤq sumℤq))
          #U_ : Count U
          #U_ = sumToCount sumU
          sumU-ext : SumExt sumU
          sumU-ext = sumProd-ext sumR-ext (sumProd-ext sumℤq-ext (sumProd-ext sumℤq-ext sumℤq-ext))

        module WithSumR
            (R : Set)
            (sumR : Sum R)
            (sumR-ext : SumExt sumR)
           where
           open SumU R sumR sumR-ext

           module EvenMoreProof
            (ddh-hyp : (A : DDHAdv R) → #U (DDH⅁ A 0b) ≡ #U (DDH⅁ A 1b))

            (otp-lem : ∀ (A : G → Bit) m → #q(λ x → A (g^ x ∙ m)) ≡ #q(λ x → A (g^ x)))
            where

                _≈U_ : (f g : U → Bit) → Set
                f ≈U g = #U f ≡ #U g

                otp-lem' : ∀ D M₀ M₁ → OTP⅁ M₀ D ≈U OTP⅁ M₁ D
                otp-lem' D M₀ M₁ = sumR-ext (f3 M₀) (f3 M₁) (λ r →
                                     sumℤq-ext (f2 M₀ r) (f2 M₁ r) (λ x →
                                       sumℤq-ext (f1 M₀ r x) (f1 M₁ r x) (λ y →
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
                          m0 = M₀ r gˣ
                          m1 = M₁ r gˣ
                          f5 = λ M z → D r gˣ gʸ (g^ z ∙ M)
                          pf' : #q(f5 m0) ≡ #q(f5 m1)
                          pf' rewrite otp-lem (D r gˣ gʸ) m0
                                    | otp-lem (D r gˣ gʸ) m1 = refl

      {-
        #-proj₁ : ∀ {A B : Set} {f g : A → Bit} → # f ≡ # g
                   → #_ {A × B} (f ∘ proj₁) ≡ #_ {A × B} (g ∘ proj₁)
        #-proj₁ = {!!}

        otp-lem'' : ∀ (A : G → Bit) m
           → #(λ { (x , y) → A (g^ x ∙ m) }) ≡ #(λ { (x , y) → A (g ^ x) })
        otp-lem'' = {!!}
        -}
                projM : EncAdv R → Bit → R → G → G
                projM A b r gˣ = proj₁ (A gˣ r) b

                projD : EncAdv R → R → G → G → G → Bit
                projD A r gˣ gʸ gᶻ∙M = proj₂ (A gˣ r) (gʸ , gᶻ∙M)


                module WithAdversary (A : EncAdv R) b where
                    Aᵇ = TrA b A
                    A¬ᵇ = TrA (not b) A

                    pf0,5 : SS⅁ A b ≗ DDH⅁ Aᵇ 0b
                    pf0,5 (r , x , y , z) rewrite dist-^-⊠ g x y = refl

                    pf1 : #U(SS⅁ A b) ≡ #U(DDH⅁ Aᵇ 0b)
                    pf1 = sumU-ext _ _ (cong Bool.toℕ ∘ pf0,5)

                    pf2 : DDH⅁ Aᵇ 0b ≈U DDH⅁ Aᵇ 1b
                    pf2 = ddh-hyp Aᵇ

                    pf2,5 : DDH⅁ Aᵇ 1b ≡ OTP⅁ (projM A b) (projD A)
                    pf2,5 = refl

                    pf3 : DDH⅁ Aᵇ 1b ≈U DDH⅁ A¬ᵇ 1b
                    pf3 = otp-lem' (projD A) (projM A b) (projM A (not b))

                    pf4 : DDH⅁ A¬ᵇ 1b ≈U DDH⅁ A¬ᵇ 0b
                    pf4 = ≡.sym (ddh-hyp A¬ᵇ)

                    pf4,5 : SS⅁ A (not b) ≗ DDH⅁ A¬ᵇ 0b
                    pf4,5 (r , x , y , z) rewrite dist-^-⊠ g x y = refl

                    pf5 : #U(SS⅁ A (not b)) ≡ #U(DDH⅁ A¬ᵇ 0b)
                    pf5 = sumU-ext _ _ (cong Bool.toℕ ∘ pf4,5)

                    final : #U(SS⅁ A b) ≡ #U(SS⅁ A (not b))
                    final rewrite pf1 | pf2 | pf3 | pf4 | pf5 = refl


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
open WithℤqProps ?
-- open Proof {!!}

        -- -}
        -- -}
        -- -}
        -- -}
        -- -}
        -- -}
