module otp-sem-sec where

open import Function
open import Data.Nat.NP
open import Data.Bits
open import Data.Bool
open import Data.Vec
open import Data.Product.NP
open import circuit
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- dup from Game
EXP : ∀ {a b} {A : Set a} {B : Set b} → Bit → (A → B) → (A × A → B)
EXP 0b f (x₀ , x₁) = f x₀
EXP 1b f (x₀ , x₁) = f x₁

proj : ∀ {a} {A : Set a} → A × A → Bit → A
proj (x₀ , x₁) 0b = x₀
proj (x₀ , x₁) 1b = x₁

module FunctionExtra where
  _***_ : ∀ {A B C D : Set} → (A → B) → (C → D) → A × C → B × D
  (f *** g) (x , y) = (f x , g y)
  _>>>_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
            (A → B) → (B → C) → (A → C)
  f >>> g = g ∘ f
  infixr 1 _>>>_

Coins = ℕ
Ports = ℕ

{-
module Guess
  (Proba : Set)
  (Pr[_≡1] : ∀ {c} (EXP : Bits c → Bit) → Proba)
  (dist : Proba → Proba → Proba)
  (negligible : Proba → Set)

  where

  record Power : Set where
    constructor mk
    field
      coins : Coins
  open Power public

  ↺ : Coins → Set → Set
  ↺ c A = Bits c → A

  GuessAdv : Power → Set
  GuessAdv (mk c) = ↺ c Bit

  runGuess⅁ : ∀ {p} (A : GuessAdv p) (b : Bit) → ↺ (coins p) Bit
  runGuess⅁ {mk c} A b R = A R

  negligible-advantage : ∀ {c} (EXP : Bit → ↺ c Bit) → Set
  negligible-advantage EXP = negligible (dist Pr[ EXP 0b ≡1] Pr[ EXP 1b ≡1])

  -- Any adversary cannot do better than a random guess.
  GuessSec : Power → Set
  GuessSec power = ∀ (A : GuessAdv power) → negligible-advantage (runGuess⅁ A)
-}

module F'
  (_]-[_ : ∀ {c} (f g : Bits c → Bit) → Set)
  (]-[-cong : ∀ {c} {f f' g g' : Bits c → Bit} → f ≗ g → f' ≗ g' → f ]-[ f' → g ]-[ g')

  (|M| |C| : ℕ)

  where

  record Power : Set where
    constructor mk
    field
      coins : Coins
  open Power public

  M = Bits |M|
  C = Bits |C|

  ↺ : Coins → Set → Set
  ↺ c A = Bits c → A

  -- M×M = Bit → M
  M×M = M × M

{-
  record SemSecAdv' power : Set where
    constructor mk

    open Power power renaming (coins to c)
    field
      {c₀ c₁}   : Coins
      c≡c₀+c₁  : c ≡ c₀ + c₁
      beh : ↺ c₀ (M×M × (C → ↺ c₁ Bit))
    R' = subst Bits c≡c₀+c₁
    R₀ = take c₀ ∘ R'
    R₁ = drop c₀ ∘ R'
-}

  record SemSecAdv power : Set where
    constructor mk

    open Power power renaming (coins to c)
    field
      beh : ↺ c (M×M × (C → Bit))

  -- Returing 0 means Chal wins, Adv looses
  --          1 means Adv  wins, Chal looses
  runSemSec : ∀ (E : M → C) {p} (A : SemSecAdv p) (b : Bit) → ↺ (coins p) Bit
  runSemSec E {mk c} A b R
      = case beh R of λ { (m , kont) → kont (E (proj m b)) }
    where open SemSecAdv A using (beh)

  _⇄_ = runSemSec

  breaks : ∀ {c} (EXP : Bit → ↺ c Bit) → Set
  breaks ⅁ = ⅁ 0b ]-[ ⅁ 1b

  ¬SemSec : ∀ (E : M → C) → Power → Set
  ¬SemSec E power = ∃ (λ (A : SemSecAdv power) → breaks (E ⇄ A))

  Enc = M → C

  Tr = Enc → Enc

  -- SemSecReduction f E₀ E₁:
  --   security of E₀ reduces to security of E₁
  --   breaking E₁ reduces to breaking E₀
  SemSecReduction : (p₀ p₁ : Power) (E₀ E₁ : Enc) → Set
  SemSecReduction p₀ p₁ E₀ E₁ = ¬SemSec E₁ p₁ → ¬SemSec E₀ p₀

  SemSecTr : (f : Power → Power) (tr : Tr) → Set
  SemSecTr f tr = ∀ {E p} → SemSecReduction p (f p) E (tr E)

  open FunctionExtra

  post-comp-pres-sem-sec : ∀ post-E → SemSecTr id (_∘_ post-E)
  post-comp-pres-sem-sec post-E {E} {power} (A' , A'-breaks-E') = A , A-breaks-E
     where E' : Enc
           E' = E >>> post-E
           open Power power renaming (coins to c)
           open SemSecAdv A' using () renaming (beh to A'-beh)
           pre-post-E : (C → Bit) → (C → Bit)
           pre-post-E kont = post-E >>> kont
           A : SemSecAdv power
           A = mk (A'-beh >>> id *** pre-post-E)
           A-breaks-E : breaks (E ⇄ A)
           A-breaks-E = A'-breaks-E'

  post-comp-pres-sem-sec' : ∀ (post-E post-E⁻¹ : C → C)
                              (post-E-inv : ∀ {bs : C} → post-E⁻¹ (post-E bs) ≡ bs)
                              {E p} → SemSecReduction p p (E >>> post-E) E
  post-comp-pres-sem-sec' post-E post-E⁻¹ post-E-inv {E} {power} (A , A-breaks-E)
       = A' , A'-breaks-E'
     where E' : Enc
           E' = E >>> post-E
           open Power power renaming (coins to c)
           open SemSecAdv A using () renaming (beh to A-beh)
           pre-post-E⁻¹ : (C → Bit) → (C → Bit)
           pre-post-E⁻¹ kont = post-E⁻¹ >>> kont
           A' : SemSecAdv power
           A' = mk (A-beh >>> id *** pre-post-E⁻¹)
           same-games : ∀ b → (E ⇄ A) b ≗ (E' ⇄ A') b
           same-games b R rewrite post-E-inv {E (proj (proj₁ (A-beh R)) b)} = refl
           A'-breaks-E' : breaks (E' ⇄ A')
           A'-breaks-E' = ]-[-cong (same-games 0b) (same-games 1b) A-breaks-E

open import diff
import Data.Fin as Fin
_]-_-[_ : ∀ {c} (f : Bits c → Bit) k (g : Bits c → Bit) → Set
_]-_-[_ {c} f k g = diff (Fin.toℕ #⟨ f ⟩) (Fin.toℕ #⟨ g ⟩) ≥ 2^(c ∸ k)
  --  diff (#1 f) (#1 g) ≥ 2^(-k) * 2^ c
  --  diff (#1 f) (#1 g) ≥ ε * 2^ c
  --  dist (#1 f) (#1 g) ≥ ε * 2^ c
  --    where ε = 2^ -k
  -- {!dist (#1 f / 2^ c) (#1 g / 2^ c) > ε !}


open import Data.Vec.NP using (count)

ext-count : ∀ {n a} {A : Set a} {f g : A → Bool} → f ≗ g → (xs : Vec A n) → count f xs ≡ count g xs
ext-count f≗g [] = refl
ext-count f≗g (x ∷ xs) rewrite ext-count f≗g xs | f≗g x = refl

ext-# : ∀ {c} {f g : Bits c → Bit} → f ≗ g → #⟨ f ⟩ ≡ #⟨ g ⟩
ext-# f≗g = ext-count f≗g (allBits _)

]-[-cong : ∀ {k c} {f f' g g' : Bits c → Bit} → f ≗ g → f' ≗ g' → f ]- k -[ f' → g ]- k -[ g'
]-[-cong f≗g f'≗g' f]-[f' rewrite ext-# f≗g | ext-# f'≗g' = f]-[f'

module F'' = F' (λ f g → f ]- 80 -[ g) (]-[-cong {80})

{-
module F''
  (|M| |C| : ℕ)

  (Proba : Set)
  (Pr[_≡1] : ∀ {c} (EXP : Bits c → Bit) → Proba)
  (Pr-ext : ∀ {c} {f g : Bits c → Bit} → f ≗ g → Pr[ f ≡1] ≡ Pr[ g ≡1])
  (dist : Proba → Proba → Proba)
  (negligible : Proba → Set)
  (non-negligible : Proba → Set)

  where
  advantage : ∀ {c} (EXP : Bit → ↺ c Bit) → Proba
  advantage EXP = dist Pr[ EXP 0b ≡1] Pr[ EXP 1b ≡1]

  breaks : ∀ {c} (EXP : Bit → ↺ c Bit) → Set
  breaks ⅁ = non-negligible (advantage ⅁)

  SemSec : ∀ (E : M → C) → Power → Set
  SemSec E power = ∀ (A : SemSecAdv power) → negligible (advantage (E ⇄ A))
-}

{-
  ⊕-pres-sem-sec : ∀ mask → SemSecReduction (_∘_ (_⊕_ mask))
  ⊕-pres-sem-sec = ?
-}

module F
  (Size Time : Set)
  -- (FCp : Coins → Size → Time → Ports → Ports → Set)
  (Cp : Ports → Ports → Set)
  (builder : CircuitBuilder Cp)
  -- (toC : ∀ {c s t i o} → FCp c s t i o → Cp (c + i) o)
  (runC : ∀ {i o} → Cp i o → Bits i → Bits o)

  (|M| |C| : ℕ)

  (_]-[_ : ∀ {c} (f g : Bits c → Bit) → Set)
  (]-[-cong : ∀ {c} {f f' g g' : Bits c → Bit} → f ≗ g → f' ≗ g' → f ]-[ f' → g ]-[ g')
{-
  (Proba : Set)
  (Pr[_≡1] : ∀ {c} (EXP : Bits c → Bit) → Proba)
  (dist : Proba → Proba → Proba)
  (negligible : Proba → Set)
-}

  where

  record Power : Set where
    constructor mk
    field
      coins : Coins
      size  : Size
      time  : Time
  open Power public

  M = Bits |M|
  C = Bits |C|

  -- M×M = Bit → M
  M×M = M × M

  ↺ : Coins → Set → Set
  ↺ c A = Bits c → A

{-
  record SemSecAdv' power : Set where
    constructor mk

    open Power power renaming (coins to c; size to s; time to t)
    field
      fcp : FCp c s t |C| (1 + (|M| + |M|))

      {c₀ c₁}   : Coins
      c≡c₀+c₁  : c ≡ c₀ + c₁

    R₀ = Bits c₀
    R₁ = Bits c₁

    open CircuitBuilder builder

    cp : Cp ((c₀ + c₁) + |C|) (1 + (|M| + |M|))
    cp rewrite sym c≡c₀+c₁ = toC fcp

    cp₁ : Cp c₀ (|M| + |M|)
    cp₁ = padR c₁ >>> padR |C| >>> cp >>> tailC

    cp₂ : Cp ((c₀ + c₁) + |C|) 1
    cp₂ = cp >>> headC

    beh : ↺ c₀ ((M × M) × (C → ↺ c₁ Bit))
    beh R₀ = (case splitAt |M| (runC cp₁ R₀) of λ { (x , y , _) → (x , y) })
           , (λ C R₁ → head (runC cp₂ ((R₀ ++ R₁) ++ C)))
-}

  record SemSecAdv power : Set where
    constructor mk

    open Power power renaming (coins to c; size to s; time to t)
{-
    field
      fcp : FCp c s t |C| (1 + (|M| + |M|))
-}

    R = Bits c

    open CircuitBuilder builder

    field
      cp : Cp (c + |C|) (1 + (|M| + |M|))
 --   cp = toC fcp

    cp₁ : Cp c (|M| + |M|)
    cp₁ = padR |C| >>> cp >>> tailC

    cp₂ : Cp (c + |C|) 1
    cp₂ = cp >>> headC

    splitAt′ : ∀ k {n} → Bits (k + n) → Bits k × Bits n
    splitAt′ k xs = case splitAt k xs of λ { (ys , zs , _) → (ys , zs) }

    beh : ↺ c (M×M × (C → Bit))
    beh R = splitAt′ |M| (runC cp₁ R)
          , (λ C → head (runC cp₂ (R ++ C)))

  -- Returing 0 means Chal wins, Adv looses
  --          1 means Adv  wins, Chal looses
  runSemSec : ∀ (E : M → C) {p} (A : SemSecAdv p) (b : Bit) → ↺ (coins p) Bit
  runSemSec E {mk c s t} A b R
      = case beh R of λ { (m , kont) → kont (E (proj m b)) }
    where open SemSecAdv A using (beh)

  _⇄_ = runSemSec

  Enc = M → C

  Tr = Enc → Enc

  breaks : ∀ {c} (EXP : Bit → ↺ c Bit) → Set
  breaks ⅁ = ⅁ 0b ]-[ ⅁ 1b

  ¬SemSec : ∀ (E : M → C) → Power → Set
  ¬SemSec E power = ∃ (λ (A : SemSecAdv power) → breaks (E ⇄ A))

  -- SemSecReduction f E₀ E₁:
  --   security of E₀ reduces to security of E₁
  --   breaking E₁ reduces to breaking E₀
  SemSecReduction : (p₀ p₁ : Power) (E₀ E₁ : Enc) → Set
  SemSecReduction p₀ p₁ E₀ E₁ = ¬SemSec E₁ p₁ → ¬SemSec E₀ p₀

  SemSecTr : (f : Power → Power) (tr : Tr) → Set
  SemSecTr f tr = ∀ {E p} → SemSecReduction p (f p) E (tr E)

  module FE = FunctionExtra
  open CircuitBuilder builder

{-
  post-comp-pres-sem-sec : ∀ (post-E : Cp |C| |C|) → SemSecTr id (_∘_ (runC post-E))
  post-comp-pres-sem-sec post-E {E} {power} (A' , A'-breaks-E') = A , A-breaks-E
     where E' : Enc
           E' = E FE.>>> runC post-E
           open Power power renaming (coins to c)
           open SemSecAdv A' using () renaming (beh to A'-beh; cp to A'-cp)
           pre-post-E : Cp |C| 1 → Cp |C| 1
           pre-post-E kont = post-E >>> kont
           A : SemSecAdv power
           A = mk (A'-cp >>> {!pre-post-E!} *** idC {|M| + |M|})
           A-breaks-E : breaks (E ⇄ A)
           A-breaks-E = {!A'-breaks-E'!}
-}
{-
  ⊕-pres-sem-sec : ∀ mask → SemSecReduction (_∘_ (_⊕_ mask))
-}
