module otp-sem-sec where

open import Function
open import Data.Nat.NP
open import Data.Bits
open import Data.Bool
open import Data.Bool.Properties
open import Data.Vec hiding (_>>=_)
open import Data.Product.NP
open import circuit
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import flipbased-implem

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

module BitsExtra where
  splitAt′ : ∀ k {n} → Bits (k + n) → Bits k × Bits n
  splitAt′ k xs = case splitAt k xs of λ { (ys , zs , _) → (ys , zs) }

  vnot∘vnot : ∀ {n} → vnot {n} ∘ vnot ≗ id
  vnot∘vnot [] = refl
  vnot∘vnot (x ∷ xs) rewrite not-involutive x = cong (_∷_ x) (vnot∘vnot xs)

open BitsExtra

Coins = ℕ
Ports = ℕ
Size  = ℕ
Time  = ℕ

record Power : Set where
  constructor mk
  field
    coins : Coins
    size  : Size
    time  : Time
open Power public

same-power : ∀ {a} {A : Set a} → A → Power → Power
same-power _ p = p

record PrgDist : Set₁ where
  constructor mk
  field
    _]-[_ : ∀ {c} (f g : ↺ c Bit) → Set
    ]-[-cong : ∀ {c} {f f' g g' : ↺ c Bit} → f ≗↺ g → f' ≗↺ g' → f ]-[ f' → g ]-[ g'

module Guess (prgDist : PrgDist) where
  open PrgDist prgDist

  GuessAdv : Coins → Set
  GuessAdv c = ↺ c Bit

  runGuess⅁ : ∀ {ca} (A : GuessAdv ca) (b : Bit) → ↺ ca Bit
  runGuess⅁ A _ = A

  breaks : ∀ {c} (EXP : Bit → ↺ c Bit) → Set
  breaks ⅁ = ⅁ 0b ]-[ ⅁ 1b

  -- Any adversary cannot do better than a random guess.
  GuessSec : Power → Set
  GuessSec power = ∀ (A : GuessAdv (coins power)) → ¬(breaks (runGuess⅁ A))

module F' (prgDist : PrgDist) (|M| |C| : ℕ) where
  open PrgDist prgDist

{-
  record Power : Set where
    constructor mk
    field
      coins : Coins
  open Power public
-}
{-
  Power = Coins
  module Power (p : Power) where
    coins : Coins
    coins = p
  open Power
-}

  M = Bits |M|
  C = Bits |C|

  M×M = Bit → M

  Enc : ∀ cc → Set
  Enc cc = M → ↺ cc C

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

  SemSecAdv : Coins → Set
  SemSecAdv c = ↺ c (M×M × (C → Bit))

  -- Returing 0 means Chal wins, Adv looses
  --          1 means Adv  wins, Chal looses
  runSemSec : ∀ {cc ca} (E : Enc cc) (A : SemSecAdv ca) b → ↺ (ca + cc) Bit
  runSemSec E A b
    = A >>= λ { (m , kont) → map↺ kont (E (m b)) }

  _⇄_ : ∀ {cc ca} (E : Enc cc) (A : SemSecAdv ca) b → ↺ (ca + cc) Bit
  _⇄_ = runSemSec

  breaks : ∀ {c} (EXP : Bit → ↺ c Bit) → Set
  breaks ⅁ = ⅁ 0b ]-[ ⅁ 1b

  _≗⅁_ : ∀ {c} (⅁₀ ⅁₁ : Bit → ↺ c Bit) → Set
  ⅁₀ ≗⅁ ⅁₁ = ∀ b → ⅁₀ b ≗↺ ⅁₁ b

  ≗⅁-trans : ∀ {c} → Transitive (_≗⅁_ {c})
  ≗⅁-trans p q b R = trans (p b R) (q b R)

  _≗A_ : ∀ {ca} (A₁ A₂ : SemSecAdv ca) → Set
  _≗A_ A₁ A₂ = ∀ R → proj₁ (run↺ A₁ R) ≡ proj₁ (run↺ A₂ R) × proj₂ (run↺ A₁ R) ≗ proj₂ (run↺ A₂ R) 

  -- change-adv : ∀ {cc ca} {E : Enc cc} {A₁ A₂ : SemSecAdv ca} → A₁ ≗A A₂ → (E ⇄ A₁) ≗⅁ (E ⇄ A₂)
  -- change-adv A₁≗A₂ = {!!}

  ext-as-broken : ∀ {c} {⅁₀ ⅁₁ : Bit → ↺ c Bit}
                  → ⅁₀ ≗⅁ ⅁₁ → breaks ⅁₀ → breaks ⅁₁
  ext-as-broken same-games = ]-[-cong (same-games 0b) (same-games 1b)

  SemBroken : ∀ {cc} (E : Enc cc) → Power → Set
  SemBroken E power = ∃ (λ (A : SemSecAdv (coins power)) → breaks (E ⇄ A))

  Tr = ∀ {cc} → Enc cc → Enc cc

  -- SemSecReduction f E₀ E₁:
  --   security of E₀ reduces to security of E₁
  --   breaking E₁ reduces to breaking E₀
  SemSecReduction : ∀ (p₀ p₁ : Power) {cc} (E₀ E₁ : Enc cc) → Set
  SemSecReduction p₀ p₁ E₀ E₁ = SemBroken E₁ p₁ → SemBroken E₀ p₀

  SemSecTr : (f : Coins → Power → Power) (tr : Tr) → Set
  SemSecTr f tr = ∀ {cc p} {E : Enc cc} → SemSecReduction (f cc p) p E (tr E)

  open FunctionExtra

  post-comp : ∀ post-E → Tr
  post-comp post-E E = E >>> map↺ post-E

  post-comp-pres-sem-sec : ∀ post-E → SemSecTr same-power (post-comp post-E)
  post-comp-pres-sem-sec post-E {cc} {p} {E} (A' , A'-breaks-E') = A , A-breaks-E
     where E' : Enc cc
           E' = post-comp post-E E
           pre-post-E : (C → Bit) → (C → Bit)
           pre-post-E kont = post-E >>> kont
           A : SemSecAdv (coins p)
           A = mk (run↺ A' >>> id *** pre-post-E)
           A-breaks-E : breaks (E ⇄ A)
           A-breaks-E = A'-breaks-E'

  post-comp-pres-sem-sec' : ∀ (post-E post-E⁻¹ : C → C)
                              (post-E-inv : post-E⁻¹ ∘ post-E ≗ id)
                              {cc p} {E : Enc cc}
                            → SemSecReduction p p (post-comp post-E E) E
  post-comp-pres-sem-sec' post-E post-E⁻¹ post-E-inv {cc} {p} {E} (A , A-breaks-E)
       = A' , A'-breaks-E'
     where E' : Enc cc
           E' = post-comp post-E E
           open Power p renaming (coins to ca)
           pre-post-E⁻¹ : (C → Bit) → (C → Bit)
           pre-post-E⁻¹ kont = post-E⁻¹ >>> kont
           A' : SemSecAdv ca 
           A' = mk (run↺ A >>> id *** pre-post-E⁻¹)
           same-games : (E ⇄ A) ≗⅁ (E' ⇄ A')
           same-games b R
             rewrite post-E-inv (run↺ (E (proj₁ (run↺ A (take ca R)) b)) (drop ca R)) = refl
           A'-breaks-E' : breaks (E' ⇄ A')
           A'-breaks-E' = ext-as-broken same-games A-breaks-E

  post-neg : Tr
  post-neg E = E >>> map↺ vnot

  post-neg-pres-sem-sec : SemSecTr same-power post-neg
  post-neg-pres-sem-sec {cc} {p} {E} = post-comp-pres-sem-sec vnot {cc} {p} {E}

  post-neg-pres-sem-sec' : ∀ {cc p} {E : Enc cc}
                            → SemSecReduction p p (post-neg E) E
  post-neg-pres-sem-sec' {cc} {p} {E} = post-comp-pres-sem-sec' vnot vnot vnot∘vnot {cc} {p} {E}

open import diff
import Data.Fin as Fin
_]-_-[_ : ∀ {c} (f : ↺ c Bit) k (g : ↺ c Bit) → Set
_]-_-[_ {c} f k g = diff (Fin.toℕ #⟨ run↺ f ⟩) (Fin.toℕ #⟨ run↺ g ⟩) ≥ 2^(c ∸ k)
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

]-[-cong : ∀ {k c} {f f' g g' : ↺ c Bit} → f ≗↺ g → f' ≗↺ g' → f ]- k -[ f' → g ]- k -[ g'
]-[-cong f≗g f'≗g' f]-[f' rewrite ext-# f≗g | ext-# f'≗g' = f]-[f'

module Concrete k where
  _]-[_ : ∀ {c} (f g : ↺ c Bit) → Set
  _]-[_ f g = f ]- k -[ g
  cong' : ∀ {c} {f f' g g' : ↺ c Bit} → f ≗↺ g → f' ≗↺ g' → f ]-[ f' → g ]-[ g'
  cong' = ]-[-cong {k}
  prgDist : PrgDist
  prgDist = mk _]-[_ cong'
  module Guess' = Guess prgDist
  module F'' = F' prgDist

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
  -- (FCp : Coins → Size → Time → Ports → Ports → Set)
  (Cp : Ports → Ports → Set)
  (builder : CircuitBuilder Cp)
  -- (toC : ∀ {c s t i o} → FCp c s t i o → Cp (c + i) o)
  (runC : ∀ {i o} → Cp i o → Bits i → Bits o)

  (prgDist : PrgDist)
  (|M| |C| : ℕ)

  where

  open PrgDist prgDist
  module FF' = F' prgDist |M| |C|
  open FF' public using (M; C; M×M; Enc; Tr; breaks; ext-as-broken; _≗⅁_) renaming (_⇄_ to _⇄↺_; SemSecAdv to SemSecAdv↺)

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

    R = Bits c

    open FunctionExtra

    field
      |S| : ℕ

      cp₁ : Cp c (|M| + |M| + |S|)

      cp₂ : Cp (|S| + |C|) 1

    S = Bits |S|

    beh₁ : R → M×M × S
    beh₁ = runC cp₁ >>>
           splitAt′ (|M| + |M|) >>>
           (splitAt′ |M| >>> proj) *** id

    beh₂ : S → C → Bit
    beh₂ S C = head (runC cp₂ (S ++ C))

    beh : R → M×M × (C → Bit)
    beh = beh₁ >>> id *** beh₂

    beh↺ : ↺ c (M×M × (C → Bit))
    beh↺ = mk beh

  -- Returing 0 means Chal wins, Adv looses
  --          1 means Adv  wins, Chal looses
  _⇄_ : ∀ {cc p} (E : Enc cc) (A : SemSecAdv p) b → ↺ (coins p + cc) Bit
  E ⇄ A = E ⇄↺ SemSecAdv.beh↺ A

  SemBroken : ∀ {cc} (E : Enc cc) → Power → Set
  SemBroken E power = ∃ (λ (A : SemSecAdv power) → breaks (E ⇄ A))

  -- SemSecReduction f E₀ E₁:
  --   security of E₀ reduces to security of E₁
  --   breaking E₁ reduces to breaking E₀
  SemSecReduction : ∀ (p₀ p₁ : Power) {cc} (E₀ E₁ : Enc cc) → Set
  SemSecReduction p₀ p₁ E₀ E₁ = SemBroken E₁ p₁ → SemBroken E₀ p₀

  SemSecTr : (f : Coins → Power → Power) (tr : Tr) → Set
  SemSecTr f tr = ∀ {cc p} {E : Enc cc} → SemSecReduction (f cc p) p E (tr E)

  module FE = FunctionExtra

  post-comp-cp : ∀ post-E → Tr
  post-comp-cp post-E E = E >>> map↺ (runC post-E)
    where open FunctionExtra

{-
  post-comp-pres-sem-sec : ∀ (post-E : Cp |C| |C|) → SemSecTr same-power (post-comp-cp post-E)
  post-comp-pres-sem-sec post-E {cc} {p} {E} (A' , A'-breaks-E') = A , A-breaks-E
     where E' : Enc cc
           E' = post-comp-cp post-E E
           open Power p renaming (coins to c)
           open SemSecAdv A' using (|S|; cp₁) renaming (beh to A'-beh; beh↺ to A'-beh↺; cp₂ to A'-cp₂)
           pre-post-E-spec : (C → Bit) → (C → Bit)
           pre-post-E-spec kont = runC post-E >>> kont
             where open FunctionExtra
           A-beh-spec = A'-beh >>> id *** pre-post-E-spec
             where open FunctionExtra
           A-beh↺-spec : SemSecAdv↺ (coins p)
           A-beh↺-spec = mk A-beh-spec
           A : SemSecAdv p
           A = mk |S| cp₁ (idC {|S|} *** post-E >>> A'-cp₂)
             where open CircuitBuilder builder
           open SemSecAdv A using () renaming (beh↺ to A-beh↺; beh to A-beh; cp₂ to A-cp₂)
           pf1 : (E ⇄ A) ≗⅁ (E ⇄↺ A-beh↺)
           pf1 b R = refl
           pf2 : (E' ⇄ A') ≗⅁ (E' ⇄↺ A'-beh↺)
           pf2 b R = refl
           pf6 : proj₁ ∘ run↺ A-beh↺-spec ≗ proj₁ ∘ A-beh
           pf6 R = refl
           pf8 : ∀ R → proj₂ (A-beh-spec R) ≗ pre-post-E-spec (proj₂ (A'-beh R))
           pf8 R C = refl
           open FunctionExtra
           pf9 : ∀ S C → SemSecAdv.beh₂ A S C ≡ pre-post-E-spec (SemSecAdv.beh₂ A' S) C
           pf9 S C = {!refl!}
           pf7 : ∀ R → proj₂ (A-beh-spec R) ≗ proj₂ (A-beh R) 
           pf7 R C = {!refl!}
           pf5 : A-beh↺-spec FF'.≗A A-beh↺
           pf5 R = pf6 R , pf7 R
           pf4 : (E ⇄↺ A-beh↺-spec) ≗⅁ (E ⇄ A)
           pf4 = FF'.change-adv {E = E} pf5
           same-games' : (E' ⇄ A') ≗⅁ (E ⇄↺ A-beh↺-spec)
           same-games' b R = refl
           same-games : (E' ⇄ A') ≗⅁ (E ⇄ A)
           same-games = FF'.≗⅁-trans same-games' pf4
           A-breaks-E : breaks (E ⇄ A)
           A-breaks-E = ext-as-broken same-games A'-breaks-E'
-}
{-
  ⊕-pres-sem-sec : ∀ mask → SemSecReduction (_∘_ (_⊕_ mask))
-}
