module otp-sem-sec where

import Level as L
open import Function
open import Data.Nat.NP
open import Data.Bits
open import Data.Bool
open import Data.Bool.Properties
open import Data.Vec hiding (_>>=_)
open import Data.Product.NP hiding (_⟦×⟧_)
-- open import circuit
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.NP
open import flipbased-implem
open ≡-Reasoning
open import Data.Unit using (⊤)
open import composable
open import vcomp
open import forkable

proj : ∀ {a} {A : Set a} → A × A → Bit → A
proj (x₀ , x₁) 0b = x₀
proj (x₀ , x₁) 1b = x₁

module FunctionExtra where
  _***_ : ∀ {A B C D : Set} → (A → B) → (C → D) → A × C → B × D
  (f *** g) (x , y) = (f x , g y)
  -- Fanout
  _&&&_ : ∀ {A B C : Set} → (A → B) → (A → C) → A → B × C
  (f &&& g) x = (f x , g x)
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

same-power : Power → Power
same-power = id

_+ᵖ_ : Power → Power → Power
(mk c₀ s₀ t₀) +ᵖ (mk c₁ s₁ t₁) = mk (c₀ + c₁) (s₀ + s₁) (t₀ + t₁)

powerComp : Composable (ConstArr Power)
powerComp = constComp _+ᵖ_

powerVComp : VComposable _ (ConstArr Power)
powerVComp = constVComp (λ { (Power.mk c₀ s₀ t₀) (mk c₁ s₁ t₁) → mk (c₀ + c₁) (s₀ + s₁) (t₀ ⊔ t₁) })

record PrgDist : Set₁ where
  constructor mk
  field
    _]-[_ : ∀ {c} (f g : ↺ c Bit) → Set
    ]-[-cong : ∀ {c} {f f' g g' : ↺ c Bit} → f ≗↺ g → f' ≗↺ g' → f ]-[ f' → g ]-[ g'

  breaks : ∀ {c} (EXP : Bit → ↺ c Bit) → Set
  breaks ⅁ = ⅁ 0b ]-[ ⅁ 1b

  _≗⅁_ : ∀ {c} (⅁₀ ⅁₁ : Bit → ↺ c Bit) → Set
  ⅁₀ ≗⅁ ⅁₁ = ∀ b → ⅁₀ b ≗↺ ⅁₁ b

  ≗⅁-trans : ∀ {c} → Transitive (_≗⅁_ {c})
  ≗⅁-trans p q b R = trans (p b R) (q b R)

module Guess (prgDist : PrgDist) where
  open PrgDist prgDist

  GuessAdv : Coins → Set
  GuessAdv c = ↺ c Bit

  runGuess⅁ : ∀ {ca} (A : GuessAdv ca) (b : Bit) → ↺ ca Bit
  runGuess⅁ A _ = A

  -- An oracle: an adversary who can break the guessing game.
  Oracle : Power → Set
  Oracle power = ∃ (λ (A : GuessAdv (coins power)) → breaks (runGuess⅁ A))

  -- Any adversary cannot do better than a random guess.
  GuessSec : Power → Set
  GuessSec power = ∀ (A : GuessAdv (coins power)) → ¬(breaks (runGuess⅁ A))

record FlatFuns (Power : Set) {t} (T : Set t) : Set (L.suc t) where
  constructor mk
  field
    `Bits   : ℕ → T
    `Bit    : T
    _`×_    : T → T → T
    ⟨_⟩_↝_  : Power → T → T → Set
  infixr 2 _`×_
  infix 0 ⟨_⟩_↝_

record PowerOps (Power : Set) : Set where
  constructor mk
  field
    _>>>ᵖ_ _***ᵖ_ : Power → Power → Power

constPowerOps : PowerOps ⊤
constPowerOps = _

record FlatFunsOps {P t} {T : Set t} (powerOps : PowerOps P) (♭Funs : FlatFuns P T) : Set t where
  constructor mk
  open FlatFuns ♭Funs
  open PowerOps powerOps
  field
    idO : ∀ {A p} → ⟨ p ⟩ A ↝ A
    isIComposable  : IComposable  {I = ⊤} _>>>ᵖ_ ⟨_⟩_↝_
    isVIComposable : VIComposable {I = ⊤} _***ᵖ_ _`×_ ⟨_⟩_↝_
  open IComposable isIComposable public
  open VIComposable isVIComposable public

fun♭Funs : FlatFuns ⊤ Set
fun♭Funs = mk Bits Bit _×_ (λ _ A B → A → B)

record AbsSemSecAdv |M| |C|
                 {Power : Set} {t} {T : Set t} (♭Funs : FlatFuns Power T)
                 (p₀ p₁ : Power) (|R| : Coins) : Set where
  constructor _,_

  open FlatFuns ♭Funs

  field
    {|S|} : ℕ

  S = `Bits |S|
  R = `Bits |R|
  M = `Bits |M|
  C = `Bits |C|

  field
    step₀ : ⟨ p₀ ⟩ R ↝ (M `× M) `× S
    step₁ : ⟨ p₁ ⟩ C `× S ↝ `Bit

module FunAdv (prgDist : PrgDist) (|M| |C| : ℕ) where
  open PrgDist prgDist

  M = Bits |M|
  C = Bits |C|
  -- module AbsSemSecAdv' |R| = AbsSemSecAdv {|M|} {|C|} {fun♭Funs} |R|

  -- open AbsSemSecAdv' using (M; C)

  M² = Bit → M

  Enc : ∀ cc → Set
  Enc cc = M → ↺ cc C

  record FunSemSecAdv |R| : Set where
    constructor mk

    field
      semSecAdv : AbsSemSecAdv |M| |C| fun♭Funs _ _ |R|

    open AbsSemSecAdv semSecAdv public hiding (M; C)

    step₀F : R → (M² × S)
    step₀F = step₀ >>> proj *** id
      where open FunctionExtra

    step₀↺ : ↺ |R| (M² × S)
    step₀↺ = mk step₀F

    step₁F : S → C → Bit
    step₁F s c = step₁ (c , s)

  -- Returing 0 means Chal wins, Adv looses
  --          1 means Adv  wins, Chal looses
  runSemSec : ∀ {cc ca} (E : Enc cc) (A : FunSemSecAdv ca) b → ↺ (ca + cc) Bit
  runSemSec E A b
    = A-step₀ >>= λ { (m , s) → map↺ (A-step₁ s) (E (m b)) }
    where open FunSemSecAdv A renaming (step₀↺ to A-step₀; step₁F to A-step₁)

  _⇄_ : ∀ {cc ca} (E : Enc cc) (A : FunSemSecAdv ca) b → ↺ (ca + cc) Bit
  _⇄_ = runSemSec

  runAdv : ∀ {|R|} → FunSemSecAdv |R| → C → Bits |R| → (M × M) × Bit
  runAdv (mk (A-step₀ , A-step₁)) C = A-step₀ >>> id *** (const C &&& id >>> A-step₁)
    where open FunctionExtra

  _≗A_ : ∀ {p} (A₁ A₂ : FunSemSecAdv p) → Set
  A₀ ≗A A₁ = ∀ C R → runAdv A₀ C R ≡ runAdv A₁ C R

  change-adv : ∀ {cc p} {E : Enc cc} {A₁ A₂ : FunSemSecAdv p} → A₁ ≗A A₂ → (E ⇄ A₁) ≗⅁ (E ⇄ A₂)
  change-adv {cc} {ca} {E} {A₁} {A₂} pf b R with splitAt ca R
  change-adv {cc} {ca} {E} {A₁} {A₂} pf b ._ | pre , post , refl = trans (cong proj₂ (helper₀ A₁)) helper₂
     where open FunSemSecAdv
           helper₀ = λ A → pf (run↺ (E (proj (proj₁ (step₀ A pre)) b)) post) pre
           helper₂ = cong (λ m → step₁ A₂ (run↺ (E (proj (proj₁ m) b)) post , proj₂ (step₀ A₂ pre)))
                          (helper₀ A₂)

  ext-as-broken : ∀ {c} {⅁₀ ⅁₁ : Bit → ↺ c Bit}
                  → ⅁₀ ≗⅁ ⅁₁ → breaks ⅁₀ → breaks ⅁₁
  ext-as-broken same-games = ]-[-cong (same-games 0b) (same-games 1b)

  SemBroken : ∀ {cc} (E : Enc cc) → Power → Set
  SemBroken E power = ∃ (λ (A : FunSemSecAdv (coins power)) → breaks (E ⇄ A))

  Tr : (cc₀ cc₁ : Coins) → Set
  Tr cc₀ cc₁ = Enc cc₀ → Enc cc₁

  -- SemSecReduction p₀ p₁ E₀ E₁:
  --   security of E₀ reduces to security of E₁
  --   breaking E₁ reduces to breaking E₀
  SemSecReduction : ∀ (p₀ p₁ : Power) {cc₀ cc₁} (E₀ : Enc cc₀) (E₁ : Enc cc₁) → Set
  SemSecReduction p₀ p₁ E₀ E₁ = SemBroken E₁ p₁ → SemBroken E₀ p₀

  SemSecTr : ∀ {cc₀ cc₁} (f : Power → Power) (tr : Tr cc₀ cc₁) → Set
  SemSecTr {cc₀} {cc₁} f tr = ∀ {p} {E : Enc cc₀} → SemSecReduction (f p) p E (tr E)

  -- SemSecReductionToOracle : ∀ (p₀ p₁ : Power) {cc} (E : Enc cc) → Set
  -- SemSecReductionToOracle = SemBroken E p₀ → Oracle p₁

  open FunctionExtra

  -- post-comp : ∀ {cc k} (post-E : C → ↺ k C) → Tr cc (cc + k)
  -- post-comp post-E E = E >=> post-E

  post-comp : ∀ {cc} (post-E : C → C) → Tr cc cc
  post-comp post-E E = E >>> map↺ post-E

  post-comp-pres-sem-sec : ∀ {cc} (post-E : C → C)
                           → SemSecTr same-power (post-comp {cc} post-E)
  post-comp-pres-sem-sec post-E (mk (A'₀ , A'₁) , A'-breaks-E') = A , A'-breaks-E'
     where A = mk (A'₀ , (post-E *** id >>> A'₁))

  post-comp-pres-sem-sec' : ∀ (post-E post-E⁻¹ : C → C)
                              (post-E-inv : post-E⁻¹ ∘ post-E ≗ id)
                              {cc p} {E : Enc cc}
                            → SemSecReduction p p (post-comp post-E E) E
  post-comp-pres-sem-sec' post-E post-E⁻¹ post-E-inv {cc} {p} {E} (A , A-breaks-E)
       = A' , A'-breaks-E'
     where E' = post-comp post-E E
           open FunSemSecAdv A renaming (step₀ to A₀; step₀F to A₀F; step₁ to A₁)
           A' = mk (A₀ , (post-E⁻¹ *** id >>> A₁))
           same-games : (E ⇄ A) ≗⅁ (E' ⇄ A')
           same-games b R
             rewrite post-E-inv (run↺ (E (proj₁ (A₀F (take (coins p) R)) b))
                                       (drop (coins p) R)) = refl
           A'-breaks-E' : breaks (E' ⇄ A')
           A'-breaks-E' = ext-as-broken same-games A-breaks-E

  post-neg : ∀ {cc} → Tr cc cc
  post-neg E = E >>> map↺ vnot

  post-neg-pres-sem-sec : ∀ {cc} → SemSecTr same-power (post-neg {cc})
  post-neg-pres-sem-sec {cc} {p} {E} = post-comp-pres-sem-sec vnot {p} {E}

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

-- Actually Ops + Spec
record FlatFunsSpec {t} {T : Set t} (♭Funs : FlatFuns ⊤ T) : Set (L.suc L.zero L.⊔ t) where
  constructor mk

  open FlatFuns ♭Funs
  Cp : T → T → Set
  Cp = ⟨_⟩_↝_ _

  field
    ⟦_⟧ : T → Set
    _⟦×⟧_ : ∀ {i₀ i₁} → ⟦ i₀ ⟧ → ⟦ i₁ ⟧ → ⟦ i₀ `× i₁ ⟧
    ♭ops : FlatFunsOps constPowerOps ♭Funs
    =[]= : ∀ {i o} → Cp i o → ⟦ i ⟧ → ⟦ o ⟧ → Set

  _=[_]=_ : ∀ {i o} → ⟦ i ⟧ → Cp i o → ⟦ o ⟧ → Set
  _=[_]=_ = λ is c os → =[]= c is os

  open FlatFunsOps ♭ops
  field
    idC-spec : ∀ {i} (bs : ⟦ i ⟧) → bs =[ idO ]= bs
    >>>-spec : IComposable  {_↝ᵢ_ = Cp} _>>>_ =[]=
    ***-spec : VIComposable {_↝ᵢ_ = Cp} _***_ _⟦×⟧_ =[]=

    runC : ∀ {i o} → Cp i o → ⟦ i ⟧ → ⟦ o ⟧
    runC-spec : ∀ {i o} (c : Cp i o) is → is =[ c ]= runC c is
{-
    splitAtC : ∀ k {n} → ⟦ `Bits (k + n) ⟧ → (⟦ `Bits k ⟧ × ⟦ `Bits n ⟧)
    splitAtC2 : ∀ k {n} → ⟦ `Bits (k + n) ⟧ → (⟦ `Bits k `× `Bits n ⟧)
    splitAtC3 : ∀ k {n} → Cp (`Bits (k + n)) (`Bits k `× `Bits n)
    splitAtC4 : ∀ k {n} → (⟦ `Bits k `× `Bits n ⟧) → (⟦ `Bits k ⟧ × ⟦ `Bits n ⟧)
-}

{-
module CpAdv
  {t}
  {T : Set t}
  (♭Funs : FlatFuns ⊤ T)
  (♭FunsSpec : FlatFunsSpec ♭Funs)
  -- (FCp : Coins → Size → Time → Ports → Ports → Set)
  -- (toC : ∀ {c s t i o} → FCp c s t i o → Cp (c + i) o)

  (prgDist : PrgDist)
  (|M| |C| : ℕ)

  where
  open FlatFuns ♭Funs
  open FlatFunsSpec ♭FunsSpec
  open FlatFunsOps  ♭ops

  open PrgDist prgDist
  `M = `Bits |M|
  `C = `Bits |C|
  M = ⟦ `M ⟧
  C = ⟦ `C ⟧
  M² = Bit → M

  -- module FunAdv' = FunAdv prgDist |M| |C|
  -- open FunAdv' public using (mk; {-module SplitSemSecAdv;-} FunSemSecAdv; M; C; M²; Enc; Tr; ext-as-broken; change-adv; _≗A_) renaming (_⇄_ to _⇄F_)

  module FE = FunctionExtra

  record CpSemSecAdv power : Set where
    constructor mk

    open Power power renaming (coins to |R|; size to s; time to t)

    -- open FunctionExtra

    field
      semSecAdv : AbsSemSecAdv |M| |C| ♭Funs _ _ |R|

    open AbsSemSecAdv semSecAdv public hiding (M; C; R; S)

    `R = `Bits |R|
    `S = `Bits |S|
    R = ⟦ `R ⟧
    S = ⟦ `S ⟧

    step₀f : R → ((M × M) × S)
    step₀f = runC step₀ FE.>>> {!splitAtC4 (|M| + |M|) FE.>>> {!splitAtC |M| FE.*** id!}!}

    -- step₀f : R → ((M × M) × S)
    -- step₀f = runC step₀ FE.>>> {!splitAtC3 (|M| + |M|) FE.>>> {!splitAtC |M| FE.*** id!}!}

    step₀F : R → (M² × S)
    step₀F = step₀f >>> proj *** id

    step₀↺ : ↺ |R| (M² × S)
    step₀↺ = mk step₀F

    step₁f : C × S → Bit
    step₁f (c , s) = head (runC step₁ (c ++ s))

    step₁F : S → C → Bit
    step₁F s c = step₁f (c , s)

--    funAdv : FunSemSecAdv |R|
--    funAdv = mk (step₀f , step₁f) 

{-
  record SemSecAdv+FunBeh power : Set where
    constructor mk

    open Power power renaming (coins to c; size to s; time to t)

    field
      Acp : CpSemSecAdv power
      A↺ : FunSemSecAdv c

    open CpSemSecAdv Acp renaming (beh↺ to Acp-beh↺; beh to Acp-beh; beh₂ to Acp-beh₂; beh₁ to Acp-beh₁)
    A↺-beh : R → M² × (C → Bit)
    A↺-beh = run↺ A↺

    module SplitA↺ = SplitSemSecAdv A↺
    open SplitA↺ using () renaming (beh₁ to As-beh₁; beh₂ to As-beh₂)

    field
      coh₁ : Acp-beh₁ ≗ As-beh₁
      coh₂ : ∀ R → Acp-beh₂ R ≗ As-beh₂ R

    coh : CpSemSecAdv.adv↺ Acp ≗A A↺
    coh = coh₁ , coh₂
-}
  -- Returing 0 means Chal wins, Adv looses
  --          1 means Adv  wins, Chal looses
  _⇄_ : ∀ {cc p} (E : Enc cc) (A : CpSemSecAdv p) b → ↺ (coins p + cc) Bit
  E ⇄ A = E ⇄F CpSemSecAdv.funAdv A

  SemBroken : ∀ {cc} (E : Enc cc) → Power → Set
  SemBroken E power = ∃ (λ (A : CpSemSecAdv power) → breaks (E ⇄ A))

  -- SemSecReduction p₀ p₁ E₀ E₁:
  --   security of E₀ reduces to security of E₁
  --   breaking E₁ reduces to breaking E₀
  SemSecReduction : ∀ (p₀ p₁ : Power) {cc₀ cc₁} (E₀ : Enc cc₀) (E₁ : Enc cc₁) → Set
  SemSecReduction p₀ p₁ E₀ E₁ = SemBroken E₁ p₁ → SemBroken E₀ p₀

  SemSecTr : ∀ {cc₀ cc₁} (f : Power → Power) (tr : Tr cc₀ cc₁) → Set
  SemSecTr {cc₀} {cc₁} f tr = ∀ {p} {E : Enc cc₀} → SemSecReduction (f p) p E (tr E)

  post-comp-cp : ∀ {cc} post-E → Tr cc cc
  post-comp-cp post-E E = E >>> map↺ (runC post-E)
    where open FunctionExtra

  post-comp-pres-sem-sec : ∀ {cc} (post-E : Cp |C| |C|) → SemSecTr same-power (post-comp-cp {cc} post-E)
  post-comp-pres-sem-sec {cc} post-E {p} {E} (A' , A'-breaks-E') = A , A-breaks-E
     where E' : Enc cc
           E' = post-comp-cp post-E E
           open Power p renaming (coins to c)
           open CpSemSecAdv A' using (R; S; |S|; step₀) renaming (step₀f to A'-step₀f; step₁f to A'-step₁f; step₁ to A'-step₁)
           A-step₁-spec = runC post-E *** id >>> A'-step₁f
             where open FunctionExtra
           A-spec : FunSemSecAdv (coins p)
           A-spec = mk (A'-step₀f , A-step₁-spec)
           open FlatFunsOps ♭ops
           A-step₁ = post-E *** idO {|S|} >>> A'-step₁
           A : CpSemSecAdv p
           A = mk (step₀ , A-step₁)
           open CpSemSecAdv A using () renaming (funAdv to funA; step₀f to A-step₀f; step₁f to A-step₁f)

           coh₁ : A-step₁-spec ≗ A-step₁f
           coh₁ (C , S) rewrite >>>-spec (post-E *** idO {|S|}) A'-step₁ (C ++ S)
                         | ***-spec post-E (idO {|S|}) C {S}
                         | idC-spec S = refl
           pf3 : A-spec ≗A funA
           pf3 C R rewrite coh₁ (C , proj₂ (A-step₀f R)) = refl
           same-games : (E' ⇄ A') ≗⅁ (E ⇄ A)
           same-games = change-adv {E = E} {A-spec} {funA} pf3
           A-breaks-E : breaks (E ⇄ A)
           A-breaks-E = ext-as-broken same-games A'-breaks-E'

{-
  ⊕-pres-sem-sec : ∀ mask → SemSecReduction (_∘_ (_⊕_ mask))
-}

{-
funBits-kit : FlatFunsSpec
funBits-kit = mk _→ᵇ_ bitsFunCircuitBuilder id idC-spec >>>-spec ***-spec where
  open CircuitBuilder bitsFunCircuitBuilder
  open BitsFunExtras

module Concrete k where
  _]-[_ : ∀ {c} (f g : ↺ c Bit) → Set
  _]-[_ f g = f ]- k -[ g
  cong' : ∀ {c} {f f' g g' : ↺ c Bit} → f ≗↺ g → f' ≗↺ g' → f ]-[ f' → g ]-[ g'
  cong' = ]-[-cong {k}
  prgDist : PrgDist
  prgDist = mk _]-[_ cong'
  module Guess' = Guess prgDist
  module FunAdv' = FunAdv prgDist
  module CpAdv' = CpAdv funBits-kit prgDist
-}

{-
module OTP (prgDist : PrgDist) where
  open FunAdv prgDist 1 1
  open Guess prgDist renaming (breaks to reads-your-mind)

  -- OTP₁ : ∀ {c} (k : Bit) → Enc c
  -- OTP₁ k m = return↺ ((k xor (head m)) ∷ [])

  OTP₁ : Enc 1
  OTP₁ m = map↺ (λ k → (k xor (head m)) ∷ []) toss

  open FunctionExtra

  -- ∀ k → SemSecReductionToOracle no-power no-power (OTP₁ k)
  foo : ∀ p → SemBroken OTP₁ p → Oracle {!(mk 1 0 0 +ᵖ p)!}
  foo p (A , A-breaks-OTP) = O , O-reads-your-mind
     where postulate
             b : Bit
           -- b = {!!}
             k : Bit
           -- k = {!!}
           O : ↺ (coins p + 1) Bit
           O = A >>= λ { (m , kont) → map↺ (_xor_ (head (m b)) ∘ kont) (OTP₁ (m b)) } --  (k ∷ []))) }
           O-reads-your-mind : reads-your-mind (runGuess⅁ O)
           O-reads-your-mind = {!!}
{-
    A >>= λ { (m , kont) → map↺ kont (OTP₁ (m b)) }
    A >>= λ { (m , kont) → map↺ kont (map↺ (λ k → (k xor (head (m b))) ∷ []) toss) }
    A >>= λ { (m , kont) → map↺ (kont ∘ λ k → (k xor (head (m b))) ∷ []) toss) }
    A >>= λ { (m , kont) → map↺ (λ k → kont ((k xor (head (m b))) ∷ []) toss) }
    A >>= λ { (m , kont) → map↺ (λ k → kont ((k xor (head (m b))) ∷ []) (choose (return↺ 0b) (return↺ 1b))) }
    A >>= λ { (m , kont) → choose (kont ((0b xor (head (m b))) ∷ []))
                                   (kont ((1b xor (head (m b))) ∷ [])) }
    A >>= λ { (m , kont) → choose (kont (head (m b) ∷ []))
                                   (kont (not (head (m b)) ∷ [])) }

kont = const b
    A >>= λ { (m , kont) → map↺ kont (OTP₁ (m b)) }
    A >>= λ { (m , kont) → map↺ (const b) (OTP₁ (m b)) }
    A >>= λ { (m , kont) → toss >> return b }

kont = const b
    A >>= λ { (m , kont) → map↺ (λ c → c xor head (m (kont c))) (OTP₁ (m b)) }
    A >>= λ { (m , kont) → map↺ (_xor_ (head (m b)) ∘ const b) (OTP₁ (m b)) }
    A >>= λ { (m , kont) → map↺ (const (head (m b) xor b)) (OTP₁ (m b)) }
    A >>= λ { (m , kont) → return↺ (head (m b) xor b) }

---
    A >>= λ { (m , kont) → map↺ (_xor_ (head (m b)) ∘ kont) (OTP₁ (m b)) }
    A >>= λ { (m , kont) → map↺ (_xor_ (head (m b)) ∘ kont) (map↺ (λ k → (k xor (head (m b))) ∷ []) toss) }
    A >>= λ { (m , kont) → map↺ (_xor_ (head (m b)) ∘ kont ∘ λ k → (k xor (head (m b))) ∷ []) toss) }
    A >>= λ { (m , kont) → map↺ (λ k → (head (m b)) xor (kont ((k xor (head (m b))) ∷ [])) toss) }
    A >>= λ { (m , kont) → choose ((head (m b)) xor (kont ((0b xor (head (m b))) ∷ [])))
                                   ((head (m b)) xor (kont ((1b xor (head (m b))) ∷ [])))
            }
-}
-}
-}
