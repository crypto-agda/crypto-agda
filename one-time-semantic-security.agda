module one-time-semantic-security where

open import Function
open import Data.Nat
open import flat-funs
open import Data.Vec using (splitAt; take; drop)
open import program-distance
open import Data.Bits
open import flipbased-implem
open import Data.Product
open import Relation.Binary.PropositionalEquality

record EncParams : Set where
  constructor mk
  field
    |M| |C| |R|e : ℕ

  M  = Bits |M|
  C  = Bits |C|
  Re = Bits |R|e

  -- The type of the encryption function
  Enc : Set
  Enc = M → ↺ |R|e C

module AbsSemSec {t} {T : Set t}
                 (♭Funs : FlatFuns T) where

  open FlatFuns ♭Funs

  record SemSecAdv (ep : EncParams) |R|a : Set where
    constructor mk

    open EncParams ep hiding (M; C; Re)

    field
      {|S|} : ℕ

    M  = `Bits |M|
    C  = `Bits |C|
    Re = `Bits |R|e
    S  = `Bits |S|

    -- Randomness adversary
    Ra = `Bits |R|a

    field
      step₀ : Ra `→ (M `× M) `× S
      step₁ : C `× S `→ `Bit

    open EncParams ep public hiding (M; C; Re)

  SemSecReduction : ∀ ep ep' (f : Coins → Coins) → Set
  SemSecReduction ep ep' f = ∀ {c} → SemSecAdv ep c → SemSecAdv ep' (f c)



-- Here we use Agda functions for FlatFuns.
module FunSemSec (prgDist : PrgDist) where
  open PrgDist prgDist
  open AbsSemSec fun♭Funs
  open FlatFunsOps fun♭Ops

  module FunSemSecAdv {ep : EncParams} {|R|a} (A : SemSecAdv ep |R|a) where
    open SemSecAdv A public

    M² = Bit → M

    step₀F : Ra → (M² × S)
    step₀F = step₀ >>> proj *** idO

    step₀↺ : ↺ |R|a (M² × S)
    step₀↺ = mk step₀F

    step₁F : S → C → Bit
    step₁F s c = step₁ (c , s)

  module RunSemSec (ep : EncParams) where
    open EncParams ep using (M; C; |R|e; Enc)

    -- Returing 0 means Chal wins, Adv looses
    --          1 means Adv  wins, Chal looses
    runSemSec : ∀ {|R|a} (E : Enc) (A : SemSecAdv ep |R|a) b → ↺ (|R|a + |R|e) Bit
    runSemSec E A b
      = A-step₀ >>= λ { (m , s) → map↺ (A-step₁ s) (E (m b)) }
      where open FunSemSecAdv A renaming (step₀↺ to A-step₀; step₁F to A-step₁)

    _⇄_ : ∀ {|R|a} (E : Enc) (A : SemSecAdv ep |R|a) b → ↺ (|R|a + |R|e) Bit
    _⇄_ = runSemSec

    runAdv : ∀ {|R|} → SemSecAdv ep |R| → C → Bits |R| → (M × M) × Bit
    runAdv (mk A-step₀ A-step₁) C = A-step₀ >>> id *** (const C &&& id >>> A-step₁)

    _≗A_ : ∀ {p} (A₁ A₂ : SemSecAdv ep p) → Set
    A₀ ≗A A₁ = ∀ C R → runAdv A₀ C R ≡ runAdv A₁ C R

    change-adv : ∀ {ca E} {A₁ A₂ : SemSecAdv ep ca} → A₁ ≗A A₂ → (E ⇄ A₁) ≗⅁ (E ⇄ A₂)
    change-adv {ca = ca} {A₁ = _} {_} pf b R with splitAt ca R
    change-adv {E = E} {A₁} {A₂} pf b ._ | pre Σ., post , refl = trans (cong proj₂ (helper₀ A₁)) helper₂
       where open FunSemSecAdv
             helper₀ = λ A → pf (run↺ (E (proj (proj₁ (step₀ A pre)) b)) post) pre
             helper₂ = cong (λ m → step₁ A₂ (run↺ (E (proj (proj₁ m) b)) post , proj₂ (step₀ A₂ pre)))
                            (helper₀ A₂)

    _≗E_ : ∀ (E₀ E₁ : Enc) → Set
    E₀ ≗E E₁ = ∀ m → E₀ m ≗↺ E₁ m

    ≗E→≗⅁ : ∀ {E₀ E₁} → E₀ ≗E E₁ → ∀ {c} (A : SemSecAdv ep c)
               → (E₀ ⇄ A) ≗⅁ (E₁ ⇄ A)
    ≗E→≗⅁ E₀≗E₁ {c} A b R
      rewrite E₀≗E₁ (proj (proj₁ (SemSecAdv.step₀ A (take c R))) b) (drop c R) = refl

    ≗E→⇓ : ∀ {E₀ E₁} → E₀ ≗E E₁ → ∀ {c} (A : SemSecAdv ep c) → (E₀ ⇄ A) ⇓ (E₁ ⇄ A)
    ≗E→⇓ E₀≗E₁ A = extensional-reduction (≗E→≗⅁ E₀≗E₁ A)

  module SemSecReductions (ep ep' : EncParams) where 
    module EP = EncParams ep
    module EP' = EncParams ep'
    open EP public using (Enc; |R|e; Re)
    open RunSemSec ep public
    open EP' public using () renaming (Enc to Enc'; |R|e to |R|e')
    open RunSemSec ep' public using () renaming (_⇄_ to _⇄'_; _≗E_ to _≗E'_; ≗E→⇓ to ≗E→⇓')

    Tr : Set
    Tr = Enc → Enc'

    Tr⁻¹ : Set
    Tr⁻¹ = Enc' → Enc

    private -- unused
      SafeSemSecReduction : ∀ (f : Coins → Coins) (_≈_ : Enc → Enc' → Set) → Set
      SafeSemSecReduction f _≈_ =
        ∃ λ (red : SemSecReduction ep ep' f) →
          ∀ {E₀ : Enc} {E₁ : Enc'} {c} A → E₀ ≈ E₁ → (E₀ ⇄ A) ⇓ (E₁ ⇄' red {c} A)

    SemSecTr : ∀ (f : Coins → Coins) (tr : Tr) → Set
    SemSecTr f tr =
      ∃ λ (red : SemSecReduction ep' ep f) →
        ∀ E {c} A → (tr E ⇄' A) ⇓ (E ⇄ red {c} A)

    SemSecTr⁻¹ : ∀ (f : Coins → Coins) (tr⁻¹ : Tr⁻¹) → Set
    SemSecTr⁻¹ f tr⁻¹ =
      ∃ λ (red : SemSecReduction ep' ep f) →
        ∀ E {c} A → (E ⇄' A) ⇓ (tr⁻¹ E ⇄ red {c} A)

    SemSecTr→SemSecTr⁻¹ : ∀ tr tr⁻¹ (tr-right-inv : ∀ E → tr (tr⁻¹ E) ≗E' E)
                            {f} → SemSecTr f tr → SemSecTr⁻¹ f tr⁻¹
    SemSecTr→SemSecTr⁻¹ _ tr⁻¹ tr-inv (red , pf) = red , helper
      where helper : ∀ (E : Enc') {c} A → (E ⇄' A) ⇓ (tr⁻¹ E ⇄ red {c} A)
            helper E A A-breaks-E = pf (tr⁻¹ E) A A-breaks-trtr⁻¹E
              where A-breaks-trtr⁻¹E = ≗E→⇓' (λ m R → sym (tr-inv E m R)) A A-breaks-E

    SemSecTr⁻¹→SemSecTr : ∀ tr tr⁻¹ (tr-left-inv : ∀ E → tr⁻¹ (tr E) ≗E E)
                           {f} → SemSecTr⁻¹ f tr⁻¹ → SemSecTr f tr
    SemSecTr⁻¹→SemSecTr tr _ tr-inv (red , pf) = red , helper
      where helper : ∀ (E : Enc) {c} A → (tr E ⇄' A) ⇓ (E ⇄ red {c} A)
            helper E {c} A A-breaks-E = ≗E→⇓ (tr-inv E) (red A) (pf (tr E) A A-breaks-E)

