module one-time-semantic-security where

open import Function
open import Data.Nat
open import Data.Product using (∃; module Σ; _×_; _,_; proj₁; proj₂)
open import Data.Vec using (splitAt; take; drop)
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≗_)

open import Data.Bits

open import flat-funs
open import program-distance
open import flipbased-implem

-- Capture the various size parameters required
-- for a cipher.
--
-- M  is the message space (|M| is the size of messages)
-- C  is the cipher text space
-- Rᵉ is the randomness used by the cipher.
record EncParams : Set where
  constructor mk
  field
    |M| |C| |R|ᵉ : ℕ

  M  = Bits |M|
  C  = Bits |C|
  Rᵉ = Bits |R|ᵉ

  -- The type of the encryption function
  Enc : Set
  Enc = M → ↺ |R|ᵉ C

module EncParams² (ep₀ ep₁ : EncParams) where
  open EncParams ep₀ public using ()
    renaming (|M| to |M|₀; |C| to |C|₀; |R|ᵉ to |R|ᵉ₀; M to M₀;
              C to C₀; Rᵉ to Rᵉ₀; Enc to Enc₀)
  open EncParams ep₁ public using ()
    renaming (|M| to |M|₁; |C| to |C|₁; |R|ᵉ to |R|ᵉ₁; M to M₁;
              C to C₁; Rᵉ to Rᵉ₁; Enc to Enc₁)
  Tr   = Enc₀ → Enc₁
  Tr⁻¹ = Enc₁ → Enc₀

module EncParams²-same-|R|ᵉ (ep₀ : EncParams) (|M|₁ |C|₁ : ℕ) where
  ep₁ = EncParams.mk |M|₁ |C|₁ (EncParams.|R|ᵉ ep₀)
  open EncParams² ep₀ ep₁ public

module ♭EncParams {t} {T : Set t}
                  (♭Funs : FlatFuns T)
                  (ep : EncParams) where
  open FlatFuns ♭Funs
  open EncParams ep public

  `M  = `Bits |M|
  `C  = `Bits |C|
  `Rᵉ = `Bits |R|ᵉ

module ♭EncParams² {t} {T : Set t}
                   (♭Funs : FlatFuns T)
                   (ep₀ ep₁ : EncParams) where
  open EncParams² ep₀ ep₁ public
  open ♭EncParams ♭Funs ep₀ public using () renaming (`M to `M₀; `C to `C₀; `Rᵉ to `Rᵉ₀)
  open ♭EncParams ♭Funs ep₁ public using () renaming (`M to `M₁; `C to `C₁; `Rᵉ to `Rᵉ₁)

module AbsSemSec {t} {T : Set t}
                 (♭Funs : FlatFuns T) where

  open FlatFuns ♭Funs

  record SemSecAdv (ep : EncParams) |R|ᵃ : Set where
    constructor mk

    open ♭EncParams ♭Funs ep

    field
      {|S|} : ℕ

    `S  = `Bits |S|
    S   =  Bits |S|

    -- Randomness adversary
    `Rᵃ = `Bits |R|ᵃ
    Rᵃ  =  Bits |R|ᵃ

    field
      step₀ : `Rᵃ `→ (`M `× `M) `× `S
      step₁ : `C `× `S `→ `Bit

    M²  = Bit → M
    `M² = `Bit `→ `M

    module Ops (♭ops : FlatFunsOps ♭Funs) where
      open FlatFunsOps ♭ops
      observe : `C `× `Rᵃ `→ (`M `× `M) `× `Bit
      observe = idO *** step₀ >>> ⟨C,⟨M,S⟩⟩→⟨M¸⟨C,S⟩⟩ >>> idO *** step₁
        where ⟨C,⟨M,S⟩⟩→⟨M¸⟨C,S⟩⟩ = < snd >>> fst , < fst , snd >>> snd > >

    open ♭EncParams ♭Funs ep public

  SemSecReduction : ∀ ep₀ ep₁ (f : Coins → Coins) → Set
  SemSecReduction ep₀ ep₁ f = ∀ {c} → SemSecAdv ep₀ c → SemSecAdv ep₁ (f c)

-- Here we use Agda functions for FlatFuns.
module FunSemSec (prgDist : PrgDist) where
  open PrgDist prgDist
  open AbsSemSec fun♭Funs
  open FlatFunsOps fun♭Ops

  module FunSemSecAdv {ep : EncParams} {|R|ᵃ} (A : SemSecAdv ep |R|ᵃ) where
    open SemSecAdv A public
    open Ops fun♭Ops public

    step₀F : Rᵃ → (M² × S)
    step₀F = step₀ >>> proj *** idO

    step₀↺ : ↺ |R|ᵃ (M² × S)
    step₀↺ = mk step₀F

    step₁F : S → C → Bit
    step₁F s c = step₁ (c , s)

  module RunSemSec (ep : EncParams) where
    open EncParams ep using (M; C; |R|ᵉ; Enc)

    -- Returing 0 means Chal wins, Adv looses
    --          1 means Adv  wins, Chal looses
    runSemSec : ∀ {|R|ᵃ} (E : Enc) (A : SemSecAdv ep |R|ᵃ) b → ↺ (|R|ᵃ + |R|ᵉ) Bit
    runSemSec E A b
      = A-step₀ >>= λ { (m , s) → map↺ (A-step₁ s) (E (m b)) }
      where open FunSemSecAdv A renaming (step₀↺ to A-step₀; step₁F to A-step₁)

    _⇄_ : ∀ {|R|ᵃ} (E : Enc) (A : SemSecAdv ep |R|ᵃ) b → ↺ (|R|ᵃ + |R|ᵉ) Bit
    _⇄_ = runSemSec

    _≗A_ : ∀ {p} (A₁ A₂ : SemSecAdv ep p) → Set
    A₀ ≗A A₁ = observe A₀ ≗ observe A₁
      where open FunSemSecAdv

    change-adv : ∀ {ca E} {A₁ A₂ : SemSecAdv ep ca} → A₁ ≗A A₂ → (E ⇄ A₁) ≗⅁ (E ⇄ A₂)
    change-adv {ca = ca} {A₁ = _} {_} pf b R with splitAt ca R
    change-adv {E = E} {A₁} {A₂} pf b ._ | pre Σ., post , ≡.refl = ≡.trans (≡.cong proj₂ (helper₀ A₁)) helper₂
       where open FunSemSecAdv
             helper₀ = λ A → pf (run↺ (E (proj (proj₁ (step₀ A pre)) b)) post , pre)
             helper₂ = ≡.cong (λ m → step₁ A₂ (run↺ (E (proj (proj₁ m) b)) post , proj₂ (step₀ A₂ pre)))
                              (helper₀ A₂)

    _≗E_ : ∀ (E₀ E₁ : Enc) → Set
    E₀ ≗E E₁ = ∀ m → E₀ m ≗↺ E₁ m

    ≗E→≗⅁ : ∀ {E₀ E₁} → E₀ ≗E E₁ → ∀ {c} (A : SemSecAdv ep c)
               → (E₀ ⇄ A) ≗⅁ (E₁ ⇄ A)
    ≗E→≗⅁ E₀≗E₁ {c} A b R
      rewrite E₀≗E₁ (proj (proj₁ (SemSecAdv.step₀ A (take c R))) b) (drop c R) = ≡.refl

    ≗E→⇓ : ∀ {E₀ E₁} → E₀ ≗E E₁ → ∀ {c} (A : SemSecAdv ep c) → (E₀ ⇄ A) ⇓ (E₁ ⇄ A)
    ≗E→⇓ E₀≗E₁ A = extensional-reduction (≗E→≗⅁ E₀≗E₁ A)

  module SemSecReductions (ep₀ ep₁ : EncParams) (f : Coins → Coins) where
    open EncParams² ep₀ ep₁
    open RunSemSec ep₀ public using () renaming (_⇄_ to _⇄₀_; _≗E_ to _≗E₀_; ≗E→⇓ to ≗E→⇓₀)
    open RunSemSec ep₁ public using () renaming (_⇄_ to _⇄₁_; _≗E_ to _≗E₁_; ≗E→⇓ to ≗E→⇓₁)

    Reduction : Set
    Reduction = SemSecReduction ep₁ ep₀ f

    SemSecTr : Tr → Set
    SemSecTr tr =
      ∃ λ (red : Reduction) →
        ∀ E {c} A → (tr E ⇄₁ A) ⇓ (E ⇄₀ red {c} A)

    SemSecTr⁻¹ : Tr⁻¹ → Set
    SemSecTr⁻¹ tr⁻¹ =
      ∃ λ (red : Reduction) →
        ∀ E {c} A → (E ⇄₁ A) ⇓ (tr⁻¹ E ⇄₀ red {c} A)

    SemSecTr→SemSecTr⁻¹ : ∀ tr tr⁻¹ (tr-right-inv : ∀ E → tr (tr⁻¹ E) ≗E₁ E)
                          → SemSecTr tr → SemSecTr⁻¹ tr⁻¹
    SemSecTr→SemSecTr⁻¹ _ tr⁻¹ tr-inv (red , pf) = red , helper
      where helper : ∀ E {c} A → (E ⇄₁ A) ⇓ (tr⁻¹ E ⇄₀ red {c} A)
            helper E A A-breaks-E = pf (tr⁻¹ E) A A-breaks-tr-tr⁻¹-E
              where A-breaks-tr-tr⁻¹-E = ≗E→⇓₁ (λ m R → ≡.sym (tr-inv E m R)) A A-breaks-E

    SemSecTr⁻¹→SemSecTr : ∀ tr tr⁻¹ (tr-left-inv : ∀ E → tr⁻¹ (tr E) ≗E₀ E)
                          → SemSecTr⁻¹ tr⁻¹ → SemSecTr tr
    SemSecTr⁻¹→SemSecTr tr _ tr-inv (red , pf) = red , helper
      where helper : ∀ E {c} A → (tr E ⇄₁ A) ⇓ (E ⇄₀ red {c} A)
            helper E {c} A A-breaks-E = ≗E→⇓₀ (tr-inv E) (red A) (pf (tr E) A A-breaks-E)

