module FunUniverse.Data where

open import Type
import Level as L
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)
open import Function
open import Data.Nat.NP using (ℕ; _+_; _*_; _^_)
open import Data.Bit using (Bit)
open import Data.Unit using (⊤)
open import Data.Product using (Σ; _×_; _,_) renaming (zip to ×-zip)
open import Data.Vec using (Vec)

-- An interface for small, finite & discrete universes of types.
record Universe {t} (T : Set t) : Set t where
  constructor mk
  field
    `⊤    : T
    `Bit  : T
    _`×_  : T → T → T
    _`^_  : T → ℕ → T

  `Vec : T → ℕ → T
  `Vec A n = A `^ n

  `Bits : ℕ → T
  `Bits n = `Bit `^ n

  infixr 2 _`×_
  infixl 2 _`^_

-- In ★-U, types are simply represented by Agda types (★ or Set).
★-U : Universe ★
★-U = mk ⊤ Bit _×_ Vec

-- In Bits-U, a type is represented by a natural number
-- representing the width of the type in a binary representation.
-- A natural embedding in ★ is the Bits type (aka Vec Bool).
Bits-U : Universe ℕ
Bits-U = mk 0 1 _+_ (flip _*_)

-- In Fin-U, a type is represented by a natural number
-- representing the cardinality of the type.
-- A natural embedding in ★ is the Fin type.
Fin-U : Universe ℕ
Fin-U = mk 1 2 _*_ _^_

-- In ⊤-U, there is only one possible type.
⊤-U : Universe ⊤
⊤-U = _ -- Agda figures out that there is only one such universe

⊤-U-uniq : {U₀ U₁ : Universe ⊤} → U₀ ≡ U₁
⊤-U-uniq = ≡.refl

-- Take the product of two universes. All types have two components, one from
-- each of the forming universes.
×-U : ∀ {s t} {S : Set s} {T : Set t} → Universe S → Universe T → Universe (S × T)
×-U S-U T-U = mk (S.`⊤ , T.`⊤) (S.`Bit , T.`Bit) (×-zip S._`×_ T._`×_)
                 (λ { (A₀ , A₁) n → S.`Vec A₀ n , T.`Vec A₁ n })
  where module S = Universe S-U
        module T = Universe T-U

-- Sym-U is a “symantic” (a mix of syntax and semantics) representation
-- for types. Symantic types are those defined only in term of the
-- Universe interface. [See the “Finally Tagless” approach by Oleg Kiselyov.]
Sym-U : ∀ t → Set (L.suc t)
Sym-U t = ∀ {T : Set t} → Universe T → T

-- Abstract syntax tree from types.
data Ty : ★ where
  ⊤′ Bit′ : Ty
  _×′_    : Ty → Ty → Ty
  _^′_    : Ty → ℕ → Ty

-- Ty-U is the universe of the syntactic represented types.
Ty-U : Universe Ty
Ty-U = mk ⊤′ Bit′ _×′_ _^′_

-- Turn a syntactic type into a symantic one.
-- Alternatively:
--   * a syntactic type is turned into a type of any $given universe.
--   * the catamorphism for syntactic types.
fold-U : ∀ {t} → Ty → Sym-U t
fold-U u₀ {T} uni = go u₀
  where open Universe uni
        go : Ty → T
        go ⊤′         = `⊤
        go Bit′       = `Bit
        go (t₀ ×′ t₁) = go t₀ `× go t₁
        go (t ^′ n)   = go t `^ n

{-
Σ-U : ∀ {t} {T : Set t} → Universe T → (P : T → ★) → Universe (Σ T P)
Σ-U T-U P = mk (`⊤ , {!!}) {!!} {!!} {!!}
  where open Universe T-U
-}

-- The type of universe unary operators or universe transformers.
UniOp : ∀ {s t} (S : Set s) (T : Set t) → Set _
UniOp S T = Universe S → Universe T

-- The type of universe binary operators.
UniOp₂ : ∀ {r s t} (R : Set r) (S : Set s) (T : Set t) → Set _
UniOp₂ R S T = Universe R → Universe S → Universe T
