{-# OPTIONS --without-K #-}
module FunUniverse.Data where

open import Type
import Level as L
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)
open import Function
open import Data.Nat.NP using (ℕ; _+_; _*_; _*′_; _^_)
open import Data.One using (𝟙)
open import Data.Two using (𝟚)
open import Data.Product using (Σ; _×_; _,_) renaming (zip to ×-zip)
open import Data.Vec using (Vec)

-- An interface for small, finite & discrete universes of types.
record Universe {t} (T : Set t) : Set t where
  constructor mk
  field
    `𝟙    : T
    `𝟚    : T
    _`×_  : T → T → T
    _`^_  : T → ℕ → T

  `Vec : T → ℕ → T
  `Vec A n = A `^ n

  `Bit : T
  `Bit = `𝟚

  `Bits : ℕ → T
  `Bits n = `Bit `^ n

  infixr 2 _`×_
  infixl 2 _`^_

-- In ★-U, types are simply represented by Agda types (★ or Set).
★-U : Universe ★
★-U = mk 𝟙 𝟚 _×_ Vec

-- In Bits-U, a type is represented by a natural number
-- representing the width of the type in a binary representation.
-- A natural embedding in ★ is the Bits type (aka Vec Bool).
Bits-U : Universe ℕ
Bits-U = mk 0 1 _+_ _*′_

-- In Fin-U, a type is represented by a natural number
-- representing the cardinality of the type.
-- A natural embedding in ★ is the Fin type.
Fin-U : Universe ℕ
Fin-U = mk 1 2 _*_ _^_

-- In 𝟙-U, there is only one possible type.
𝟙-U : Universe 𝟙
𝟙-U = _ -- Agda figures out that there is only one such universe

𝟙-U-uniq : {U₀ U₁ : Universe 𝟙} → U₀ ≡ U₁
𝟙-U-uniq = ≡.refl

-- Take the product of two universes. All types have two components, one from
-- each of the forming universes.
×-U : ∀ {s t} {S : Set s} {T : Set t} → Universe S → Universe T → Universe (S × T)
×-U S-U T-U = mk (S.`𝟙 , T.`𝟙) (S.`𝟚 , T.`𝟚) (×-zip S._`×_ T._`×_)
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
  𝟙′ 𝟚′ : Ty
  _×′_  : Ty → Ty → Ty
  _^′_  : Ty → ℕ → Ty

-- Ty-U is the universe of the syntactic represented types.
Ty-U : Universe Ty
Ty-U = mk 𝟙′ 𝟚′ _×′_ _^′_

-- Turn a syntactic type into a symantic one.
-- Alternatively:
--   * a syntactic type is turned into a type of any $given universe.
--   * the catamorphism for syntactic types.
fold-U : ∀ {t} → Ty → Sym-U t
fold-U u₀ {T} uni = go u₀
  where open Universe uni
        go : Ty → T
        go 𝟙′         = `𝟙
        go 𝟚′         = `𝟚
        go (t₀ ×′ t₁) = go t₀ `× go t₁
        go (t ^′ n)   = go t `^ n

{-
Σ-U : ∀ {t} {T : Set t} → Universe T → (P : T → ★) → Universe (Σ T P)
Σ-U T-U P = mk (`𝟙 , {!!}) {!!} {!!} {!!}
  where open Universe T-U
-}

-- The type of universe unary operators or universe transformers.
UniOp : ∀ {s t} (S : Set s) (T : Set t) → Set _
UniOp S T = Universe S → Universe T

-- The type of universe binary operators.
UniOp₂ : ∀ {r s t} (R : Set r) (S : Set s) (T : Set t) → Set _
UniOp₂ R S T = Universe R → Universe S → Universe T
