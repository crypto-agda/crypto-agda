open import Type
open import Data.Bits    using (Bit; Bits)
open import Data.Empty   using (⊥)
open import Data.Fin     using (Fin)
open import Data.Maybe   using (Maybe)
open import Data.Nat     using (ℕ)
open import Data.Product using (Σ; _×_)
open import Data.Sum     using (_⊎_)
open import Data.Unit    using (⊤)
open import Data.Vec     using (Vec)

module Search.Syntax where

-- this is to be imported from the appropriate module
postulate
  S : ★₀ → ★₀
  S⊤ : S ⊤
  SBit : S Bit
  SFin : ∀ n → S (Fin n)
  SBits : ∀ n → S (Bits n)
  SVec : ∀ {A} → S A → ∀ n → S (Vec A n)
  _S×_ : ∀ {A B} → S A → S B → S (A × B)
  _S⊎_ : ∀ {A B} → S A → S B → S (A ⊎ B)
  SMaybe : ∀ {A} → S A → S (Maybe A)
  SΣ : ∀ {A} {B : A → _} → S A → (∀ x → S (B x)) → S (Σ A B)
  S⊤→ : ∀ {A} → S A → S (⊤ → A)
  SBit→ : ∀ {A} → S A → S (Bit → A)
  S⊥→ : ∀ A → S (⊥ → A)
  S×→ : ∀ {A B C} → S (A → B → C) → S (A × B → C)
  S⟨_⊎_⟩→ : ∀ {A B C} → S (A → C) → S (B → C) → S (A ⊎ B → C)

module Fin-universe where

    `★ : ★₀
    `★ = ℕ

    -- decoding
    El : `★ → ★₀
    El = Fin

    `S : ∀ `A → S (El `A)
    `S = SFin

module Bits-universe where

    `★ : ★₀
    `★ = ℕ

    -- decoding
    El : `★ → ★₀
    El = Bits

    `S : ∀ `A → S (El `A)
    `S = SBits

module ⊎×-universe where

    data `★ : ★₀ where
      `⊤ : `★
      _`×_ _`⊎_ : `★ → `★ → `★

    -- decoding
    El : `★ → ★₀
    El `⊤ = ⊤
    El (s `× t) = El s × El t
    El (s `⊎ t) = El s ⊎ El t

    `S : ∀ `A → S (El `A)
    `S `⊤       = S⊤
    `S (s `× t) = `S s S× `S t
    `S (s `⊎ t) = `S s S⊎ `S t

module ⊤-Maybe-universe where

    data `★ : ★₀ where
      -- one element
      `⊤     : `★
      -- one element more
      `Maybe : `★ → `★

    -- decoding
    El : `★ → ★₀
    El `⊤ = ⊤
    El (`Maybe t) = Maybe (El t)

    `S : ∀ `A → S (El `A)
    `S `⊤ = S⊤
    `S (`Maybe t) = SMaybe (`S t)

module ΣBit-universe where

    data `★ : ★₀
    El : `★ → ★₀

    data `★ where
      `Bit : `★
      `Σ   : (s : `★) → (El s → `★) → `★

    -- decoding
    El `Bit     = Bit
    El (`Σ s t) = Σ (El s) λ x → El (t x)

    `S : ∀ `A → S (El `A)
    `S `Bit = SBit
    `S (`Σ s t) = SΣ (`S s) λ x → `S (t x)

module ⊎×→-universe where

    -- Types appearing on the left of an arrow
    data `★⁻ : ★₀ where
      -- zero and elements
      `⊥ `⊤ : `★⁻

      -- products and co-products
      _`×_ _`⊎_ : `★⁻ → `★⁻ → `★⁻

    -- decoding of negative types
    El⁻ : `★⁻ → ★₀
    El⁻ `⊥ = ⊥
    El⁻ `⊤ = ⊤
    El⁻ (s `× t) = El⁻ s × El⁻ t
    El⁻ (s `⊎ t) = El⁻ s ⊎ El⁻ t

    `S⟨_⟩→_ : ∀ `A {B} (sB : S B) → S (El⁻ `A → B)
    `S⟨ `⊥ ⟩→ t = S⊥→ _
    `S⟨ `⊤ ⟩→ t = S⊤→ t
    `S⟨ s `× t ⟩→ u = S×→ (`S⟨ s ⟩→ `S⟨ t ⟩→ u)
    `S⟨ s `⊎ t ⟩→ u = S⟨ `S⟨ s ⟩→ u ⊎ `S⟨ t ⟩→ u ⟩→

    data `★ : ★₀ where
      -- one element
      `⊤     : `★

      -- products and co-products
      _`×_ _`⊎_ : `★ → `★ → `★

      -- functions
      _`→_ : `★⁻ → `★ → `★

    -- decoding of positive types
    El : `★ → ★₀
    El `⊤ = ⊤
    El (s `× t) = El s × El t
    El (s `⊎ t) = El s ⊎ El t
    El (s `→ t) = El⁻ s → El t

    `S : ∀ `A → S (El `A)
    `S `⊤ = S⊤
    `S (s `× t) = `S s S× `S t
    `S (s `⊎ t) = `S s S⊎ `S t
    `S (s `→ t) = `S⟨ s ⟩→ `S t

module Σ⊎×→-universe where

    -- Types appearing on the left of an arrow
    data `★⁻ : ★₀ where
      -- zero, one, and two elements
      `⊥ `⊤ `Bit : `★⁻

      -- products and co-products
      _`×_ _`⊎_ : `★⁻ → `★⁻ → `★⁻

      -- Σ?

    -- decoding of negative types
    El⁻ : `★⁻ → ★₀
    El⁻ `⊥ = ⊥
    El⁻ `⊤ = ⊤
    El⁻ `Bit = Bit
    El⁻ (s `× t) = El⁻ s × El⁻ t
    El⁻ (s `⊎ t) = El⁻ s ⊎ El⁻ t

    `S⟨_⟩→_ : ∀ `A {B} (sB : S B) → S (El⁻ `A → B)
    `S⟨ `⊥ ⟩→ t = S⊥→ _
    `S⟨ `⊤ ⟩→ t = S⊤→ t
    `S⟨ `Bit ⟩→ t = SBit→ t
    `S⟨ s `× t ⟩→ u = S×→ (`S⟨ s ⟩→ `S⟨ t ⟩→ u)
    `S⟨ s `⊎ t ⟩→ u = S⟨ `S⟨ s ⟩→ u ⊎ `S⟨ t ⟩→ u ⟩→

    data `★ : ★₀
    El : `★ → ★₀

    data `★ where
      -- one and two elements
      `⊤ `Bit : `★

      -- 'n' elements
      `Fin : ℕ → `★

      -- one element more
      `Maybe : `★ → `★

      -- products and co-products
      _`×_ _`⊎_ : `★ → `★ → `★

      -- dependent pairs
      `Σ   : (s : `★) → (El s → `★) → `★

      -- vectors
      `Vec : `★ → ℕ → `★

      -- functions
      _`→_ : `★⁻ → `★ → `★

    -- decoding of positive types
    El `⊤ = ⊤
    El `Bit = Bit
    El (`Fin n) = Fin n
    El (`Maybe t) = Maybe (El t)
    El (s `× t) = El s × El t
    El (s `⊎ t) = El s ⊎ El t
    El (`Σ s t) = Σ (El s) λ x → El (t x)
    El (s `→ t) = El⁻ s → El t
    El (`Vec t n) = Vec (El t) n

    `Bits = `Vec `Bit

    `S : ∀ `A → S (El `A)
    `S `⊤ = S⊤
    `S `Bit = SBit
    `S (`Fin n) = SFin n
    `S (`Maybe `A) = SMaybe (`S `A)
    `S (`A `× `B) = `S `A S× `S `B
    `S (`A `⊎ `B) = `S `A S⊎ `S `B
    `S (`Σ `A `B) = SΣ (`S `A) λ x → `S (`B x)
    `S (`Vec `A n) = SVec (`S `A) n
    `S (`A `→ `B) = `S⟨ `A ⟩→ `S `B
