open import Data.Nat.NP
open import Data.Nat.Properties
open import Data.Product using (∃)
open import Relation.Nullary using (¬_)
open import Function
open import Data.Bool.NP

open import Data.Bits

open import flipbased-implem using (Coins; ↺; ⅁) -- ; #⟨_⟩) renaming (count↺ to #⟨_⟩)
open import program-distance using (PrgDist; module PrgDist)
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)

module bit-guessing-game (prgDist : PrgDist) where

open PrgDist prgDist

GuessAdv : Coins → Set
GuessAdv = ⅁

runGuess⅁ : ∀ {ca} (A : GuessAdv ca) (b : Bit) → ⅁ ca
runGuess⅁ A _ = A

-- An oracle: an adversary who can break the guessing game.
Oracle : Coins → Set
Oracle ca = ∃ (λ (A : GuessAdv ca) → breaks (runGuess⅁ A))

-- Any adversary cannot do better than a random guess.
GuessSec : Coins → Set
GuessSec ca = ∀ (A : GuessAdv ca) → ¬(breaks (runGuess⅁ A))
