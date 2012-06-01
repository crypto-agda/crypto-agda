open import program-distance
open import flipbased-implem
open import Data.Bits
open import Data.Product
open import Relation.Nullary

module bit-guessing-game (prgDist : PrgDist) where
  open PrgDist prgDist

  GuessAdv : Coins → Set
  GuessAdv c = ↺ c Bit

  runGuess⅁ : ∀ {ca} (A : GuessAdv ca) (b : Bit) → ↺ ca Bit
  runGuess⅁ A _ = A

  -- An oracle: an adversary who can break the guessing game.
  Oracle : Coins → Set
  Oracle ca = ∃ (λ (A : GuessAdv ca) → breaks (runGuess⅁ A))

  -- Any adversary cannot do better than a random guess.
  GuessSec : Coins → Set
  GuessSec ca = ∀ (A : GuessAdv ca) → ¬(breaks (runGuess⅁ A))
