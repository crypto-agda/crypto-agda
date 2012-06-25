open import Data.Product using (∃)
open import Relation.Nullary using (¬_)

open import Data.Bits using (Bit)

open import flipbased-implem using (Coins; ↺)
open import program-distance using (PrgDist; module PrgDist)

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
