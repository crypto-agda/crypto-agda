open import Data.Nat.NP
open import Data.Nat.Properties
open import Data.Product using (∃)
open import Relation.Nullary using (¬_)
open import Function
open import Data.Bool.NP

open import Data.Bits hiding (#⟨_⟩)

open import flipbased-implem using (Coins; ↺; ⅁; return↺; toss; Rat; _/_; Pr[_≡1]) renaming (count↺ to #⟨_⟩)
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

-- The guessing game is secure iff all adversaries have
-- only a neglible advantage over the game.
-- Meaning that no adversary can be behave differently when
-- the game is to guess 0 than when the game is to guess 1.
GuessSec : Coins → Set
GuessSec ca = ∀ (A : GuessAdv ca) → ¬(breaks (runGuess⅁ A))

-- The adversary actually has to behave the same way in both
-- situation give the definition of the runGuess⅁.
-- Agda reduces to two sides of the equation to same thing.
same-behavior : ∀ {ca} (A : GuessAdv ca) → runGuess⅁ A 0b ≡ runGuess⅁ A 1b
same-behavior A = ≡.refl

-- The guessing game is actually secure since any adversary
-- has an advantage of zero.
-- This a direct application of the fact that the "far-apart" _]-[_
-- relation is antisymetric, meaning that any point cannot be "far-apart"
-- from itself. The definiton of "breaks ⅁" being that ⅁ 0b is "far-apart"
-- from ⅁ 1b.
guessSec : ∀ {ca} → GuessSec ca
guessSec = ]-[-antisym

-- Let's look at three possible strategies:

-- Always returning 1 will allow to win all the time when
-- one has to guess 1 but lose all the time when one has to
-- guess 0.
count↺-return↺-1b : Pr[ return↺ {0} 1b ≡1] ≡ 1 / 1
count↺-return↺-1b = ≡.refl

-- Similarily returning always 0 is not better.
count↺-return↺-0b : Pr[ return↺ {0} 0b ≡1] ≡ 0 / 1
count↺-return↺-0b = ≡.refl

-- Tossing a coin will allow to win half the time in
-- both situtations, but still once we look at the distance
-- between the two situtations these two halfs cancel each
-- other.
count↺-toss : Pr[ toss ≡1] ≡ 1 / 2
count↺-toss = ≡.refl

-- In the end, at the pure guessing game it is as hard to be
-- consitently good than to be consitently bad.
