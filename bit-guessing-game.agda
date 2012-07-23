open import Data.Nat.NP
open import Data.Nat.Properties
open import Data.Product using (∃)
open import Relation.Nullary using (¬_)
open import Function
open import Data.Bool.NP

open import Data.Bits

open import flipbased-implem using (Coins; ↺; ⅁) -- ; #⟨_⟩) renaming (count↺ to #⟨_⟩)
open import program-distance using (PrgDist; module PrgDist)
open import Relation.Binary.PropositionalEquality

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

#ᵇ : Bool → ℕ
#ᵇ b = if b then 1 else 0

#ᵇ≤1 : ∀ b → #ᵇ b ≤ 1
#ᵇ≤1 true = s≤s z≤n
#ᵇ≤1 false = z≤n

#-bound : ∀ c (f : Bits c → Bit) → #⟨ f ⟩ ≤ 2^ c
#-bound zero    f = #ᵇ≤1 (f [])
#-bound (suc c) f = #-bound c (f ∘ 0∷_) +-mono #-bound c (f ∘ 1∷_)

#-∘vnot : ∀ c (f : Bits c → Bit) → #⟨ f ⟩ ≡ #⟨ f ∘ vnot ⟩
#-∘vnot zero f = refl
#-∘vnot (suc c) f
  rewrite #-∘vnot c (f ∘ 0∷_)
        | #-∘vnot c (f ∘ 1∷_) = ℕ°.+-comm #⟨ f ∘ 0∷_ ∘ vnot ⟩ _

#-not∘ : ∀ c (f : Bits c → Bit) → #⟨ f ⟩ ≡ 2^ c ∸ #⟨ not ∘ f ⟩
#-not∘ zero f with f []
... | true = refl
... | false = refl
#-not∘ (suc c) f
  rewrite #-not∘ c (f ∘ 0∷_)
        | #-not∘ c (f ∘ 1∷_) = helper c #⟨ not ∘ f ∘ 0∷_ ⟩ _ (#-bound c (not ∘ f ∘ 0∷_)) (#-bound c (not ∘ f ∘ 1∷_))
  where helper : ∀ c x y → x ≤ 2^ c → y ≤ 2^ c → (2^ c ∸ x) + (2^ c ∸ y) ≡ 2^(1 + c) ∸ (x + y)
        helper zero x y x≤ y≤ = {!!}
        helper (suc c₁) x y x≤ y≤ = {!helper c₁ x y ? ?!}
