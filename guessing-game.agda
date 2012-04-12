module guessing-game where

open import Function.NP
open import Data.Nat.NP
open import Data.Product
open import Data.Fin hiding (Ordering; compare; _+_)
open import Data.Bool -- hiding (_≟_)

record Beh (ChalMove AdvMove : Set) : Set where
  constructor mk
  field run : AdvMove → ChalMove × Beh ChalMove AdvMove

module OrderingTags where
  data OrderingTag : Set where
    LT EQ GT : OrderingTag

  tag : ∀ {m n} → Ordering m n → OrderingTag
  tag (less _ _)    = LT
  tag (equal _)     = EQ
  tag (greater _ _) = GT

  cmp : (m n : ℕ) → OrderingTag
  cmp m n = tag (compare m n)

open OrderingTags

data Trace : Set where
  say : (lastguess : ℕ) → Trace
  ask : (guess : ℕ) (ordering : OrderingTag) → Trace → Trace

data Win answer : Trace → Set where
  win  : Win answer (say answer)
  step : ∀ {guess trace} → Win answer trace → Win answer (ask guess (cmp guess answer) trace)

data ChalMove : Set where
  chalStop : ChalMove
  chalStep : OrderingTag → ChalMove

data AdvMove : Set where
  advStop : (guess : ℕ) → AdvMove
  advStep : (guess : ℕ) → AdvMove

advGuess : AdvMove → ℕ
advGuess (advStop guess) = guess
advGuess (advStep guess) = guess

Chal : Set
Chal = Beh ChalMove AdvMove

Adv : Set
Adv = Beh AdvMove ChalMove

chalBeh : (answer : ℕ) → Chal
chalBeh answer = chal where
  chal : Chal
  go : AdvMove → ChalMove × Chal
  go (advStop lastguess) = chalStop , chal
  go (advStep guess) = chalStep (cmp guess answer) , chal
  chal = mk go

middle : (lo hi : ℕ) → ℕ
middle lo hi = lo + ⌊ hi ∸ lo /2⌋

advStop' : ℕ → AdvMove × Adv
advStop' g = advStop g , mk (const (advStop' g))

adv : ∀ (lo g hi : ℕ) → ChalMove → AdvMove × Adv

advStep' : ∀ (lo g hi : ℕ) → AdvMove × Adv
advStep' lo g hi = advStep g , mk (adv lo g hi)

adv lo g hi chalStop = advStop' g
adv lo g hi (chalStep LT) = advStep' g (middle g hi) hi
adv lo g hi (chalStep EQ) = advStop' g
adv lo g hi (chalStep GT) = advStep' lo (middle lo g) g

play : ℕ → Chal → AdvMove × Adv → Trace
play (suc n) (mk chal) (advStep g , mk adv) with chal (advStep g)
... | chalStop , chalNext = say g
... | chalStep o , chalNext = ask g o (play n chalNext (adv (chalStep o)))
play _ _ (advMove , _) = say (advGuess advMove)

play100 : Fin 100 → Trace
play100 a = play 100 (chalBeh (toℕ a)) (advStep' 0 50 100)

ex : Trace
ex = play100 (# 5)

ex-wining : Win 5 ex
ex-wining = step (step (step (step (step (step (step win))))))

--  winner's-win : ∀ answer → Win (toℕ answer) (play100 answer)
-- winner's-win answer = {!!}
