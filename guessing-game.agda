module guessing-game where

open import Type
open import Function.NP
open import Data.Nat.NP
open import Data.Product
open import Data.Fin hiding ({-Ordering; compare;-} _+_)
open import Data.Bool -- hiding (_≟_)

record Beh (MyMove OpMove : ★) : ★ where
  constructor _,_
  field
    myMove : MyMove
    opMove : OpMove → Beh MyMove OpMove

module OrderingTags where
  data OrderingTag : ★ where
    LT EQ GT : OrderingTag

  tag : ∀ {m n} → Ordering m n → OrderingTag
  tag (less _ _)    = LT
  tag (equal _)     = EQ
  tag (greater _ _) = GT

  cmp : (m n : ℕ) → OrderingTag
  cmp m n = tag (compare m n)

open OrderingTags

data Trace : ★ where
  say : (lastguess : ℕ) → Trace
  ask : (guess : ℕ) (ordering : OrderingTag) → Trace → Trace

data Win answer : Trace → ★ where
  win  : Win answer (say answer)
  step : ∀ {guess trace} → Win answer trace → Win answer (ask guess (cmp guess answer) trace)

data ChalMove : ★ where
  chalStop : ChalMove
  chalStep : OrderingTag → ChalMove

data AdvMove : ★ where
  advStop : (guess : ℕ) → AdvMove
  advStep : (guess : ℕ) → AdvMove

advGuess : AdvMove → ℕ
advGuess (advStop guess) = guess
advGuess (advStep guess) = guess

Chal : ★
Chal = Beh ChalMove AdvMove

Adv : ★
Adv = Beh AdvMove ChalMove

chalBeh : (answer : ℕ) → AdvMove → Chal
chalBeh answer (advStop lastguess) = chalStop , chalBeh answer
chalBeh answer (advStep guess) = chalStep (cmp guess answer) , chalBeh answer

middle : (lo hi : ℕ) → ℕ
middle lo hi = lo + ⌊ hi ∸ lo /2⌋

advStop' : ℕ → Adv
advStop' g = advStop g , const (advStop' g)

adv : ∀ (lo g hi : ℕ) → ChalMove → Adv

advStep' : ∀ (lo g hi : ℕ) → Adv
advStep' lo g hi = advStep g , adv lo g hi

adv lo g hi chalStop = advStop' g
adv lo g hi (chalStep LT) = advStep' g (middle g hi) hi
adv lo g hi (chalStep EQ) = advStop' g
adv lo g hi (chalStep GT) = advStep' lo (middle lo g) g

play : ℕ → (AdvMove → Chal) → Adv → Trace
play (suc n) chal (advStep g , adv) with chal (advStep g)
... | chalStop , chalNext = say g
... | chalStep o , chalNext = ask g o (play n chalNext (adv (chalStep o)))
play _ _ (advMove , _) = say (advGuess advMove)

play100 : Fin 100 → Trace
play100 a = play 100 (chalBeh (toℕ a)) (advStep' 0 50 100)

ex : Trace
ex = play100 (# 5)

ex-wining : Win 5 ex
ex-wining = step (step (step (step (step (step (step win))))))

-- winner's-win : ∀ answer → Win (toℕ answer) (play100 answer)
-- winner's-win answer = {!!}
