{-# OPTIONS --without-K #-}
-- This module is an example of the use of the circuit building library.
-- The point is to start with a tiny bytecode evaluator for bit operations.
module bytecode where

open import Function
open import Data.Nat
open import Data.Vec
open import Data.Product.NP
open import Data.Bits
open import Data.Bool
open import Algebra.FunctionProperties

data I : ℕ → ★ where
  `[]  : I 1
  `op₀ : ∀ {i} (b : Bit) (is : I (1 + i)) → I i
  `op₁ : ∀ {i} (op₁ : Op₁ Bit) (is : I (1 + i)) → I (1 + i)
  `op₂ : ∀ {i} (op₂ : Op₂ Bit) (is : I (1 + i)) → I (2 + i)

eval : ∀ {i} → I i → Bits i → Bit
eval `[] (x ∷ []) = x
eval (`op₀ b is) st = eval is (b ∷ st)
eval (`op₁ op₁ is) (b ∷ st) = eval is (op₁ b ∷ st)
eval (`op₂ op₂ is) (b₀ ∷ b₁ ∷ st) = eval is (op₂ b₀ b₁ ∷ st)

eval₀ : I 0 → Bit
eval₀ i₀ = eval i₀ []

open import circuit

module Ck {C} (cb : CircuitBuilder C) where
  open CircuitBuilder cb

  data IC : ℕ → ★ where
    `[] : IC 1
    `op : ∀ {i ki ko} (op : C ki ko) (is : IC (ko + i)) → IC (ki + i)

  module Eval (runC : RunCircuit C) where
    module CF = CircuitBuilder bitsFunCircuitBuilder
    ckIC : ∀ {i} → IC i → C i 1
    ckIC `[]         = idC
    ckIC (`op op is) = op *** idC >>> ckIC is

    evalIC : ∀ {i} → IC i → Bits i → Bit
    evalIC is bs = head (runC (ckIC is) bs)

  ck : ∀ {i} → I i → C i 1
  ck `[]           = idC
  ck (`op₀ b   is) = bit b *** idC >>> ck is
  ck (`op₁ op₁ is) = unOp op₁ *** idC >>> ck is
  ck (`op₂ op₂ is) = binOp op₂ *** idC >>> ck is

  I2IC : ∀ {i} → I i → IC i
  I2IC `[] = `[]
  I2IC (`op₀ b is) = `op (bit b) (I2IC is)
  I2IC (`op₁ op₁ is) = `op (unOp op₁) (I2IC is)
  I2IC (`op₂ op₂ is) = `op (binOp op₂) (I2IC is)

  ck₀ : I 0 → C 0 1
  ck₀ = ck

module CheckCk where
  open Ck bitsFunCircuitBuilder
  open CircuitBuilder bitsFunCircuitBuilder
  open import Relation.Binary.PropositionalEquality

  ck-eval : ∀ {i} (is : I i) bs → ck is bs ≡ eval is bs ∷ []
  ck-eval `[] (x ∷ []) = refl
  ck-eval (`op₀ b is) bs = ck-eval is (b ∷ bs)
  ck-eval (`op₁ op₁ is) (b ∷ bs) = ck-eval is (op₁ b ∷ bs)
  ck-eval (`op₂ op₂ is) (b₀ ∷ b₁ ∷ bs) = ck-eval is (op₂ b₀ b₁ ∷ bs)
