{-# OPTIONS --without-K #-}
module README where

-- A module for bit-vectors which is used almost
-- everywhere in this development.
open import Data.Bits

open import elgamal
open import schnorr
open import generic-zero-knowledge-interactive
open import sum-properties

-- Randomized programs
open import flipbased
open import flipbased-counting
open import flipbased-running
open import flipbased-implem
open import flipbased-tree

-- A distance between randomized programs
open import program-distance

-- Pure guessing game, a game in which no strategy can
-- consistently win or consistently lose.
open import bit-guessing-game

-- Cryptographic pseudo-random generator game.
open import prg

-- “One time Semantic Security” of the “One time pad” cipher
-- on one bit messages. In other words, “xor”ing any bit with
-- a random bit will look random as well.
open import single-bit-one-time-pad

-- Ciphers, the “one time Semantic Security” game.
open import one-time-semantic-security

-- A simple reduction on ciphers.
open import composition-sem-sec-reduction

-- TODO: Fix & restore the product of universes and ops

-- Draft modules of previous attempts.
-- There is still some code to rescue.
open import circuit
open import flipbased-tree-probas
open import flipbased-no-split
open import flipbased-product-implem
