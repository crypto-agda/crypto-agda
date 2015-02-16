{-# OPTIONS --without-K #-}
open import Type                 using (Type; Type₁)
open import Data.Bool.Base       using (Bool) renaming (T to ✓)
open import Relation.Binary.Core using (_≡_; _≢_)
open import ZK.SigmaProtocol.Types
import ZK.SigmaProtocol as ΣP
import ZK.SigmaProtocol.KnownStatement as ΣPKS

module ZK.SigmaProtocol.Signature where

record Σ-Signature : Type₁ where
  field
    -- Prover's randomness type
    Randomness : Type
    -- Prover's commitments
    Commitment : Type
    -- Verifier challenges, picked at random
    Challenge  : Type
    -- Prover responses/proofs to challenges
    Response   : Type

record Σ-Signature'
         -- Set of possible statements of the zk-proof
         (Statement : Type)
         {-
         -- The of witnesses, namely the knowledge at stake
         {Witness : Statement → Type}
         -- Valid witness for the statement.
         -- The knowledge of such a valid witness is the
         -- secret known by the prover
         (_∋_ : (Y : Statement) → Witness Y → Type)-} : Type₁ where
  field
    -- Prover's randomness type
    Randomness : Statement → Type
    -- Prover's commitments
    Commitment : Statement → Type
    -- Verifier challenges, picked at random
    Challenge  : Statement → Type
    -- Prover responses/proofs to challenges
    Response   : Statement → Type
-- -}
-- -}
-- -}
-- -}
-- -}
