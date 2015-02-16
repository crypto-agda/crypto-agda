{-# OPTIONS --without-K #-}
open import Type using (Type; Type₁)
open import ZK.SigmaProtocol.Signature
import ZK.SigmaProtocol.KnownStatement as ΣPKS
import ZK.SigmaProtocol as ΣP

module ZK.SigmaProtocol.Structure where

{- Witness: The of witnesses, namely the knowledge at stake
   ValidWitness:
     Valid witness for the statement.
     The knowledge of such a valid witness is the
     secret known by the prover
-}
record Σ-Structure {Witness : Type} (ValidWitness : Witness → Type) : Type₁ where
  field Σ-sig : Σ-Signature
  open  Σ-Signature Σ-sig public
  open  ΣPKS Commitment Challenge Response Randomness Witness ValidWitness public
  field special-Σ-protocol : Special-Σ-Protocol
  open  Special-Σ-Protocol special-Σ-protocol public

record Σ-Structure' {Statement : Type}
                    {Witness : Statement → Type}
                    (_∋_ : (Y : Statement) → Witness Y → Type)
                  : Type₁ where
  field Σ-sig : Σ-Signature' Statement
  open  Σ-Signature' Σ-sig public
  open  ΣP Statement Commitment Challenge Response Randomness Witness _∋_ public
  field special-Σ-protocol : Special-Σ-Protocol
  open  Special-Σ-Protocol special-Σ-protocol public
-- -}
-- -}
-- -}
-- -}
