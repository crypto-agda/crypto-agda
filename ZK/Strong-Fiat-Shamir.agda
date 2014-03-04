open import Type
open import Data.Maybe
open import Data.Two
open import Data.Product.NP
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Control.Strategy

module ZK.Strong-Fiat-Shamir
  {W S : ★}{L : W → S → ★}{Prf : S → ★}
  {RP RV RS : ★}{SimState : ★}{Q : ★}{Resp :    ★}
  (L? : ∀ w Y → Dec (L w Y))(L-to-Prf : ∀ {w Y} → L w Y → Prf Y)
  where

Random-Oracle : ★
Random-Oracle = Q → Resp

State : (S A : ★) → ★
State S A = S → A × S

record Proof-System : ★ where
  field
    Prove : RP →  (w : W)(Y : S) → Prf Y
    Verify : RV → (Y : S)(π : Prf Y) → 𝟚

record Simulator (PF : Proof-System) : ★ where
  open Proof-System PF
  field
    init : RS → SimState
    H : Q → State SimState Resp
    Simulate : (Y : S) → State SimState (Prf Y)
    verify-sim-spec : (rv : RV)(Y : S)(s : SimState) → let π = proj₁ (Simulate Y s)
                     in Verify rv Y π ≡ 1₂

module Is-Zero-Knowledge
  (PF : Proof-System)
  (sim : Simulator PF)
  where

  open Simulator sim

  data Adversary-Query : ★ where
    query-H : (q : Q) → Adversary-Query
    query-create-proof : (w : W)(Y : S) → Adversary-Query

  Challenger-Resp : Adversary-Query → ★
  Challenger-Resp (query-H s) = Resp
  Challenger-Resp (query-create-proof w Y) = Maybe (Prf Y)

  Adversary : ★
  Adversary = Strategy Adversary-Query Challenger-Resp 𝟚

  simulated-Challenger : ∀ q → State SimState (Challenger-Resp q)
  simulated-Challenger (query-H q) s = H q s
  simulated-Challenger (query-create-proof w Y) s with L? w Y
  simulated-Challenger (query-create-proof w Y) s | yes p = first just (Simulate Y s)
  simulated-Challenger (query-create-proof w Y) s | no ¬p = nothing , s

  open StatefulRun
  simulated : SimState → Adversary → 𝟚
  simulated s adv = evalS simulated-Challenger adv s

  module _ (ro : Random-Oracle) where

    real-Challenger : ∀ q → Challenger-Resp q
    real-Challenger (query-H q) = ro q
    real-Challenger (query-create-proof w Y) with L? w Y
    ... | yes p = just (L-to-Prf p)
    ... | no  _ = nothing

    real : Adversary → 𝟚
    real adv = run real-Challenger adv

    Experiment : 𝟚 → RS → Adversary → 𝟚
    Experiment 0₂ rs = real
    Experiment 1₂ rs = simulated (init rs)

{-
-- there exists a simulator, such that for all adversaries they are clueless if
-- they are in the real or simulated Experiment
Zero-Knowledge : Proof-System → ★
Zero-Knowledge PF = Σ (Simulator PF) (λ sim → {!!})
-}

module Sigma-Protocol
  (Commitment Challenge : ★)
  (Σ-Prf : S → ★)
  {RΣP : ★}
  (PF : Proof-System)
  where
  open Proof-System PF

  record Σ-Prover : ★ where
    field
      A : RΣP → (Y : S) → Commitment
      f : RΣP → (Y : S) → (c : Challenge) → Σ-Prf Y

  Σ-Verifier : ★
  Σ-Verifier = (Y : S)(A : Commitment)(c : Challenge)
             → Σ-Prf Y → 𝟚

  Correct : Σ-Verifier → Σ-Prover → ★
  Correct v p = ∀ {Y w} → L w Y → (r : RΣP)(c : _) →
    let open Σ-Prover p
    in v Y (A r Y) c (f r Y c) ≡ 1₂

  module Special-Honest-Verifier-Zero-Knowledge
    where

    record shvzk : ★ where


module Simulation-Sound-Extractability
  (PF : Proof-System)
  (sim : Simulator PF)
  where

