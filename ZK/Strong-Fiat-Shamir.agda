open import Type
open import Data.Maybe
open import Data.Two
open import Data.List.NP
open import Data.Product.NP
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Control.Strategy

module ZK.Strong-Fiat-Shamir
  {W Λ : ★}{L : W → Λ → ★}{Prf : Λ → ★}
  {RP RV RS : ★}{Q : ★}{Resp :    ★}
  (L? : ∀ w Y → Dec (L w Y))
  (L-to-Prf : ∀ {w Y} → L w Y → Prf Y)
  (Q? : Decidable (_≡_ {A = Q}))
  where

Random-Oracle : ★
Random-Oracle = Q → Resp

State : (S A : ★) → ★
State S A = S → A × S

data Adversary-Query : ★ where
  query-H : (q : Q) → Adversary-Query
  query-create-proof : (w : W)(Y : Λ) → Adversary-Query

Challenger-Resp : Adversary-Query → ★
Challenger-Resp (query-H s) = Resp
Challenger-Resp (query-create-proof w Y) = Maybe (Prf Y)

Transcript = List (Σ Adversary-Query Challenger-Resp)

record Proof-System : ★ where
  field
    Prove  : RP → (w : W)(Y : Λ) → Prf Y
    Verify : RV → (Y : Λ)(π : Prf Y) → 𝟚

module H-def (ro : Random-Oracle)(t : Transcript)(q : Q) where
  H : Resp
  H with find (λ { (query-H q' , r) → ⌊ Q? q' q ⌋
                 ; (query-create-proof _ _ , _) → 0₂ }) t
  ... | just (query-H q₁ , r) = r
  ... | _ = ro q

record Simulator (PF : Proof-System) : ★ where
  open Proof-System PF

  field
    Simulate : RS → Transcript → (Y : Λ) → Prf Y
    verify-sim-spec : (rs : RS)(rv : RV)(t : Transcript)(Y : Λ) →
                      let π = Simulate rs t Y
                      in Verify rv Y π ≡ 1₂

module Is-Zero-Knowledge
  (PF : Proof-System)
  (sim : Simulator PF)
  where

  open Simulator sim

  Adversary : ★
  Adversary = Strategy Adversary-Query Challenger-Resp 𝟚

  module _ (ro : Random-Oracle) where

    open H-def ro

    simulated-Challenger : RS → Transcript → ∀ q → Challenger-Resp q
    simulated-Challenger rs t (query-H q) = H t q
    simulated-Challenger rs t (query-create-proof w Y) with L? w Y
    simulated-Challenger rs t (query-create-proof w Y) | yes p = just (Simulate rs t Y)
    simulated-Challenger rs t (query-create-proof w Y) | no ¬p = nothing

    real-Challenger : ∀ q → Challenger-Resp q
    real-Challenger (query-H q) = ro q
    real-Challenger (query-create-proof w Y) with L? w Y
    ... | yes p = just (L-to-Prf p)
    ... | no  _ = nothing

    challenger : 𝟚 → RS → Transcript → ∀ q → Challenger-Resp q
    challenger 0₂ _  _ = real-Challenger
    challenger 1₂ rs t = simulated-Challenger rs t

    open TranscriptRun
    Experiment : 𝟚 → RS → Adversary → 𝟚 × Transcript
    Experiment β rs adv = runT (challenger β rs) adv []

{-
-- there exists a simulator, such that for all adversaries they are clueless if
-- they are in the real or simulated Experiment
Zero-Knowledge : Proof-System → ★
Zero-Knowledge PF = Σ (Simulator PF) (λ sim → {!!})
-}

module Sigma-Protocol
  (Commitment Challenge : ★)
  (Σ-Prf : Λ → ★)
  {RΣP : ★}
  (PF : Proof-System)
  where
  open Proof-System PF

  record Σ-Prover : ★ where
    field
      get-A : RΣP → (Y : Λ) → Commitment
      get-f : RΣP → (Y : Λ) → (c : Challenge) → Σ-Prf Y

  record Σ-Transcript (Y : Λ) : ★ where
    constructor mk
    field
      get-A : Commitment
      get-c : Challenge
      get-f : Σ-Prf Y

  Σ-Verifier : ★
  Σ-Verifier = (Y : Λ)(t : Σ-Transcript Y) → 𝟚

  record Σ-Protocol : ★ where
    constructor _,_
    field
      Σ-verifier : Σ-Verifier
      Σ-prover   : Σ-Prover
    open Σ-Prover Σ-prover public

    Σ-game : (r : RΣP)(Y : Λ)(c : Challenge) → 𝟚
    Σ-game r Y c = Σ-verifier Y (mk A c f)
      where
        A = get-A r Y
        f = get-f r Y c

  _⇄_ : Σ-Verifier → Σ-Prover → RΣP → Λ → Challenge → 𝟚
  (v ⇄ p) r Y c = Σ-Protocol.Σ-game (v , p) r Y c

  Correct : Σ-Protocol → ★
  Correct (v , p) = ∀ {Y w} → L w Y → (r : RΣP)(c : _) →
    let open Σ-Prover p
    in v Y (mk (get-A r Y) c (get-f r Y c)) ≡ 1₂

  module Special-Honest-Verifier-Zero-Knowledge where

    record SHVZK (Σ-proto : Σ-Protocol) : ★ where
      open Σ-Protocol Σ-proto
      field
        Simulate : (Y : Λ)(c : Challenge)(f : Σ-Prf Y) → Commitment
        Simulate-ok : ∀ Y c f → Σ-verifier Y (mk (Simulate Y c f) c f) ≡ 1₂
        -- If (c,f) uniformly distributed then (Simulate Y c f , c , f) is
        -- distributed equaly to ((Σ-verifier ⇄ Σ-prover) r Y c)

  module Special-Soundness where

    record SpSo : ★ where
      field
        Extract : (Y : Λ)(t₀ t₁ : Σ-Transcript Y) → W
        Extract-ok : ∀ Y A c₀ c₁ f₀ f₁ → (c₀ ≢ c₁) → L (Extract Y (mk A c₀ f₀) (mk A c₁ f₁)) Y

  module Simulation-Sound-Extractability
    (sim : Simulator PF)
    (open Is-Zero-Knowledge PF sim)
    {RA : ★}
    (Adv : Adversary)
    (ro : Random-Oracle)
    where

    module Initial-run where
        K-winning-Transcript : Transcript → 𝟚
        K-winning-Transcript []            = 1₂
        K-winning-Transcript ((query-H q , r) ∷ t) = K-winning-Transcript t -- nothing else to check right?
        K-winning-Transcript ((query-create-proof w Y , nothing) ∷ t) = ?
        K-winning-Transcript ((query-create-proof w Y , just π)  ∷ t) = ?
        {-with L? w Y
        ... | yes p = {!!}
        ... | no ¬p = {!!}-}

        game : (w : RA)(β : 𝟚)(rs : RS) → {!!}
        game w β rs = let (β' , t) = Experiment ro β rs Adv in {!!}

-- -}
-- -}
-- -}
-- -}
-- -}
