open import Type
open import Function.NP
open import Data.Maybe
open import Data.One
open import Data.Two
open import Data.List.NP renaming (map to mapᴸ)
open import Data.Product.NP renaming (proj₁ to fst; proj₂ to snd)
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Control.Strategy

module ZK.Strong-Fiat-Shamir
  {W Λ : ★}{L : W → Λ → ★}{Prf : Λ → ★}
  {RS : ★}{Q : ★}{Resp :    ★}
  (L? : ∀ w Y → Dec (L w Y))
  (L-to-Prf : ∀ {w Y} → L w Y → Prf Y)
  (Prf? : ∀ {Y Y'} → Prf Y → Prf Y' → 𝟚)
  -- (Prf? : ∀ Y → Decidable (_≡_ {A = Prf Y}))
  -- (Q? : Decidable (_≡_ {A = Q}))
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

Adversary : ★ → ★
Adversary A = Strategy Adversary-Query Challenger-Resp A

Transcript = List (Σ Adversary-Query Challenger-Resp)

Prfs : ★
Prfs = List (Σ Λ Prf)

Random-Oracle-List : ★
Random-Oracle-List = List (Q × Resp)

record Proof-System (RP : ★)(Prf : Λ → ★) : ★ where
  field
    Prove  : RP → (w : W)(Y : Λ) → Prf Y
    Verify : (Y : Λ)(π : Prf Y) → 𝟚

Complete-Proof-System : {RP : ★}{Prf : Λ → ★} → Proof-System RP Prf → ★
Complete-Proof-System PS = ∀ rp w Y → Verify Y (Prove rp w Y) ≡ 1₂
  where open Proof-System PS

    {-
module H-def (ro : Random-Oracle)(t : Random-Oracle-List)(q : Q) where
  H : Resp
  H with find (λ { (query-H q' , r) → ⌊ Q? q' q ⌋
                 ; (query-create-proof _ _ , _) → 0₂ }) t
  ... | just (query-H q₁ , r) = r
  ... | _ = ro q
  -}

record Simulator {RP}(PF : Proof-System RP Prf) : ★ where
  open Proof-System PF

  field
    -- Computing the compound patch to the random oracle
    H-patch  : RS → Transcript → Random-Oracle → Random-Oracle

    -- Simulate does not patch itself but H-patch does
    Simulate : RS → Transcript → (Y : Λ) → Prf Y
    verify-sim-spec : ∀ rs t Y →
                      let π = Simulate rs t Y
                      in Verify Y π ≡ 1₂

module Is-Zero-Knowledge
  {RP}
  (PF : Proof-System RP Prf)
  (sim : Simulator PF)
  where

  open Simulator sim

  module _ (ro : Random-Oracle) where

    simulated-Challenger : RS → Transcript → ∀ q → Challenger-Resp q
    simulated-Challenger rs t (query-H q) = H-patch rs t ro q
    simulated-Challenger rs t (query-create-proof w Y) with L? w Y
    ... | yes p = just (Simulate rs t Y)
    ... | no ¬p = nothing

    real-Challenger : ∀ q → Challenger-Resp q
    real-Challenger (query-H q) = ro q
    real-Challenger (query-create-proof w Y) with L? w Y
    ... | yes p = just (L-to-Prf p)
    ... | no  _ = nothing

    challenger : 𝟚 → RS → Transcript → ∀ q → Challenger-Resp q
    challenger 0₂ _  _ = real-Challenger
    challenger 1₂ rs t = simulated-Challenger rs t

    open TranscriptRun
    -- β = 0₂ is real
    -- β = 1₂ is simulated
    Experiment : ∀ {A} → 𝟚 → RS → Adversary A → A × Transcript
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
  {RP RΣP : ★}
  (PF : Proof-System RP Prf)
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

  module Simulation-Sound-Extractability where

    Prf-in-Q : ∀ {Y} → Prf Y → Σ Adversary-Query Challenger-Resp → 𝟚
    Prf-in-Q π (query-H _ , _) = 0₂
    Prf-in-Q π (query-create-proof _ _ , just π') = Prf? π π'
    Prf-in-Q π (query-create-proof _ _ , nothing) = 0₂

    HistoryForExtractor = List (Prfs × Transcript)

    ExtractorServerPart =
         (past-history : HistoryForExtractor) {- previous invocations of Adv -}
         (on-going-transcript : Transcript)   {- about the current invocation of Adv -}
       → Π Adversary-Query Challenger-Resp

    Extractor : ★
    Extractor = Prfs → (init-transcript : Transcript)
                     → ExtractorServerPart
                     × Strategy 𝟙 (const (Prfs × Transcript)) (List W)

    valid-witness? : W → Λ → 𝟚
    valid-witness? w Y = ⌊ L? w Y ⌋

    valid-witnesses? : List W → List Λ → 𝟚
    valid-witnesses? [] [] = 1₂
    valid-witnesses? (w ∷ ws) (prf ∷ prfs) = valid-witness? w prf ∧ valid-witnesses? ws prfs
    valid-witnesses? _ _ = 0₂

    open TranscriptRun
    open StatefulRun

    module _ (t : Transcript) where
        Prf-in-Transcript : ∀ {Y} → Prf Y → 𝟚
        Prf-in-Transcript π = any (Prf-in-Q π) t

        K-winning-prf : Σ Λ Prf → 𝟚
        K-winning-prf (Y , π) = not (Verify Y π)
                              ∨ Prf-in-Transcript π

        K-winning-prfs : Prfs → 𝟚
        K-winning-prfs []   = 1₂
        K-winning-prfs prfs = any K-winning-prf prfs

    module Game
        (sim : Simulator PF)
        (open Is-Zero-Knowledge PF sim)
        {RA : ★}

        {- The malicious prover -}
        (Adv : RA → Adversary Prfs)
        (w : RA)(rs : RS)(ro : Random-Oracle)(K' : Extractor) where

        initial-result = Experiment ro 1₂ rs (Adv w)

        initial-prfs : Prfs
        initial-prfs = fst initial-result

        initial-transcript : Transcript
        initial-transcript = snd initial-result

        K-winning-intial-run : 𝟚
        K-winning-intial-run = K-winning-prfs initial-transcript initial-prfs

        -- Second run

        K = K' initial-prfs initial-transcript

        Kf = fst K
        Ks = snd K

        ws = fst (runT (λ h _ → runT (λ t q → Kf (mapᴸ snd h) t q) (Adv w) []) Ks [])

        K-winning-second-run : 𝟚
        K-winning-second-run = valid-witnesses? ws (mapᴸ fst initial-prfs)

  module Fiat-Shamir-Transformation
              (Σ-proto : Σ-Protocol)
              (shvzk : Special-Honest-Verifier-Zero-Knowledge.SHVZK Σ-proto)
              where

      open Σ-Protocol Σ-proto
      open Special-Honest-Verifier-Zero-Knowledge.SHVZK shvzk

      sFS : (H : (Λ × Commitment) → Challenge) → Proof-System RΣP (λ Y → Challenge × Σ-Prf Y)
      sFS H = record { Prove = sFS-Prove ; Verify = sFS-Verify }
        where
          sFS-Prove : RΣP → W → (Y : Λ) → (Challenge × Σ-Prf Y)
          sFS-Prove r w Y = let c = H (Y , get-A r Y) in c , get-f r Y c
          sFS-Verify : ∀ Y → Challenge × Σ-Prf Y → 𝟚
          sFS-Verify Y (c , π) = Σ-verifier Y (mk (Simulate Y c π) c π)

      -- The weak fiat-shamir is like the strong one but the H function do not get to see
      -- the statement, hence the 'snd'
      wFS : (H : Commitment → Challenge) → Proof-System RΣP (λ Y → Challenge × Σ-Prf Y)
      wFS H = sFS (H ∘ snd)

  module Theorem1
              (Σ-proto : Σ-Protocol)
              (shvzk : Special-Honest-Verifier-Zero-Knowledge.SHVZK Σ-proto)
              (ssound : Special-Soundness.SpSo)
              where
      open Simulation-Sound-Extractability
      {-
      S : Simulator PF
      S = record { H-patch = {!!}
                 ; Simulate = {!!}
                 ; verify-sim-spec = {!!} }
      -}

-- -}
-- -}
-- -}
-- -}
-- -}
