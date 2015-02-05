open import Function
open import Data.Product.NP
open import Data.Two
open import Data.One
open import Relation.Binary.PropositionalEquality

module zk
  (Commit Chal Resp {-Rver Rprv-} Secret : Set)
  (_==-commit_ : Commit → Commit → 𝟚)
  (verif : Commit → Chal → Resp → 𝟚)

  -- the challenges must be different for the trick to work
  (trick : Commit → (cr0 cr1 : Chal × Resp) → fst cr0 ≢ fst cr1 → Secret)
  where

module Ended (End : Set) where
    Ver : Set
    Ver = Commit →
          Chal   ×
         (Resp   →
          End)

    Prv : Set
    Prv = Commit ×
         (Chal   →
          Resp   ×
          End)

    Log : Set
    Log = Commit ×
         (Chal   ×
         (Resp   ×
          End))

    -- Condition for the "picky" verifier which might not
    -- accept a particular commitment.
    Bad : Set
    Bad = Commit →
          𝟚 ×
          End

    BadLog : Set
    BadLog = Commit ×
          𝟚 ×
          End

open Ended

run : ∀ {E-ver E-prv} → Ver E-ver → Prv E-prv → Log (E-ver × E-prv)
run ver (commit , prv) =
  let (chal , k-ver) = ver commit
      (resp , k-prv) = prv chal
   in commit , chal , resp , k-ver resp , k-prv

verif-log : ∀ {X} → Log X → (X → 𝟚) → 𝟚
verif-log (commit , chal , resp , x) k = verif commit chal resp ∧ k x

ver : (Commit → Chal) → Ver 𝟙
ver h = λ c → h c , _

Ver₂ = Ver ∘ Ver
Prv₂ = Prv ∘ Prv
Log₂ = Log ∘ Log

_⇆₁_ : Ver 𝟙 → Prv 𝟙 → 𝟚
ver ⇆₁ prv = verif-log (run ver prv) λ _ → 1₂

_⇆₂_ : Ver₂ 𝟙 → Prv₂ 𝟙 → 𝟚
ver ⇆₂ prv = verif-log (run ver prv) λ { (v' , p') →
              verif-log (run v' p') λ _ → 1₂
             }

ver₂ : Chal → Chal → Ver₂ 𝟙
ver₂ c₀ c₁ = λ _ → c₀ , λ _ _ → c₁ , _

tricked-log₂ : ∀ {X} → Log₂ X → 𝟚
tricked-log₂ (commit , chal , resp , commit' , _ , _) = commit ==-commit commit'

Honest-Prv : Prv 𝟙 → Set
Honest-Prv prv = ∀ c → ver c ⇆₁ prv ≡ 1₂

module _ (h : 𝟚 → Commit → Chal)
         (h-diff : ∀ c → h 0₂ c ≢ h 1₂ c) where

    extr-prv : Prv 𝟙 → Secret
    extr-prv (commit , prv) = trick commit (c₀ , fst (prv c₀)) (c₁ , fst (prv c₁)) (h-diff commit)
       where c₀ = h 0₂ commit
             c₁ = h 1₂ commit

    extr-ver : Ver₂ 𝟙
    extr-ver commit₀ = h 0₂ commit₀ , λ r₀ commit₁ → h 1₂ commit₁ , _

    -- This condition defines the events we want to consider
    cond-ver : Ver (Bad 𝟙)
    cond-ver commit₀ = h 0₂ commit₀ , λ r₀ commit₁ → commit₀ ==-commit commit₁ , _

--Pr[ extr-ver ⇆ prv | tricked-log ]

-- TODO specify the retry event of Extr' and then when the conditional process succeed then the log can be "tricked"

-- -}
-- -}
-- -}
-- -}
