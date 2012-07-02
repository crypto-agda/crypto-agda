module flat-funs-prod where

open import Data.Unit using (⊤)
import Data.Product as ×
open × using (_×_; _,_)

open import data-universe
open import flat-funs

×-♭Funs : ∀ {s t} {S : Set s} {T : Set t} → FlatFuns S → FlatFuns T → FlatFuns (S × T)
×-♭Funs funs-S funs-T = mk (×-U S.universe T.universe)
                           (λ { (A₀ , A₁) (B₀ , B₁) → (A₀ S.`→ B₀) × (A₁ T.`→ B₁) })
  where module S = FlatFuns funs-S
        module T = FlatFuns funs-T

×⊤-♭Funs : ∀ {s} {S : Set s} → FlatFuns S → FlatFuns ⊤ → FlatFuns S
×⊤-♭Funs funs-S funs-T = mk S.universe (λ A B → (A S.`→ B) × (_ T.`→ _))
  where module S = FlatFuns funs-S
        module T = FlatFuns funs-T

×-♭Ops : ∀ {s t} {S : Set s} {T : Set t} {funs-S : FlatFuns S} {funs-T : FlatFuns T}
         → FlatFunsOps funs-S → FlatFunsOps funs-T
         → FlatFunsOps (×-♭Funs funs-S funs-T)
×-♭Ops ops-S ops-T
  = mk (S.id , T.id) (×.zip S._∘_ T._∘_)
       (S.<0b> , T.<0b>) (S.<1b> , T.<1b>) (S.cond , T.cond) (×.zip S.fork T.fork) (S.tt , T.tt)
       (×.zip S.<_,_> T.<_,_>) (S.fst , T.fst) (S.snd , T.snd)
       (S.dup , T.dup) (×.map S.first T.first)
       (S.swap , T.swap) (S.assoc , T.assoc)
       (S.<tt,id> , T.<tt,id>) (S.snd<tt,> , T.snd<tt,>)
       (×.zip S.<_×_> T.<_×_>) (×.map S.second T.second)
       (S.nil , T.nil) (S.cons , T.cons) (S.uncons , T.uncons)
  where module S = FlatFunsOps ops-S
        module T = FlatFunsOps ops-T

×⊤-♭Ops : ∀ {s} {S : Set s} {funs-S : FlatFuns S} {funs-⊤ : FlatFuns ⊤}
         → FlatFunsOps funs-S → FlatFunsOps funs-⊤
         → FlatFunsOps (×⊤-♭Funs funs-S funs-⊤)
×⊤-♭Ops ops-S ops-⊤
  = mk (S.id , T.id) (×.zip S._∘_ T._∘_)
       (S.<0b> , T.<0b>) (S.<1b> , T.<1b>) (S.cond , T.cond) (×.zip S.fork T.fork) (S.tt , T.tt)
       (×.zip S.<_,_> T.<_,_>) (S.fst , T.fst) (S.snd , T.snd)
       (S.dup , T.dup) (×.map S.first T.first)
       (S.swap , T.swap) (S.assoc , T.assoc)
       (S.<tt,id> , T.<tt,id>) (S.snd<tt,> , T.snd<tt,>)
       (×.zip S.<_×_> T.<_×_>) (×.map S.second T.second)
       (S.nil , T.nil) (S.cons , T.id) (S.uncons , T.id)
  where module S = FlatFunsOps ops-S
        module T = FlatFunsOps ops-⊤
