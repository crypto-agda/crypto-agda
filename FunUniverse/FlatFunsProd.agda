{-# OPTIONS --without-K #-}
module FunUniverse.FlatFunsProd where

open import Data.Unit using (⊤)
import Data.Product as ×
open × using (_×_; _,_)

open import FunUniverse.Data
open import FunUniverse.Core

×-FunU : ∀ {s t} {S : Set s} {T : Set t} → FunUniverse S → FunUniverse T → FunUniverse (S × T)
×-FunU funs-S funs-T = ×-U S.universe T.universe
                     , (λ { (A₀ , A₁) (B₀ , B₁) → (A₀ S.`→ B₀) × (A₁ T.`→ B₁) })
  where module S = FunUniverse funs-S
        module T = FunUniverse funs-T

×⊤-FunU : ∀ {s} {S : Set s} → FunUniverse S → FunUniverse ⊤ → FunUniverse S
×⊤-FunU funs-S funs-T = S.universe , (λ A B → (A S.`→ B) × (_ T.`→ _))
  where module S = FunUniverse funs-S
        module T = FunUniverse funs-T

×-FunOps : ∀ {s t} {S : Set s} {T : Set t} {funs-S : FunUniverse S} {funs-T : FunUniverse T}
         → FunOps funs-S → FunOps funs-T
         → FunOps (×-FunU funs-S funs-T)
×-FunOps ops-S ops-T = record
  { rewiring = record
                 { linRewiring = {!!}
                 ; tt = S.tt , T.tt
                 ; dup = S.dup , T.dup
                 ; <[]> = S.<[]> , T.<[]>
                 ; <_,_> = ×.zip S.<_,_> T.<_,_>
                 ; fst = S.fst , T.fst
                 ; snd = S.snd , T.snd
                 ; rewire = λ x → S.rewire x , T.rewire x
                 ; rewireTbl = λ x → S.rewireTbl x , T.rewireTbl x
                 }
  ; hasFork = {!×.zip S.fork T.fork!} , {!S.cond , T.cond!}
  ; <0₂> = S.<0₂> , T.<0₂>
  ; <1₂> = S.<1₂> , T.<1₂>
  }

  where module S = FunOps ops-S
        module T = FunOps ops-T

        {-
×⊤-FunOps : ∀ {s} {S : Set s} {funs-S : FunUniverse S} {funs-⊤ : FunUniverse ⊤}
         → FunOps funs-S → FunOps funs-⊤
         → FunOps (×⊤-FunU funs-S funs-⊤)
×⊤-FunOps ops-S ops-⊤
  = mk (S.id , T.id) (×.zip S._∘_ T._∘_)
       (S.<0b> , T.<0b>) (S.<1b> , T.<1b>) (S.cond , T.cond) (×.zip S.fork T.fork) (S.tt , T.tt)
       (×.zip S.<_,_> T.<_,_>) (S.fst , T.fst) (S.snd , T.snd)
       (S.dup , T.dup) (×.map S.first T.first)
       (S.swap , T.swap) (S.assoc , T.assoc)
       (S.<tt,id> , T.<tt,id>) (S.snd<tt,> , T.snd<tt,>)
       (×.zip S.<_×_> T.<_×_>) (×.map S.second T.second)
       {!(S.nil , T.nil) (S.cons , T.id)!} (S.uncons , T.id)
  where module S = FunOps ops-S
        module T = FunOps ops-⊤

        -- -}
