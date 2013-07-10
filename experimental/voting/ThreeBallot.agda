{-# OPTIONS --without-K #-}
module ThreeBallot
   -- ()
   where

open import Data.Fin using (Fin ; zero ; suc )
open import Data.Nat
open import Data.Bool.NP using (toℕ) renaming (false to 0b ; true to 1b)

open import Data.List using (List ; [] ; _∷_ ; length)
open import Data.Bits hiding (toℕ ; 0b ; 1b)

open import Data.Vec.NP renaming (map to vmap)
open import Data.Product

import Function.Inverse.NP as Inv
open Inv using (_↔_; _∘_; sym; id; inverses; module Inverse) renaming (_$₁_ to to; _$₂_ to from)

import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_ ; refl)

data Cand : Set where
  Nice'Guy Bad'Guy : Cand

Vote = Bits 2
Tag  = ℕ

record Ballot : Set where
  constructor mk
  field
    vote : Vote
    tag  : Tag

open Ballot

record 3'_ (A : Set) : Set where
  constructor [_][_][_]
  field
    1t 2t 3t : A

3Vote = 3' Vote
3Ballot = 3' Ballot

[_][_] : Bit → Bit → Bits 2
[ x ][ y ] = x ∷ y ∷ []

svote : Vote
svote = [ 0b ][ 1b ]

example : 3Vote
example = [ [ 1b ][ 0b ] ][ [ 0b ][ 1b ] ][ [ 0b ][ 1b ] ]

row-const : Bit → 3' Bit → Set
row-const b [ 1t ][ 2t ][ 3t ] = 1 + toℕ b ≡ toℕ 1t + toℕ 2t + toℕ 3t

voteFor : Vote → 3Vote → Set
voteFor (n ∷ b ∷ []) [ x ∷ x₁ ∷ [] ][ x₂ ∷ x₃ ∷ [] ][ x₄ ∷ x₅ ∷ [] ] = row-const n [ x ][ x₂ ][ x₄ ]
                                                                     × row-const b [ x₁ ][ x₃ ][ x₅ ]

vote-example : voteFor svote example
vote-example = refl , refl

cast : (_ _ : Vote) → Vote
cast i r = vnot r


vote-any : (intent receipt : Vote) → voteFor intent [ intent ][ receipt ][ cast intent receipt ]
vote-any (true ∷ true ∷ []) (true ∷ true ∷ []) = refl , refl
vote-any (true ∷ true ∷ []) (true ∷ false ∷ []) = refl , refl
vote-any (true ∷ true ∷ []) (false ∷ true ∷ []) = refl , refl
vote-any (true ∷ true ∷ []) (false ∷ false ∷ []) = refl , refl
vote-any (true ∷ false ∷ []) (true ∷ true ∷ []) = refl , refl
vote-any (true ∷ false ∷ []) (true ∷ false ∷ []) = refl , refl
vote-any (true ∷ false ∷ []) (false ∷ true ∷ []) = refl , refl
vote-any (true ∷ false ∷ []) (false ∷ false ∷ []) = refl , refl
vote-any (false ∷ true ∷ []) (true ∷ true ∷ []) = refl , refl
vote-any (false ∷ true ∷ []) (true ∷ false ∷ []) = refl , refl
vote-any (false ∷ true ∷ []) (false ∷ true ∷ []) = refl , refl
vote-any (false ∷ true ∷ []) (false ∷ false ∷ []) = refl , refl
vote-any (false ∷ false ∷ []) (true ∷ true ∷ []) = refl , refl
vote-any (false ∷ false ∷ []) (true ∷ false ∷ []) = refl , refl
vote-any (false ∷ false ∷ []) (false ∷ true ∷ []) = refl , refl
vote-any (false ∷ false ∷ []) (false ∷ false ∷ []) = refl , refl

{-

NP :

  (R?×V)^n → (3V)^n → (3B)^n → B^3n -⟨ shuffle ⟩→ b^3n → T

-}

Perm : ℕ → Set
Perm n = Fin n ↔ Fin n

shuffle : ∀ {n}{A : Set} → Perm n → Vec A n → Vec A n
shuffle p xs = tabulate (λ i → lookup (to p i) xs)

module _
  (tally : ∀ {n} → Vec Vote n → ℕ)
  (tally-stable : ∀ {n} vs π → tally {n} vs ≡ tally (shuffle π vs))
  where

  3-tally : ∀ {n} → Vec Ballot (3 * n) → ℕ
  3-tally {n} bs = tally (vmap vote bs) ∸ n


  lookup-map : ∀ {n}{A B : Set}(f : A → B)(i : Fin n)(xs : Vec A n)
             → f (lookup i xs) ≡ lookup i (vmap f xs)
  lookup-map f zero (x ∷ xs) = refl
  lookup-map f (suc i) (x ∷ xs) = lookup-map f i xs

  -- map g (tabulate f) = tabulate (g ∘ f)
  -- f (lookup i xs) ≡ lookup i (map f xs)
  3-tally-stable : ∀ {n} bs π → 3-tally {n} bs ≡ 3-tally {n} (shuffle π bs)
  3-tally-stable {n} bs p rewrite tally-stable (vmap vote bs) p
                           | ≡.sym (tabulate-ext (λ i → lookup-map vote (to p i) bs))
                           = ≡.cong (λ p₁ → tally p₁ ∸ n) (tabulate-∘ _ _)

{-
  Ballot privacy ☺
-}

module BallotPrivacy
  (RA : Set)
  where

  data Msg : Set where
    vote! : (intent receipt : Vote) → Msg
    stop! : Msg

  Resp = List Ballot

  Adv₀ = RA → Vote
  Adv₁ = RA → Resp → Msg
  Adv₂ = RA → (l : Resp) → Vec Ballot (3 * length l) → Bit

  Adv = Adv₀ × Adv₁ × Adv₂


  G : Adv → (∀ {n} → Perm n) → RA → Bit →  Bit
  G (A₀ , A₁ , A₂) π Ra b = {!!} where
    ε = A₀ Ra

    go : (r : Resp) → Vec Ballot (3 * length r) → Bit
    go r bb with A₁ Ra r | b
    go r bb | vote! intent receipt | 1b = {!!}
    go r bb | vote! intent receipt | 0b = {!!}
    go r bb | stop!                | _ = A₂ Ra r (shuffle π bb)
































3<4 : 3 < 4
3<4 =  s≤s (s≤s (s≤s (s≤s z≤n)))


