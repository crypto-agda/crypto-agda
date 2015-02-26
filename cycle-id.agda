{-# OPTIONS --with-K #-}
open import Function
open import Type using (Type)
open import Data.Nat.Base
open import Data.Product.NP
open import Data.Zero
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.NP
open import cycle using (here; there; [_]; _∷_)

module cycle-id (A : Type) where

open import cycle A id hiding (here; there; [_]; _∷_)

module _ {x z : A} where
    ∷-no-chain : ∀ (c : x ↦* z) → ¬(is-chain (x ∷ c))
    ∷-no-chain c ch with ch here (there here)
    ... | ()

module _ (x : A) where

    []-chain : is-chain [ x ]
    []-chain here here = refl

    c : ℕ → x ↦* x
    c zero    = [ x ]
    c (suc n) = x ∷ c n

    c+-no-chain : ∀ n → ¬(is-chain (c (suc n)))
    c+-no-chain n ch = ∷-no-chain (c n) ch

    c-no-uniq : ¬(uniq-↦* x x)
    c-no-uniq (c , co) with co (x ∷ c)
    ... | ()

c-chain-uniq : ∀ {x z : A}(c c' : x ↦C z) → fst c ≡ fst c'
c-chain-uniq (c , ch) (c' , ch') = go c c' ch ch'
  where
    go : ∀ {x z : A}(c c' : x ↦* z) → is-chain c → is-chain c' → c ≡ c'
    go [ _ ] [ ._ ] _ _ = refl
    go [ _ ] (._ ∷ c') _ ch' = 𝟘-elim (∷-no-chain c' ch')
    go (x ∷ c) [ ._ ]    ch _ = 𝟘-elim (∷-no-chain c ch)
    go (x ∷ c) (._ ∷ c') ch ch'
      = ap (_∷_ x) (go c c' (chain-∷ ch) (chain-∷ ch'))
