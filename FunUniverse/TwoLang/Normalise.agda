open import Type
open import Function
open import Data.Two
open import Data.Nat.NP using (_+_)
open import Data.Fin.NP using (Fin; inject+; raise)
open import Data.Vec.NP using (Vec; []; _∷_; lookup)
open import Data.Bits   using (Bits)
open import FunUniverse.TwoLang

module FunUniverse.TwoLang.Normalise where

-- Normal forms
data No (I : ★) : ★
-- Neutral forms
data Ne (I : ★) : ★

data No I where
  0₂ 1₂ : No I
  ne    : Ne I → No I

data Ne I where
  input : I → Ne I
  fork  : (c : Ne I) (e₀ e₁ : No I) → Ne I

module _ {I} where
    forkNo : (c e₀ e₁ : No I) → No I
    forkNo 0₂     e₀ e₁ = e₀
    forkNo 1₂     e₀ e₁ = e₁
    forkNo (ne c) e₀ e₁ = ne (fork c e₀ e₁)

    normalise : E I → No I
    normalise (input x) = ne (input x)
    normalise (fork c e₀ e₁) = forkNo (normalise c) (normalise e₀) (normalise e₁)
    normalise 0₂ = 0₂
    normalise 1₂ = 1₂

module _ {I J} (f : I → J) where
    mapNo : No I → No J
    mapNe : Ne I → Ne J

    mapNo 0₂     = 0₂
    mapNo 1₂     = 1₂
    mapNo (ne x) = ne (mapNe x)

    mapNe (input x)      = input (f x)
    mapNe (fork e e₀ e₁) = fork (mapNe e) (mapNo e₀) (mapNo e₁)

module _ {I J} (f : I → No J) where
    bindNo : No I → No J
    bindNe : Ne I → No J

    bindNo 0₂     = 0₂
    bindNo 1₂     = 1₂
    bindNo (ne x) = bindNe x

    bindNe (input x)      = f x
    bindNe (fork e e₀ e₁) = forkNo (bindNe e) (bindNo e₀) (bindNo e₁)
