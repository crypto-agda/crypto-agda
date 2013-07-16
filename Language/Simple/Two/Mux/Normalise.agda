open import Type
open import Function
open import Data.Two    renaming (mux to mux₂)
open import Data.Nat.NP using (_+_)
open import Data.Fin.NP using (Fin; inject+; raise)
open import Data.Vec.NP using (Vec; []; _∷_; lookup)
open import Data.Bits   using (Bits)

open import Language.Simple.Two.Mux

module Language.Simple.Two.Mux.Normalise where

-- Normal forms
data No (I : ★) : ★
-- Neutral forms
data Ne (I : ★) : ★

data No I where
  0₂ 1₂ : No I
  ne    : Ne I → No I

data Ne I where
  var : I → Ne I
  mux : (c : Ne I) (e₀ e₁ : No I) → Ne I

module _ {I} where
    muxNo : (c e₀ e₁ : No I) → No I
    muxNo 0₂     e₀ e₁ = e₀
    muxNo 1₂     e₀ e₁ = e₁
    muxNo (ne c) e₀ e₁ = ne (mux c e₀ e₁)

    normalise : E I → No I
    normalise (var x)       = ne (var x)
    normalise (mux c e₀ e₁) = muxNo (normalise c) (normalise e₀) (normalise e₁)
    normalise 0₂            = 0₂
    normalise 1₂            = 1₂

module _ {I J} (f : I → J) where
    mapNo : No I → No J
    mapNe : Ne I → Ne J

    mapNo 0₂     = 0₂
    mapNo 1₂     = 1₂
    mapNo (ne x) = ne (mapNe x)

    mapNe (var x)       = var (f x)
    mapNe (mux e e₀ e₁) = mux (mapNe e) (mapNo e₀) (mapNo e₁)

module _ {I J} (f : I → No J) where
    bindNo : No I → No J
    bindNe : Ne I → No J

    bindNo 0₂     = 0₂
    bindNo 1₂     = 1₂
    bindNo (ne x) = bindNe x

    bindNe (var x)       = f x
    bindNe (mux e e₀ e₁) = muxNo (bindNe e) (bindNo e₀) (bindNo e₁)
