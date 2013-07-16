{-# OPTIONS --without-K #-}
open import Type hiding (★)
open import Function.NP using (flip)
open import FunUniverse.Category as Cat

module FunUniverse.Category.Op {t ℓ} {T : ★ t} {_`→_ : T → T → ★ ℓ} (cat : Category _`→_) where
    open Cat.Category _ cat

    op : Category (flip _`→_)
    op = id , flip _∘_
