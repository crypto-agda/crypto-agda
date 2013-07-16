open import Type
open import Function
open import Data.Product using (proj₂)
open import Data.Two renaming (mux to mux₂)
open import Data.Nat.NP using (ℕ; zero; suc; _+_; _*_; module ℕ°)
open import Data.Fin.NP as Fin using (Fin; inject+; raise; bound; free; zero; suc)
open import Data.Vec.NP using (Vec; []; _∷_; lookup; tabulate)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Data.Bits using (Bits; _→ᵇ_; RewireTbl{-; 0ⁿ; 1ⁿ-})
open import Relation.Binary.PropositionalEquality

open import FunUniverse.Data
open import FunUniverse.Core
open import FunUniverse.Fin.Op
open import FunUniverse.Rewiring.Linear
open import FunUniverse.Category
open import Language.Simple.Interface

module FunUniverse.Fin.Op.Abstract where

private
  module BF = Rewiring finOpRewiring

module _ {E : ★ → ★} {Op} (lang : Lang Op 𝟚 E) where
    open Lang lang

    {-
    bits : ∀ {o} → Bits o → 0 →ᵉ o
    bits xs = 𝟚▹E ∘ flip Vec.lookup xs
    -}

    efinFunU : FunUniverse ℕ
    efinFunU = Bits-U , _→ᵉ_

    module EFinFunUniverse = FunUniverse efinFunU

    efinCat : Category _→ᵉ_
    efinCat = input , _∘ᵉ_

    private
      open EFinFunUniverse
      module _ {A B C D} (f : A `→ C) (g : B `→ D) where
        <_×_>  : (A `× B) `→ (C `× D)
        <_×_> x with Fin.cmp C D x
        <_×_> ._ | Fin.bound y = inject+ B <$> f y
        <_×_> ._ | Fin.free  y = raise   A <$> g y

    efinLin : LinRewiring efinFunU
    efinLin = mk efinCat (flip <_×_> input)
                         (λ {A} → input ∘ BF.swap {A})
                         (λ {A} → input ∘ BF.assoc {A})
                         input input <_×_> (λ {A} → <_×_> {A} input)
                         input input input input

    efinRewiring : Rewiring efinFunU
    efinRewiring = mk efinLin (λ()) (input ∘ BF.dup) (λ()) (λ f g → < f × g > ∘ᵉ (input ∘ BF.dup))
                      (input ∘ inject+ _) (λ {A} → input ∘ raise A)
                      (λ f → input ∘ BF.rewire f) (λ f → input ∘ BF.rewireTbl f)

    {-
    efinFork : HasFork efinFunU
    efinFork = cond , λ f g → second {1} < f , g > ⁏ cond
      where
        open Rewiring efinRewiring
        cond : ∀ {A} → `Bit `× A `× A `→ A
        cond {A} x = {!mux (return zero) (input (raise 1 (inject+ _ x))) (input (raise 1 (raise A x)))!}

    𝟚▹E = {!!}
    efinOps : FunOps efinFunU
    efinOps = mk efinRewiring efinFork (const (𝟚▹E 0₂)) (const (𝟚▹E 1₂))
    open Cong-*1 _→ᵉ_

    reify : ∀ {i o} → i →ᵇ o → i →ᵉ o
    reify = cong-*1′ ∘ FunOps.fromBitsFun efinOps
    -}

      {-
    eval-reify : eval (reify f)
    eval-reify = ?
    -}

    -- -}
