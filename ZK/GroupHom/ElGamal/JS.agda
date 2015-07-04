{-# OPTIONS --without-K #-}
open import Type.Eq
open import FFI.JS.BigI
open import Data.Product
open import Data.Bool.Base using (Bool)
-- open import SynGrp
open import ZK.GroupHom.Types
import ZK.GroupHom.ElGamal
import ZK.GroupHom.JSChal
open import Crypto.JS.BigI.FiniteField
  hiding (_*_; _^I_)
open import Crypto.JS.BigI.CyclicGroup
open import Relation.Binary.Core using (_≡_)
open import Algebra.Group
open import Algebra.Group.Homomorphism
open import Algebra.Group.Constructions

module ZK.GroupHom.ElGamal.JS (p q : BigI)(g : ℤ[ p ]★) where

open module ^-h = ^-hom p {q}

exp-× : ∀ {a b c}{A : Set a}{B : Set b}{C : Set c}
          (expA : A → C → A)
          (expB : B → C → B)
        → A × B → C → A × B
exp-× expA expB (b0 , b1) e = expA b0 e , expB b1 e

-- module EG = ZK.GroupHom.ElGamal `ℤ[ q ]+ `ℤ[ p ]★ _`^_ g
module EG = ZK.GroupHom.ElGamal {ℤ[ q ]} {ℤ[ p ]★} ℤ[ q ]+-grp ℤ[ p ]★-grp
                                {{ℤ[ p ]★-Eq?}} {_^_} ^-hom (λ {α}{x}{y} → ^-comm {α} {x} {y}) g

module known-enc-rnd (pk : EG.PubKey)
                     (M  : EG.Message)
                     (ct : EG.CipherText) where
  module zkh = ZK-hom (EG.Known-enc-rnd.zk-hom pk M ct)
  -- module zkh = `ZK-hom ker.zk-hom
  -- module zkp = ZK.GroupHom.JS q zkh.φ zkh.y
  verify-transcript = ZK.GroupHom.JSChal.verifier' q {ℤ[ q ]} {ℤ[ p ]★ EG.²}
                                    ℤ[ q ]+-grp (ℤ[ p ]★-grp EG.²-grp)
                  {{×-Eq? {{ℤ[ p ]★-Eq?}} {{ℤ[ p ]★-Eq?}}}}
                  (_⊗I_ q) (exp-× (_^I_ p) (_^I_ p)) zkh.φ zkh.φ-hom zkh.y
  {-
  prover-commitment : (r : zkp.Randomness)(w : zkp.Witness) → zkp.Commitment
  prover-commitment r w = zkp.Prover-Interaction.get-A (zkp.prover r w)
  prover-response : (r : zkp.Randomness)(w : zkp.Witness)(c : zkp.Challenge) → zkp.Response
  prover-response r w c = zkp.Prover-Interaction.get-f (zkp.prover r w) c
  verify-transcript : ∀ A c r → Bool
   -- (A : zkp.Commitment)(c : zkp.Challenge)(r : zkp.Response) → Bool
  verify-transcript = zkp.verifier'

-- -}
-- -}
-- -}
-- -}
