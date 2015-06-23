{-# OPTIONS --without-K #-}
open import FFI.JS.BigI
open import Data.Bool.Base using (Bool)
open import SynGrp
open import ZK.GroupHom.Types
import ZK.GroupHom.ElGamal
import ZK.GroupHom.JS

module ZK.GroupHom.ElGamal.JS (p q : BigI)(g : ℤ[ p ]★) where

module EG = ZK.GroupHom.ElGamal `ℤ[ q ]+ `ℤ[ p ]★ _`^_ g

module known-enc-rnd (pk : EG.PubKey)
                     (M  : EG.Message)
                     (ct : EG.CipherText) where
  module ker = EG.Known-enc-rnd pk M ct
  module zkh = `ZK-hom ker.zk-hom
  module zkp = ZK.GroupHom.JS q zkh.`φ zkh.y
  prover-commitment : (r : zkp.Randomness)(w : zkp.Witness) → zkp.Commitment
  prover-commitment r w = zkp.Prover-Interaction.get-A (zkp.prover r w)
  prover-response : (r : zkp.Randomness)(w : zkp.Witness)(c : zkp.Challenge) → zkp.Response
  prover-response r w c = zkp.Prover-Interaction.get-f (zkp.prover r w) c
  verify-transcript : (A : zkp.Commitment)(c : zkp.Challenge)(r : zkp.Response) → Bool
  verify-transcript A c r = zkp.verifier (zkp.Transcript.mk A c r)

-- -}
-- -}
-- -}
-- -}
