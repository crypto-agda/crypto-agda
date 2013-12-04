{-# OPTIONS --copatterns #-}
open import Type
open import Function
open import Data.Product
open import Control.Strategy renaming (map to mapS)

module Control.Strategy.Utils where

record Proto : ★₁ where
  constructor P[_,_]
  field
    Q : ★
    R : Q → ★

Client : Proto → ★ → ★
Client P[ Q , R ] A = Strategy Q R A

{-
data Bisim {P P' A A'} (RA : A → A' → ★) : Client P A → Client P' A' → ★ where
  ask-nop : ∀ {q? cont clt} r
            → Bisim RA (cont r) clt
            → Bisim RA (ask q? cont) clt
  ask-ask : ∀ q₀ q₁ cont₀ cont₁ r₀ r₁
            → ({!!} → Bisim RA (cont₀ r₀) (cont₁ r₁))
            → Bisim RA (ask q₀ cont₀) (ask q₁ cont₁)
-}
module Unused where
  mapS' : ∀ {A B Q Q' R} (f : A → B) (g : Q → Q') → Strategy Q (R ∘ g) A → Strategy Q' R B
  mapS' f g (ask q cont) = ask (g q) (λ r → mapS' f g (cont r))
  mapS' f g (done x)     = done (f x)

[_,_]=<<_ : ∀ {A B Q Q' R} (f : A → Strategy Q' R B) (g : Q → Q') → Strategy Q (R ∘ g) A → Strategy Q' R B
[ f , g ]=<< ask q? cont = ask (g q?) (λ r → [ f , g ]=<< cont r)
[ f , g ]=<< done x      = f x

module Rec {A B Q : ★} {R : Q → ★} {M : ★ → ★}
           (runAsk : ∀ {A} → (q : Q) → (R q → M A) → M A)
           (runDone : A → M B) where
  runMM : Strategy Q R A → M B
  runMM (ask q? cont) = runAsk q? (λ r → runMM (cont r))
  runMM (done x)      = runDone x

module MM {A B Q : ★} {R : Q → ★} {M : ★ → ★}
         (_>>=M_ : ∀ {A B : ★} → M A → (A → M B) → M B)
         (runAsk : (q : Q) → M (R q))
         (runDone : A → M B) where
  runMM : Strategy Q R A → M B
  runMM (ask q? cont) = runAsk q? >>=M (λ r → runMM (cont r))
  runMM (done x)      = runDone x

module _ {A B Q Q' : ★} {R : Q → ★} {R'}
         (f : (q : Q) → Strategy Q' R' (R q))
         (g : A → Strategy Q' R' B) where
  [_,_]=<<'_ : Strategy Q R A → Strategy Q' R' B
  [_,_]=<<'_ (ask q? cont) = f q? >>= λ r → [_,_]=<<'_ (cont r)
  [_,_]=<<'_ (done x)      = g x

record ServerResp (P : Proto) (q : Proto.Q P) (A : ★₀) : ★₀ where
  coinductive
  open Proto P
  field
      srv-resp : R q
      srv-cont : ∀ q → ServerResp P q A
open ServerResp

Server : Proto → ★₀ → ★₀
Server P A = ∀ q → ServerResp P q A

OracleServer : Proto → ★₀
OracleServer P[ Q , R ] = (q : Q) → R q

module _ {P : Proto} {A : ★} where
  open Proto P
  com : Server P A → Client P A → A
  com srv (ask q κc) = com (srv-cont r) (κc (srv-resp r)) where r = srv q
  com srv (done x)   = x

module _ {P P' : Proto} {A A' : ★} where
  module P = Proto P
  module P' = Proto P'
  record MITM : ★ where
    coinductive
    field
      hack-query : (q' : P'.Q) → Client P (P'.R q' × MITM)
      hack-result : A' → Client P A
  open MITM

  module WithOutBind where
      hacked-com-client : Server P A → MITM → Client P' A' → A
      hacked-com-mitm : ∀ {q'} → Server P A → Client P (P'.R q' × MITM) → (P'.R q' → Client P' A') → A
      hacked-com-srv-resp : ∀ {q q'} → ServerResp P q A → (P.R q → Client P (P'.R q' × MITM)) → (P'.R q' → Client P' A') → A

      hacked-com-srv-resp r mitm clt = hacked-com-mitm (srv-cont r) (mitm (srv-resp r)) clt

      hacked-com-mitm srv (ask q? mitm) clt = hacked-com-srv-resp (srv q?) mitm clt
      hacked-com-mitm srv (done (r' , mitm)) clt = hacked-com-client srv mitm (clt r')

      hacked-com-client srv mitm (ask q' κc) = hacked-com-mitm srv (hack-query mitm q') κc
      hacked-com-client srv mitm (done x) = com srv (hack-result mitm x)

  mitm-to-client-trans : MITM → Client P' A' → Client P A
  mitm-to-client-trans mitm (ask q? cont) = hack-query mitm q? >>= λ { (r' , mitm') → mitm-to-client-trans mitm' (cont r') }
  mitm-to-client-trans mitm (done x)      = hack-result mitm x

  hacked-com : Server P A → MITM → Client P' A' → A
  hacked-com srv mitm clt = com srv (mitm-to-client-trans mitm clt)

module _ (P : Proto) (A : ★) where
  open Proto P
  open MITM
  honest : MITM {P} {P} {A} {A}
  hack-query  honest q = ask q λ r → done (r , honest)
  hack-result honest a = done a

module _ (P : Proto) (A : ★) (Oracle : OracleServer P) where
  oracle-server : Server P A
  srv-resp (oracle-server q) = Oracle q
  srv-cont (oracle-server q) = oracle-server

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
