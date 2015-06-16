{-# OPTIONS --without-K #-}
module ZK.JSChecker where

open import Function         using (id; _∘′_; case_of_)
open import Data.Bool.Base   using (Bool; true; false; _∧_)
open import Data.List.Base   using (List; []; _∷_; and; foldr)
open import Data.String.Base using (String)

open import FFI.JS
open import FFI.JS.Check
-- open import FFI.JS.Proc using (URI; JSProc; showURI; server)
-- open import Control.Process.Type
import FFI.JS.Console as Console
import FFI.JS.Process as Process
import FFI.JS.FS as FS

import FFI.JS.BigI as BigI
open BigI using (BigI; bigI)

import Crypto.JS.BigI.ZqZp as ZqZp

-- TODO dynamise me
primality-test-probability-bound : Number
primality-test-probability-bound = readNumber "10"

-- TODO: check if this is large enough
min-bits-q : Number
min-bits-q = 256N

min-bits-p : Number
min-bits-p = 2048N

-- TODO check with undefined
bigdec : JSValue → BigI
bigdec v = bigI (castString v) "10"

-- TODO bug (undefined)!
record ZK-chaum-pedersen-pok-elgamal-rnd {--(ℤq ℤp★ : Set)--} : Set where
  field
    m c s : BigI {--ℤq--}
    g p q y α β A B : BigI --ℤp★

zk-check-chaum-pedersen-pok-elgamal-rnd! : ZK-chaum-pedersen-pok-elgamal-rnd {-BigI BigI-} → JS!
zk-check-chaum-pedersen-pok-elgamal-rnd! pf
      = trace "g=" g λ _ →
        trace "p=" I.p λ _ →
        trace "q=" I.q λ _ →
        trace "y=" y λ _ →
        trace "α=" α λ _ →
        trace "β=" β λ _ →
        trace "m=" m λ _ →
        trace "M=" M λ _ →
        trace "A=" A λ _ →
        trace "B=" B λ _ →
        trace "c=" c λ _ →
        trace "s=" s λ _ →
         checks!
      >> check! "g^s==A·α^c"     ((g ^ s) == (A · (α ^ c)))        (λ _ → "")
      >> check! "y^s==B·(β/M)^c" ((y ^ s) == (B · ((β ·/ M) ^ c))) (λ _ → "")
  module ZK-check-chaum-pedersen-pok-elgamal-rnd where
    module I = ZK-chaum-pedersen-pok-elgamal-rnd pf
    params = record
      { primality-test-probability-bound = primality-test-probability-bound
      ; min-bits-q = min-bits-q
      ; min-bits-p = min-bits-p
      ; qI = I.q
      ; pI = I.p
      ; gI = I.g
      }
    open module [ℤq]ℤp★ = ZqZp params
    A = BigI▹ℤp★ I.A
    B = BigI▹ℤp★ I.B
    α = BigI▹ℤp★ I.α
    β = BigI▹ℤp★ I.β
    y = BigI▹ℤp★ I.y
    s = BigI▹ℤq  I.s
    c = BigI▹ℤq  I.c
    m = BigI▹ℤq  I.m
    M = g ^ m

zk-check! : JSValue → JS!
zk-check! arg =
    check! "type of statement" (typ === fromString "chaum-pedersen-pok-elgamal-rnd")
                               (λ _ → "")
 >> zk-check-chaum-pedersen-pok-elgamal-rnd! pok
 module Zk-check where
    stm = arg ·« "statement" »
    typ = stm ·« "type" »
    dat = stm ·« "data" »
    g   = bigdec (dat ·« "g" »)
    p   = bigdec (dat ·« "p" »)
    q   = bigdec (dat ·« "q" »)
    y   = bigdec (dat ·« "y" »)
    m   = bigdec (dat ·« "plain" »)
    enc = dat ·« "enc" »
    α   = bigdec (enc ·« "alpha" »)
    β   = bigdec (enc ·« "beta"  »)
    prf = arg ·« "proof" »
    com = prf ·« "commitment" »
    A   = bigdec (com ·« "A" »)
    B   = bigdec (com ·« "B" »)
    c   = bigdec (prf ·« "challenge" »)
    s   = bigdec (prf ·« "response" »)
    pok = record { g = g; p = p; q = q; y = y; α = α; β = β; A = A; B = B; c = c; s = s; m = m }

{-
srv : URI → JSProc
srv d =
  recv d λ q →
  send d (fromBool (zk-check q))
  end
-}

-- Working around Agda.Primitive.lsuc being undefined
-- case_of_ : {A : Set} {B : Set} → A → (A → B) → B
-- case x of f = f x

main : JS!
main =
  Process.argv !₁ λ args →
  case JSArray▹ListString args of λ {
    (_node ∷ _run ∷ _test ∷ args') →
      case args' of λ {
        [] →
        Console.log "usage: No arguments"
        {- server "127.0.0.1" "1337" srv !₁ λ uri →
           Console.log (showURI uri)
         -}
      ; (arg ∷ args'') →
          case args'' of λ {
            [] →
              Console.log ("Reading input file: " ++ arg) >>
              FS.readFile arg nullJS !₂ λ err dat →
                check! "reading input file" (is-null err)
                       (λ _ → "readFile error: " ++ toString err) >>
                zk-check! (JSON-parse (toString dat))
          ; _ →
              Console.log "usage: Too many arguments"
          }
      }
  ; _ →
      Console.log "usage"
  }
-- -}
-- -}
-- -}
-- -}
