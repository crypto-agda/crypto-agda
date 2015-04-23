{-# OPTIONS --without-K #-}
module ZK.JSChecker where

open import Type
open import Function hiding (case_of_)
open import Data.Bool.Base
open import Data.Product
open import Data.List.Base using (List; []; _∷_; and; foldr)
open import Data.String.Base  using (String)

open import FFI.JS as JS hiding (_+_)
import FFI.JS.Console as Console
import FFI.JS.Process as Process
import FFI.JS.FS as FS
open import FFI.JS.Proc
open import Control.Process.Type

import FiniteField.JS as 𝔽

import FFI.JS.BigI as BigI
open BigI using (BigI; bigI)

bignum : Number → BigI
bignum n = bigI (Number▹String n) "10"

-- TODO check with undefined
bigdec : JSValue → BigI
bigdec v = bigI (castString v) "10"

record ZK-chaum-pedersen-pok-elgamal-rnd (ℤq ℤp★ : Set) : Set where
  field
    c s : ℤq
    g p q y α β A B : ℤp★
    m : Number

-- TODO dynamise me
t : Number
t = readNumber "1"

min-bytes : Number
min-bytes = readNumber "456"

min-bits : Number
min-bits = readNumber "8" JS.* min-bytes

abstract
  Checks = Bool → Bool

  run : Checks → Bool
  run c = c true

  infixr 9 _&_
  _&_ : Checks → Checks → Checks
  _&_ = _∘′_

  check' : (title  : String)
           (pred   : Bool)
           (errmsg : 𝟙 → String)
         → Checks
  check' title pred errmsg x =
    trace title pred λ b → warn-check b errmsg (b ∧ x)

  check-size : String → BigI → Checks
  check-size name value =
    check' ("check size of " ++ name ++ ": ")
           (BigI.byteLength value <Number min-bytes)
           (λ _ → "Not a necessarily a safe prime: less than " ++ Number▹String min-bits ++ " bits")

  check-pq-relation : (p q : BigI) → Checks
  check-pq-relation p q =
    check' "check p and q relation: "
           (BigI.equals (BigI.add BigI.1I (BigI.multiply BigI.2I q)) p)
           (λ _ → "Not a necessarily a safe group: 1+2*"
                ++ BigI.toString q ++ " != " ++ BigI.toString p)

  check-primality : String → BigI → Checks
  check-primality name value =
    check' ("check primality of " ++ name ++ ": ")
           (BigI.isProbablePrime value t)
           (λ _ → "Not a prime number: " ++ BigI.toString value)

  check-generator-group-order : (g q p : BigI) → Checks
  check-generator-group-order g q p =
    check' "check generator & group order: "
           (BigI.equals (BigI.modPow g q p) BigI.1I)
           (λ _ → "Not a generator of a group of order q: modPow "
                ++ BigI.toString g ++ " " ++ BigI.toString q ++ " "
                ++ BigI.toString p)

module [ℤq]ℤp★ (qI pI gI : BigI) where

  checks : Checks
  checks =
    check-pq-relation pI qI &
    check-size       "p" pI &
    check-primality  "q" qI &
    check-primality  "p" pI &
    check-generator-group-order gI qI pI

  open 𝔽 qI
    public
    using (ℤq; BigI▹ℤq; 0#; 1#; _+_; _−_; _*_; _/_)
    renaming (repr to ℤq-repr)

  open 𝔽 pI
    public
    using (_==_)
    renaming (BigI▹ℤq to BigI▹ℤp★; ℤq to ℤp★; _*_ to _·_; repr to ℤp★-repr
             ;_/_ to _·/_)

  g : ℤp★
  g = BigI▹ℤp★ gI

  _^_ : ℤp★ → ℤq → ℤp★
  b ^ e = BigI▹ℤp★ (BigI.modPow (ℤp★-repr b) (ℤq-repr e) pI)

zk-check-chaum-pedersen-pok-elgamal-rnd : ZK-chaum-pedersen-pok-elgamal-rnd BigI BigI → Checks
zk-check-chaum-pedersen-pok-elgamal-rnd pf
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
        checks
      & check' "g^s==A·α^c: "     ((g ^ s) == (A · (α ^ c)))        (λ _ → "")
      & check' "y^s==B·(β/M)^c: " ((y ^ s) == (B · ((β ·/ M) ^ c))) (λ _ → "")
  where
    module I = ZK-chaum-pedersen-pok-elgamal-rnd pf
    open [ℤq]ℤp★ I.q I.p I.g
    A = BigI▹ℤp★ I.A
    B = BigI▹ℤp★ I.B
    α = BigI▹ℤp★ I.α
    β = BigI▹ℤp★ I.β
    y = BigI▹ℤp★ I.y
    s = BigI▹ℤq  I.s
    c = BigI▹ℤq  I.c
    m = BigI▹ℤq  (bignum I.m)
    M = g ^ m

zk-check-one : Number → JSValue → Bool
zk-check-one ix arg = trace "ix="  ix λ _ →
                      trace "res=" (run res) id
 where
    stm = arg ·« "statement" »
    typ = stm ·« "type" »
    dat = stm ·« "data" »
    g   = bigdec (dat ·« "g" »)
    p   = bigdec (dat ·« "p" »)
    q   = bigdec (dat ·« "q" »)
    y   = bigdec (dat ·« "y" »)
    m   = castNumber (dat ·« "plain" »)
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

    res = check' "type of statement: " (typ === fromString "chaum-pedersen-pok-elgamal-rnd") (λ _ → "")
        & zk-check-chaum-pedersen-pok-elgamal-rnd pok

zk-check : JSValue → Bool
zk-check πs = and (decodeJSArray (castJSArray πs) zk-check-one)

srv : URI → JSProc
srv d =
  recv d λ q →
  send d (fromBool (zk-check q))
  end

-- Working around Agda.Primitive.lsuc being undefined
case_of_ : {A : Set} {B : Set₁} → A → (A → B) → B
case x of f = f x

main : JS!
main =
  Process.argv !₁ λ args →
  case JSArray▹ListString args of λ {
    (_node ∷ _run ∷ _test ∷ args') →
      case args' of λ {
        [] →
          server "127.0.0.1" "1337" srv !₁ λ uri →
          Console.log (showURI uri) >>
          end
      ; (arg ∷ args'') →
          case args'' of λ {
            [] →
              let opts =
                 -- fromJSObject (fromObject (("encoding" , fromString "utf8") ∷ []))
                 -- nullJS
                    JSON-parse "{\"encoding\":\"utf8\"}"
              in
              Console.log ("readFile=" ++ arg) >>
              FS.readFile arg opts !₂ λ err dat →
                Console.log ("readFile: err=" ++ err) >>
                Console.log (Bool▹String (zk-check (JSON-parse (castString dat)))) >>
                end
          ; _ →
              Console.log "usage" >>
              end
          }
      }
  ; _ →
      Console.log "usage" >>
      end
  }
-- -}
-- -}
-- -}
-- -}
