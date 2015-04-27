{-# OPTIONS --without-K #-}
module ZK.JSChecker where

open import Function         using (id; _∘′_; case_of_)
open import Data.Bool.Base   using (Bool; true; false; _∧_)
open import Data.List.Base   using (List; []; _∷_; and; foldr)
open import Data.String.Base using (String)

open import FFI.JS
  hiding (check; trace)
  renaming (_*_ to _*Number_)
-- open import FFI.JS.Proc using (URI; JSProc; showURI; server)
-- open import Control.Process.Type
import FFI.JS.Console as Console
import FFI.JS.Process as Process
import FFI.JS.FS as FS

import FiniteField.JS as 𝔽

import FFI.JS.BigI as BigI
open BigI using (BigI; bigI)

trace : {A B : Set}(msg : String)(inp : A)(f : A → B) → B
trace _ inp f = f inp

bignum : Number → BigI
bignum n = bigI (Number▹String n) "10"

-- TODO check with undefined
bigdec : JSValue → BigI
bigdec v = bigI (castString v) "10"

record ZK-chaum-pedersen-pok-elgamal-rnd (ℤq ℤp★ : Set) : Set where
  field
    m c s : ℤq
    g p q y α β A B : ℤp★

-- TODO dynamise me
t : Number
t = readNumber "10"

-- TODO: check if this is large enough
min-bits-q : Number
min-bits-q = 256N

min-bits-p : Number
min-bits-p = 2048N

check : (title  : String)
        (pred   : Bool)
        (errmsg : 𝟙 → String)
     → JS!
check title true  errmsg = Console.log (title ++ ": PASS")
check title false errmsg = Console.log (title ++ ": FAIL [" ++ errmsg _ ++ "]")

check-size : Number → String → BigI → JS!
check-size min-bits name value =
  check ("check size of " ++ name)
        (len ≥Number min-bits)
        (λ _ → name ++ " is not a necessarily a safe prime: "
             ++ BigI.toString value    ++ " has "
             ++ Number▹String len      ++ " bits which is less than "
             ++ Number▹String min-bits ++ " bits")
  module Check-size where
    len = BigI.byteLength value *Number 8N

check-pq-relation : (p q : BigI) → JS!
check-pq-relation p q =
  check ("check p and q relation p-1/q=" ++ BigI.toString s)
        (equals r 0I)
        (λ _ → "Not necessarily a safe group: (p-1) mod q != 0\np="
             ++ BigI.toString p
             ++ ", q=" ++ BigI.toString q)
  module Check-pq-relation where
    open BigI
    p-1 = subtract p 1I
    r   = mod    p-1 q
    s   = divide p-1 q

check-primality : String → BigI → JS!
check-primality name value =
  check ("check primality of " ++ name)
        (BigI.isProbablePrime value t)
        (λ _ → "Not a prime number: " ++ BigI.toString value)

check-generator-group-order : (g q p : BigI) → JS!
check-generator-group-order g q p =
  check "check generator & group order"
        (BigI.equals (BigI.modPow g q p) BigI.1I)
        (λ _ → "Not a generator of a group of order q: modPow "
             ++ BigI.toString g ++ " " ++ BigI.toString q ++ " "
             ++ BigI.toString p)

module [ℤq]ℤp★ (qI pI gI : BigI) where

  checks : JS!
  checks =
    check-pq-relation      pI qI >>
    check-size min-bits-q "q" qI >>
    check-size min-bits-p "p" pI >>
    check-primality       "q" qI >>
    check-primality       "p" pI >>
    check-generator-group-order gI qI pI

  module ℤq = 𝔽 qI
    using (0#; 1#; _+_; _−_; _*_; _/_)
    renaming (𝔽 to ℤq; fromBigI to BigI▹ℤq; repr to ℤq-repr)
  module ℤp★ = 𝔽 pI
    using (_==_)
    renaming ( fromBigI to BigI▹ℤp★; 𝔽 to ℤp★; _*_ to _·_
             ; repr to ℤp★-repr; _/_ to _·/_)

  open ℤq  -- public -- <- BUG
  open ℤp★ public

  g : ℤp★
  g = BigI▹ℤp★ gI

  _^_ : ℤp★ → ℤq → ℤp★
  b ^ e = BigI▹ℤp★ (BigI.modPow (ℤp★-repr b) (ℤq-repr e) pI)

zk-check-chaum-pedersen-pok-elgamal-rnd : ZK-chaum-pedersen-pok-elgamal-rnd BigI BigI → JS!
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
      >> check "g^s==A·α^c"     ((g ^ s) == (A · (α ^ c)))        (λ _ → "")
      >> check "y^s==B·(β/M)^c" ((y ^ s) == (B · ((β ·/ M) ^ c))) (λ _ → "")
  module Zk-check-chaume-pedersen-pok-elgamal-rnd where
    module I = ZK-chaum-pedersen-pok-elgamal-rnd pf
    open [ℤq]ℤp★ I.q I.p I.g
    open ℤq
--  open ℤp★ -- <- BUG
    A = BigI▹ℤp★ I.A
    B = BigI▹ℤp★ I.B
    α = BigI▹ℤp★ I.α
    β = BigI▹ℤp★ I.β
    y = BigI▹ℤp★ I.y
    s = BigI▹ℤq  I.s
    c = BigI▹ℤq  I.c
    m = BigI▹ℤq  I.m
    M = g ^ m

zk-check : JSValue → JS!
zk-check arg =
    check "type of statement" (typ === fromString "chaum-pedersen-pok-elgamal-rnd")
                              (λ _ → "")
 >> zk-check-chaum-pedersen-pok-elgamal-rnd pok
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
              FS.readFile arg nullJS !₂ λ err dat →
                check "reading input file" (is-null err)
                       (λ _ → "readFile error: " ++ toString err) >>
                zk-check (JSON-parse (castString dat))
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
