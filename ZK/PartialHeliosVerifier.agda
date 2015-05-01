module ZK.PartialHeliosVerifier where

open import Type
open import Function hiding (case_of_)
open import Data.Bool.Base
open import Data.Product
open import Data.List.Base using (List; []; _∷_; and; foldr)
open import Data.String.Base  using (String)

open import FFI.JS as JS hiding (_+_; _/_; _*_; join)
open import FFI.JS.BigI as BigI
import FFI.JS.Console as Console
import FFI.JS.Process as Process
import FFI.JS.FS as FS
open import FFI.JS.SHA1
open import FFI.JS.Proc
open import Control.Process.Type

join : String → List String → String
join sep []       = ""
join sep (x ∷ xs) = x ++ foldr (λ y z → sep ++ y ++ z) "" xs

{-
instance
  showBigI = mk λ _ → showString ∘ BigI.toString
-}

G  = BigI
ℤq = BigI

BigI▹G : BigI → G
BigI▹G = id

BigI▹ℤq : BigI → ℤq
BigI▹ℤq = id

non0I : BigI → BigI
non0I x with equals x 0I
... | true  = throw "Should be non zero!" 0I
... | false = x

module BigICG (p q : BigI) where
  _^_  : G  → ℤq → G
  _·_  : G  → G  → G
  _/_  : G  → G  → G
  _+_  : ℤq → ℤq → ℤq
  _*_  : ℤq → ℤq → ℤq
  _==_ : (x y : G) → Bool

  _^_ = λ x y → modPow x y p
  _·_ = λ x y → mod (multiply x y) p
  _/_ = λ x y → mod (multiply x (modInv (non0I y) p)) p
  _+_ = λ x y → mod (add x y) q
  _*_ = λ x y → mod (multiply x y) q
  _==_ = equals

  sumI : List BigI → BigI
  sumI = foldr _+_ 0I

bignum : Number → BigI
bignum n = bigI (Number▹String n) "10"

-- TODO check with undefined
bigdec : JSValue → BigI
bigdec v = bigI (castString v) "10"

{-
print : {A : Set}{{_ : Show A}} → A → Callback0
print = Console.log ∘ show
-}

PubKey         = G
EncRnd         = ℤq {- randomness used for encryption of ct -}
Message        = G {- plain text message -}
Challenge      = ℤq
Response       = ℤq
CommitmentPart = G
CipherTextPart = G

module HeliosVerifyV3 (g : G) p q (y : PubKey) where
  open BigICG p q

  verify-chaum-pedersen : (α β : CipherTextPart)(M : Message)(A B : G)(c : Challenge)(s : Response) → Bool
  verify-chaum-pedersen α β M A B c s
      = trace "α=" α λ _ →
        trace "β=" β λ _ →
        trace "M=" M λ _ →
        trace "A=" A λ _ →
        trace "B=" B λ _ →
        trace "c=" c λ _ →
        trace "s=" s λ _ →
        (g ^ s) == (A · (α ^ c))
      ∧ (y ^ s) == (B · ((β / M) ^ c))

  verify-individual-proof : (α β : CipherTextPart)(ix : Number)(π : JSValue) → Bool
  verify-individual-proof α β ix π
      = trace "m=" m λ _ →
        trace "M=" M λ _ →
        trace "commitmentA=" A λ _ →
        trace "commitmentB=" B λ _ →
        trace "challenge=" c λ _ →
        trace "response=" s λ _ →
        res
      where
        m  = bignum ix
        M  = g ^ m
        A  = bigdec (π ·« "commitment" » ·« "A" »)
        B  = bigdec (π ·« "commitment" » ·« "B" »)
        c  = bigdec (π ·« "challenge" »)
        s  = bigdec (π ·« "response" »)
        res = verify-chaum-pedersen α β M A B c s

  -- Conform to HeliosV3 but it is too weak.
  -- One should follow a "Strong Fiat Shamir" transformation
  -- from interactive ZK proof to non-interactive ZK proofs.
  -- Namely one should hash the statement as well.
  --
  -- SHA1(A0 + "," + B0 + "," + A1 + "," + B1 + ... + "Amax" + "," + Bmax)
  hash-commitments : JSArray JSValue → BigI
  hash-commitments πs =
    fromHex $
    trace-call "SHA1(commitments)=" SHA1       $
    trace-call "commitments="       (join ",") $
    decodeJSArray πs λ _ π →
      (castString (π ·« "commitment" » ·« "A" »))
      ++ "," ++
      (castString (π ·« "commitment" » ·« "B" »))

  sum-challenges : JSArray JSValue → BigI
  sum-challenges πs =
    sumI $ decodeJSArray πs λ _ π → bigdec (π ·« "challenge" »)

  verify-challenges : JSArray JSValue → Bool
  verify-challenges πs =
      trace "hash(commitments)=" h λ _ →
      trace "sum(challenge)="    c λ _ →
      h == c
    where
      h = hash-commitments πs
      c = sum-challenges   πs

  verify-choice : (v : JSValue)(πs : JSArray JSValue) → Bool
  verify-choice v πs =
      trace "α=" α λ _ →
      trace "β=" β λ _ →
      verify-challenges πs
      ∧
      and (decodeJSArray πs $ verify-individual-proof α β)
    where
      α = bigdec (v ·« "alpha" »)
      β = bigdec (v ·« "beta"  »)

  verify-choices : (choices πs : JSArray JSValue) → Bool
  verify-choices choices πs =
    trace "TODO: check the array size of choices πs together election data" "" λ _ →
    and $ decodeJSArray choices λ ix choice →
      trace "verify choice " ix λ _ →
      verify-choice choice (castJSArray (πs Array[ ix ]))

  verify-answer : (answer : JSValue) → Bool
  verify-answer answer =
      trace "TODO: CHECK the overall_proof" "" λ _ →
      verify-choices choices individual-proofs
    where
      choices           = answer ·« "choices" »A
      individual-proofs = answer ·« "individual_proofs" »A
      overall-proof     = answer ·« "overall_proof" »A

  verify-answers : (answers : JSArray JSValue) → Bool
  verify-answers answers =
    and $ decodeJSArray answers λ ix a →
      trace "verify answer " ix λ _ →
      verify-answer a

  {-
  verify-election-hash =
  ""
  -- notice the whitespaces and the alphabetical order of keys
  -- {"email": ["ben@adida.net", "ben@mit.edu"], "first_name": "Ben", "last_name": "Adida"}
    computed_hash = base64.b64encode(hash.new(election.toJSON()).digest())[:-1]
    computed_hash == vote.election_hash:
  ""
  -}

  -- module _ {-(election : JSValue)-} where
  verify-ballot : (ballot : JSValue) → Bool
  verify-ballot ballot =
        trace "TODO: CHECK the election_hash: " election_hash λ _ →
        trace "TODO: CHECK the election_uuid: " election_uuid λ _ →
        verify-answers answers
      where
        answers       = ballot ·« "answers" »A
        election_hash = ballot ·« "election_hash" »
        election_uuid = ballot ·« "election_uuid" »

  verify-ballots : (ballots : JSArray JSValue) → Bool
  verify-ballots ballots =
      and $ decodeJSArray ballots λ ix ballot →
        trace "verify ballot " ix λ _ →
        verify-ballot ballot

-- Many checks are still missing!
verify-helios-election : (arg : JSValue) → Bool
verify-helios-election arg = trace "res=" res id
 where
    ed = arg ·« "election_data" »
    bs = arg ·« "ballots" »A
    pk = ed  ·« "public_key" »
    g  = bigdec (pk ·« "g" »)
    p  = bigdec (pk ·« "p" »)
    q  = bigdec (pk ·« "q" »)
    y  = bigdec (pk ·« "y" »)
    res =
        trace "g=" g λ _ →
        trace "p=" p λ _ →
        trace "q=" q λ _ →
        trace "y=" y λ _ →
        HeliosVerifyV3.verify-ballots g p q y bs

srv : URI → JSProc
srv d =
  recv d λ q →
  send d (fromBool (verify-helios-election q))
  end

-- Working around Agda.Primitive.lsuc being undefined
case_of_ : {A : Set} {B : Set} → A → (A → B) → B
case x of f = f x

main : JS!
main =
  Process.argv !₁ λ args →
  case JSArray▹ListString args of λ {
    (_node ∷ _run ∷ _test ∷ args') →
      case args' of λ {
        [] →
          server "127.0.0.1" "1337" srv !₁ λ uri →
          Console.log (showURI uri)
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
                Console.log ("readFile: err=" ++ JS.toString err) >>
                Console.log (Bool▹String (verify-helios-election (JSON-parse (castString dat))))
          ; _ →
              Console.log "usage"
          }
      }
  ; _ →
      Console.log "usage"
  }
-- -}
-- -}
-- -}
-- -}
-- -}
