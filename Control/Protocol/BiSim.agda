open import Type
open import Control.Protocol.CoreOld
open import Relation.Binary.PropositionalEquality.NP
open import Data.Product

module Control.Protocol.BiSim where


module _ (Q : ★)(R : Q → ★)(A : ★)(_≈ᴬ_ : A → A → ★) where
  data ClientSim : Client Q R A → Client Q R A → ★ where
    ask  : ∀ {q c c'} → (∀ r → ClientSim (c r) (c' r)) → ClientSim (ask q c) (ask q c')
    done : ∀ {x y} → x ≈ᴬ y → ClientSim (done x) (done y)

module _ (Q : ★)(R : Q → ★)(A : ★)(_≈ᴬ_ : A → A → ★) where

  record ServerSim (x y : Server Q R A) : ★
  record ServerResponseSim {q : Q}(x y : ServerResponse Q R A q) : ★

  record ServerSim x y where
    coinductive
    field
      sim-srv-done : srv-done x ≈ᴬ srv-done y
      sim-srv-ask  : ∀ q → ServerResponseSim (srv-ask x q) (srv-ask y q)

  record ServerResponseSim {q} x y where
    constructor _,_
    field
      sim-srv-resp : srv-resp x ≡ srv-resp y
      sim-srv-cont : ServerSim (srv-cont x) (srv-cont y)

open ServerSim public
open ServerResponseSim public

module _ {X : ★} (_≈_ : X → X → ★) where
  BiSim : {P : Proto} → El X P → El X P → ★
  BiSim {end} p q = p ≈ q
  BiSim {Π' A B} p q = ∀ x → BiSim {B x} (p x) (q x)
  BiSim {Σ' A B} (x , p) (y , q) = Σ (x ≡ y) (λ eq → BiSim {B y}(subst _ eq p) q)
  BiSim {Client' Q R P} x f = ClientSim Q R (El X P) (BiSim {P}) x f
  BiSim {Server' Q R P} x f = ServerSim Q R (El X P) (BiSim {P}) x f

module BiSimServerProof {Q A B : ★}{R : Q → ★}{_≈ᴬ_ : A → A → ★}{_≈ᴮ_ : B → B → ★} where

  _≈×_ : A × B → A × B → ★
  (a , b) ≈× (a' , b') = a ≈ᴬ a' × b ≈ᴮ b'

  ServerProof : {s s' : Server Q R A}{c c' : Client Q R B}
              → ServerSim Q R A _≈ᴬ_ s s' → ClientSim Q R B _≈ᴮ_ c c'
              → Server-Com s c ≈× Server-Com s' c'
  ServerProof ss' (ask {q} x) rewrite sim-srv-resp (sim-srv-ask ss' q) =  ServerProof (sim-srv-cont (sim-srv-ask ss' _)) (x _)
  ServerProof ss' (done x₁) = (sim-srv-done ss') , x₁

module BiSimProof {X Y} where
  open import Relation.Binary.PropositionalEquality.NP
  open BiSimServerProof

  proof : (P : Proto){s s' : El X P}{c c' : El Y (dual P)}
        → BiSim _≡_ {P} s s' → BiSim _≡_ {dual P} c c' → com P s c ≡ com P s' c'
  proof end ss' cc' rewrite ss' | cc' = refl
  proof (Π' A B) ss' (eq , cc') rewrite eq = proof (B _) (ss' _) cc'
  proof (Σ' A B) (eq , ss') cc' rewrite eq = proof (B _) ss' (cc' _)
  proof (Client' Q R P) ss' cc' = let (cc'' , ss'') = ServerProof cc' ss' in proof P ss'' cc''
  proof (Server' Q R P) ss' cc' = let (ss'' , cc'') = ServerProof ss' cc' in proof P ss'' cc''
