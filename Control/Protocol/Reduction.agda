{-# OPTIONS --copatterns #-}
open import Type
open import Control.Protocol.CoreOld
open import Data.Product

module Control.Protocol.Reduction where

record RServerSim (P : Proto)(Q : ★)(R : Q → ★)(A : Proto) : ★₁
record LServerSim (P : Proto)(Q : ★)(R : Q → ★)(A : Proto) : ★₁
record _[_,_,_]⊢Server[_,_,_] (A : Proto)(Q : ★)(R : Q → ★)(q : Q)(Q' : ★)(R' : Q' → ★)(B : Proto) : ★₁
record Client[_,_,_]⊢[_,_,_]_ (Q : ★)(R : Q → ★)(A : Proto)(Q' : ★)(R' : Q' → ★)(q' : Q')(B : Proto) : ★₁
-- can do the dual of the first or do the second..
data _⊢_ : Proto → Proto → ★₁ where
  end  :

      ------------
       end ⊢ end

  LΣ : ∀ {A B Q} →

       (Π A λ x → B x ⊢ Q)
    → ----------------------
            Σ' A B ⊢ Q

  RΣ : ∀ {A B Q} →

       (Σ A λ x → Q ⊢ B x)
    → ----------------------
            Q ⊢ Σ' A B

  LΠ : ∀ {A B Q} →

       (Σ A λ x → B x ⊢ Q)
    → ----------------------
            Π' A B ⊢ Q

  RΠ : ∀ {A B Q} →

       (Π A λ x → Q ⊢ B x)
    → ----------------------
            Q ⊢ Π' A B

  RC-done : ∀ {Q' R' B Q} →

              Q ⊢ B
    → ----------------------
       Q ⊢ Client' Q' R' B

  LS-done : ∀ {Q' R' B Q} →

              B ⊢ Q
    → ----------------------
       Server' Q' R' B ⊢ Q

  RC-ask  : ∀ {Q' R' B Q} →

        (Σ Q' λ q? → R' q? → Q ⊢ Client' Q' R' B)
    → --------------------------------------------
                Q ⊢ Client' Q' R' B

  LS-ask  : ∀ {Q' R' B Q} →

         (Σ Q' λ q? → R' q? → Server' Q' R' B ⊢ Q)
     → ---------------------------------------------
                Server' Q' R' B ⊢ Q

  RS : ∀ {P Q R A} →

       RServerSim P Q R A
    → ---------------------
        P ⊢ Server' Q R A

  LC : ∀ {P Q R A} →

       LServerSim P Q R A
    → ---------------------
        Client' Q R P ⊢ A

  -- l-client : ∀ {Q R A P} → Sim A P → Lazy (Sim (Σ' Q λ q → R q →' Client' Q R A) P) → Sim (Client' Q R A) P


data _⊢[_,_,_]_ : Proto → (Q : ★)(R : Q → ★) → Q → Proto → ★₁ where
  ret : ∀ {P Q R q A} →

      (Σ (R q) λ _ → RServerSim P Q R A)
    → -----------------------------------
             P ⊢[ Q , R , q ] A

  LS-ask : ∀ {P Q R Q' R' q A} →

        (Σ Q' λ q' →  R' q' → Server' Q' R' P ⊢[ Q , R , q ] A)
    → ----------------------------------------------------------
                   Server' Q' R' P ⊢[ Q , R , q ] A

  LS-done : ∀ {P Q R Q' R' q A} →

             P ⊢[ Q , R , q ] A
    → -------------------------
        Server' Q' R' P ⊢[ Q , R , q ] A

  LΠ : ∀ {A B Q R q P} →

       (Σ A λ x → B x ⊢[ Q , R , q ] P)
    → ----------------------------------
         Π' A B ⊢[ Q , R , q ] P

  LΣ : ∀ {A B Q R q P} →

       (Π A λ x → B x ⊢[ Q , R , q ] P)
    → ----------------------------------
         Σ' A B ⊢[ Q , R , q ] P

  LC : ∀ {A B Q Q' R R' q} →

        Client[ Q' , R' , B ]⊢[ Q , R , q ] A
    → -----------------------------------
        Client' Q' R' B ⊢[ Q , R , q ] A

data _[_,_,_]⊢_ : Proto → (Q : ★)(R : Q → ★) → Q → Proto → ★₁ where
  ret : ∀ {P Q R q A} →

      (Σ (R q) λ _ → LServerSim P Q R A)
    → -----------------------------------
          P [ Q , R , q ]⊢ A

  RC-ask : ∀ {P Q R Q' R' q A} →

        (Σ Q' λ q' → R' q' → P [ Q , R , q ]⊢ Client' Q' R' A)
    → ----------------------------------------------------------
              P [ Q , R , q ]⊢ Client' Q' R' A

  RC-done : ∀ {P Q R Q' R' q A} →

             P [ Q , R , q ]⊢ A
    → -------------------------
        P [ Q , R , q ]⊢ Client' Q' R' A

  RΣ : ∀ {A B Q R q P} →

       (Σ A λ x → P [ Q , R , q ]⊢ B x)
    → ----------------------------------
         P [ Q , R , q ]⊢ Σ' A B

  RΠ : ∀ {A B Q R q P} →

       (Π A λ x → P [ Q , R , q ]⊢ B x)
    → ----------------------------------
         P [ Q , R , q ]⊢ Π' A B

  RS : ∀ {A B Q Q' R R' q} →

        A [ Q , R , q ]⊢Server[ Q' , R' , B ]
    → ----------------------------------------
        A [ Q , R , q ]⊢ Server' Q' R' B

record RServerSim (P : Proto)(Q : ★)(R : Q → ★)(A : Proto) where
  coinductive
  field
    r-done : P ⊢ A
    r-ask  : Π Q λ q? → P ⊢[ Q , R , q? ] A

record LServerSim (P : Proto)(Q : ★)(R : Q → ★)(A : Proto) where
  coinductive
  field
    l-done : P ⊢ A
    l-ask  : Π Q λ q? → P [ Q , R , q? ]⊢ A

record _[_,_,_]⊢Server[_,_,_] A Q R q Q' R' B where
  coinductive
  field
    [r]-done : A [ Q , R , q ]⊢ B
    [r]-ask  : Π Q' λ q' → R' q' × A [ Q , R , q ]⊢Server[ Q' , R' , B ]

record Client[_,_,_]⊢[_,_,_]_ Q R A Q' R' q' B where
  coinductive
  field
    [l]-done : A ⊢[ Q' , R' , q' ] B
    [l]-ask  : Π Q λ q → R q × Client[ Q , R , A ]⊢[ Q' , R' , q' ] B

open LServerSim public
open RServerSim public
open _[_,_,_]⊢Server[_,_,_] public
open Client[_,_,_]⊢[_,_,_]_ public


-- {-
inv : ∀ {P Q} → P ⊢ Q → dual Q ⊢ dual P

invRS : ∀ {P Q R A} → RServerSim P Q R A → LServerSim (dual A) Q R (dual P)
invLS : ∀ {P Q R A} → LServerSim P Q R A → RServerSim (dual A) Q R (dual P)

invL : ∀ {P Q R q A} → P ⊢[ Q , R , q ] A → dual A [ Q , R , q ]⊢ dual P
invR : ∀ {P Q R q A} → P [ Q , R , q ]⊢ A → dual A ⊢[ Q , R , q ] dual P

invLC : ∀ {A B Q Q' R R' q} → Client[ Q' , R' , B ]⊢[ Q , R , q ] A
      → dual A [ Q , R , q ]⊢Server[ Q' , R' , dual B ]

invRC : ∀ {P Q R q B Q' R'} →
    P [ Q , R , q ]⊢Server[ Q' , R' , B ] →
    Client[ Q' , R' , dual B ]⊢[ Q , R , q ] dual P


inv end = end
inv (LΣ f) = RΠ (λ x → inv (f x))
inv (RΣ (x , p)) = LΠ (x , inv p)
inv (LΠ (x , p)) = RΣ (x , inv p)
inv (RΠ f) = LΣ (λ x → inv (f x))
inv (RC-done s) = LS-done (inv s)
inv (RC-ask (q , cont)) = LS-ask (q , λ x → inv (cont x))
inv (LS-done s) = RC-done (inv s)
inv (LS-ask (q , cont)) = RC-ask (q , λ x → inv (cont x))
inv (RS sim) = LC (invRS sim)
inv (LC sim) = RS (invLS sim)

l-done (invRS sim) = inv (r-done sim)
l-ask (invRS sim) q? = invL (r-ask sim q?)

r-done (invLS sim) = inv (l-done sim)
r-ask (invLS sim) q? = invR (l-ask sim q?)

invL (ret (r , s)) = ret (r , invRS s)
invL (LS-ask (q , c)) = RC-ask (q , λ r → invL (c r))
invL (LS-done s)      = RC-done (invL s)
invL (LΠ (x , c))  = RΣ (x , invL c)
invL (LΣ f)  = RΠ λ x → invL (f x)
invL (LC s)  = RS (invLC s)

invR (ret (r , s)) = ret (r , invLS s)
invR (RC-ask (q , c)) = LS-ask (q , λ r → invR (c r))
invR (RC-done s)      = LS-done (invR s)
invR (RΣ (x , c))  = LΠ (x , invR c)
invR (RΠ f)       = LΣ λ x → invR (f x)
invR (RS s)       = LC (invRC s)

[r]-done (invLC s) = invL ([l]-done s)
[r]-ask  (invLC s) q = let r , s' = [l]-ask s q in r , invLC s'

[l]-done (invRC s)  = invR ([r]-done s)
[l]-ask (invRC s) q = let r , s' = [r]-ask s q in r , invRC s'

-- record { [r]-done = {!!} ; [r]-ask = {!!} }
-- -}

applySim : ∀ {A P Q R X} → RServerSim P Q R A → El X P → Server Q R (El X A)
applySimResp : ∀ {P Q R X A q} → P ⊢[ Q , R , q ] A → El X P → ServerResponse Q R (El X A) q
applySimRespServe : ∀ {P Q R Q' R' X A q} → Client[ Q' , R' , P ]⊢[ Q , R , q ] A → Client Q' R' (El X P) → ServerResponse Q R (El X A) q

applyClient : ∀ {P Q R A X} → LServerSim P Q R A → Client Q R (El X P) → El X A
applyClientResp : ∀ {P Q R X A q} → P [ Q , R , q ]⊢ A → (R q → Client Q R (El X P)) → El X A

apply : ∀ {A P Q} → P ⊢ Q → El A P → El A Q

apply end               p       = p
apply (LΣ f)            (x , p) = apply (f x) p
apply (RΣ (x , f))      p       = x , apply f p
apply (LΠ (x , f))      p       = apply f (p x)
apply (RΠ f)            p x     = apply (f x) p
apply (RC-done p)       x       = done (apply p x)
apply (RC-ask (q? , c)) p       = ask q? (λ x → apply (c x) p)
apply (LS-done p)       x       = apply p (srv-done x)
apply (LS-ask (q? , c)) p       = let r = srv-ask p q? in apply (c (srv-resp r)) (srv-cont r)
apply (RS serversim)    p       = applySim serversim p
apply (LC serversim)    c       = applyClient serversim c

applyClient sim (ask q? cont) = applyClientResp (l-ask sim q?) cont
applyClient sim (done x) = apply (l-done sim) x

applyClientResp (ret (r , s)) cont = applyClient s (cont r)
applyClientResp (RC-ask (q , c)) cont = ask q (λ r → applyClientResp (c r) cont)
applyClientResp (RC-done s)      cont = done (applyClientResp s cont)
applyClientResp (RΣ (x , c))  cont = x , applyClientResp c cont
applyClientResp (RΠ f)        cont x = applyClientResp (f x) cont
srv-done (applyClientResp (RS s) cont)   = applyClientResp ([r]-done s) cont
srv-resp (srv-ask  (applyClientResp (RS s) cont) q) = proj₁ ([r]-ask s q)
srv-cont (srv-ask  (applyClientResp (RS s) cont) q) = applyClientResp (RS (proj₂ ([r]-ask s q))) cont

srv-done (applySim sim process) = apply (r-done sim) process
srv-ask (applySim sim process) q? = applySimResp (r-ask sim q?) process

srv-cont (applySimResp (ret (r , s)) process) = applySim s process
srv-resp (applySimResp (ret (r , s)) process) = r
applySimResp (LΠ (x , c)) process = applySimResp c (process x)
applySimResp (LΣ f) (x , process) = applySimResp (f x) process
applySimResp (LS-done s) process = applySimResp s (srv-done process)
applySimResp (LS-ask (q , c)) process = let r = srv-ask process q in applySimResp (c (srv-resp r)) (srv-cont r)
applySimResp (LC s) process = applySimRespServe s process

applySimRespServe s (ask q? cont) = let r , s' = [l]-ask s q? in applySimRespServe s' (cont r)
applySimRespServe s (done x) = applySimResp ([l]-done s) x

module Proof (X Y : ★) where
  open import Relation.Binary.PropositionalEquality.NP

  proof : {P Q : Proto}{c : El X P}{a : El Y (dual Q)}(sim : P ⊢ Q)
        → com P c (apply (inv sim) a) ≡ com Q (apply sim c) a

  proofRS : ∀ {P A Q R}{c : El X P}(a : Client Q R (El Y (dual A)))(sim : RServerSim P Q R A)
          → com P c (applyClient (invRS sim) a)
          ≡ let (c' , a') = Server-Com (applySim sim c) a
             in com A c' a'
  proofRS-Resp : ∀ {P Q R q A}{c : El X P}(cont : R q → Client Q R (El Y (dual A)))(der : P ⊢[ Q , R , q ] A)
               →
               com P c (applyClientResp (invL der) cont)
               ≡ let (c' , a') = Server-Com (srv-cont (applySimResp der c))
                                            (cont (srv-resp (applySimResp der c)))
                  in com A c' a'

  proofLS : ∀ {P A Q R}{a : El Y (dual A)}(c : Client Q R (El X P))(sim : LServerSim P Q R A)
          → let (c' , a') = Server-Com (applySim (invLS sim) a) c
             in com P a' c' ≡ com A (applyClient sim c) a

  proofLS-Resp : ∀ {P Q R q A}{a : El Y (dual A)}(cont : R q → Client Q R (El X P))(der : P [ Q , R , q ]⊢ A)
               →
               let (c' , a') = Server-Com (srv-cont (applySimResp (invR der) a))
                                          (cont (srv-resp (applySimResp (invR der) a)))
                in com P a' c' ≡ com A (applyClientResp der cont) a

  proofRS-Resp* : ∀ {A B Q Q' R R' q}(c : Client Q' R' (El X B))(cont : R q → Client Q R (El Y (dual A)))(s : Client[ Q' , R' , B ]⊢[ Q , R , q ] A) →
    let (b2 , b1) = Server-Com (applyClientResp (RS (invLC s)) cont) c
        (a1 , a2) = Server-Com (srv-cont (applySimRespServe s c))
                               (cont (srv-resp (applySimRespServe s c)))
     in com B b1 b2 ≡ com A a1 a2

  proofLS-Resp* : ∀ {A B Q Q' R R' q}(a : Client Q' R' (El Y (dual B)))
    (cont : R q → Client Q R (El X A))(s : A [ Q , R , q ]⊢Server[ Q' , R' , B ])
    → let (a2 , a1) = Server-Com (srv-cont (applySimRespServe (invRC s) a))
                                 (cont (srv-resp (applySimRespServe (invRC s) a)))
          (b1 , b2) = Server-Com (applyClientResp (RS s) cont) a
      in com A a1 a2 ≡ com B b1 b2

  proof         end               = refl
  proof         (LΣ f)            = proof (f _)
  proof         (RΣ (x , p))      = proof p
  proof         (LΠ (x , p))      = proof p
  proof         (RΠ f)            = proof (f _)
  proof         (RC-done sim)     = proof sim
  proof         (LS-done sim)     = proof sim
  proof {a = a} (RC-ask (q? , x)) = proof (x (srv-resp (srv-ask a q?)))
  proof {c = c} (LS-ask (q? , x)) = proof (x (srv-resp (srv-ask c q?)))
  proof {a = a} (RS sim)          = proofRS a sim
  proof {c = c} (LC sim)          = proofLS c sim

  proofRS (ask q? cont) sim = proofRS-Resp cont (r-ask sim q?)
  proofRS (done x) sim = proof (r-done sim)

  proofLS (ask q? cont) sim = proofLS-Resp cont (l-ask sim q?)
  proofLS (done x) sim = proof (l-done sim)

  proofRS-Resp cont (ret (r , s)) = proofRS (cont r) s
  proofRS-Resp cont (LS-ask (q , c)) = proofRS-Resp cont (c _)
  proofRS-Resp cont (LS-done s)      = proofRS-Resp cont s
  proofRS-Resp cont (LΠ (x , c))  = proofRS-Resp cont c
  proofRS-Resp cont (LΣ f)        = proofRS-Resp cont (f _)
  proofRS-Resp {c = c} cont (LC s)        = proofRS-Resp* c cont s

  proofLS-Resp cont (ret (r , s)) = proofLS (cont r) s
  proofLS-Resp cont (RC-ask (q , c)) = proofLS-Resp cont (c _)
  proofLS-Resp cont (RC-done s)      = proofLS-Resp cont s
  proofLS-Resp cont (RΣ (x , c))  = proofLS-Resp cont c
  proofLS-Resp cont (RΠ f) = proofLS-Resp cont (f _)
  proofLS-Resp {a = a} cont (RS s) = proofLS-Resp* a cont s

  proofRS-Resp* (ask q? cont) cont₁ s = let (r , s') = [l]-ask s q?
    in proofRS-Resp* (cont r) cont₁ s'
  proofRS-Resp* (done x) cont s = proofRS-Resp cont ([l]-done s)

  proofLS-Resp* (ask q? cont) kont s = let (r , s') = [r]-ask s q?
    in proofLS-Resp* (cont r) kont s'
  proofLS-Resp* (done x) kont s = proofLS-Resp kont ([r]-done s)

-- -}
-- -}
-- -}
-- -}
-- -}
