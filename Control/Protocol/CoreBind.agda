-- {-# OPTIONS --without-K #-}
open import Coinduction
open import Function.NP
open import Type
open import Level
open import Data.Product
open import Data.One
open import Data.Two

open import Relation.Binary.PropositionalEquality

module Control.Protocol.CoreBind where
open import Control.Strategy renaming (Strategy to Client) public

{-
data Inf : ★ where
  mu nu : Inf
-}

data Proto : ★₁ where
  end : Proto
  Π' Σ' : (A : ★)(B : A → Proto) → Proto
  -- mu nu : ∞ Proto → Proto

Tele : Proto → ★
Tele end = 𝟙
Tele (Π' A B) = Σ A λ x → Tele (B x)
Tele (Σ' A B) = Σ A λ x → Tele (B x)
-- Tele (later i P) = ?

_>>≡_ : (P : Proto) → (Tele P → Proto) → Proto
end >>≡ Q = Q _
Π' A B >>≡ Q = Π' A (λ x → B x >>≡ (λ xs → Q (x , xs)))
Σ' A B >>≡ Q = Σ' A (λ x → B x >>≡ (λ xs → Q (x , xs)))
-- later i P >>≡ Q = ?

++Tele : ∀ (P : Proto)(Q : Tele P → Proto) → (x : Tele P) → Tele (Q x) → Tele (P >>≡ Q)
++Tele end Q x y = y
++Tele (Π' M C) Q (m , x) y = m , ++Tele (C m) (λ x₁ → Q (m , x₁)) x y
++Tele (Σ' M C) Q (m , x) y = m , ++Tele (C m) _ x y
-- ++Tele (later i P) Q x y = ?

module _ (funExt : ∀ {a}{b}{A : ★_ a}{B : ★_ b}{f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g) where
  right-unit : ∀ (P : Proto) → (P >>≡ λ x → end) ≡ P
  right-unit end = refl
  right-unit (Π' M C) = let p = funExt (λ x → right-unit (C x)) in cong (Π' M) p
  right-unit (Σ' M C) = cong (Σ' M) (funExt (λ x → right-unit (C x)))
  -- right-unit (later i P) = ?

  assoc : ∀ (P : Proto)(Q : Tele P → Proto)(R : Tele (P >>≡ Q) → Proto)
        → P >>≡ (λ x → Q x >>≡ (λ y → R (++Tele P Q x y))) ≡ ((P >>≡ Q) >>≡ R)
  assoc end Q R = refl
  assoc (Π' M C₁) Q R = cong (Π' M) (funExt (λ x → assoc (C₁ x) (λ xs → Q (x , xs)) (λ xs → R (x , xs))))
  assoc (Σ' M C₁) Q R = cong (Σ' M) (funExt (λ x → assoc (C₁ x) (λ xs → Q (x , xs)) (λ xs → R (x , xs))))
  -- assoc (later i P) Q R = ?

_>>_ : Proto → Proto → Proto
P >> Q = P >>≡ λ _ → Q

_×'_ : Set → Proto → Proto
A ×' B = Σ' A λ _ → B

_→'_ : Set → Proto → Proto
A →' B = Π' A λ _ → B

{-
dualInf : Inf → Inf
dualInf mu = nu
dualInf nu = mu
-}

dual : Proto → Proto
dual end = end
dual (Π' A B) = Σ' A (λ x → dual (B x))
dual (Σ' A B) = Π' A (λ x → dual (B x))
-- dual (mu P) = nu (♯ (dual (♭ P)))
-- dual (nu P) = mu (♯ (dual (♭ P)))

{-
module _ (funExt : ∀ {a b}{A : ★_ a}{B : A → ★_ b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g)where
  dual-Tele : ∀ P → Tele P ≡ Tele (dual P)
  dual-Tele end = refl
  dual-Tele (Π' A B) = cong (Σ A) (funExt (λ x → dual-Tele (B x)))
  dual-Tele (Σ' A B) = cong (Σ A) (funExt (λ x → dual-Tele (B x)))
  dual-Tele (later i P) = ?
-}{-
module _ X where
  El : Proto → ★
  El end = X
  El (Π' A B) = Π A λ x → El (B x)
  El (Σ' A B) = Σ A λ x → El (B x)
module _ where
  El : (P : Proto) → (Tele P → ★) → ★
  El end X = X _
  El (Π' A B) X = Π A λ x → El (B x) (λ y → X (x , y))
  El (Σ' A B) X = Σ A λ x → El (B x) (λ y → X (x , y))
  El (later i P) = ?

module ElBind (funExt : ∀ {a b}{A : ★_ a}{B : A → ★_ b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g)where

  bind-spec : (P : Proto)(Q : Tele P → Proto)(X : Tele (P >>≡ Q) → ★) → El (P >>≡ Q) X ≡ El P (λ x → El (Q x) (λ y → X (++Tele P Q x y)))
  bind-spec end Q X = refl
  bind-spec (Π' A B) Q X = cong (Π A) (funExt (λ x → bind-spec (B x) (λ xs → Q (x , xs)) (λ y → X (x , y))))
  bind-spec (Σ' A B) Q X = cong (Σ A) (funExt (λ x → bind-spec (B x) _ _))
  bind-spec (later i p) Q X = ?


module _ {A B} where
  com : (P : Proto) → El P (const A) → El (dual P) (const B) → A × B
  com end a b = a , b
  com (Π' A B) f (x , y) = com (B x) (f x) y
  com (Σ' A B) (x , y) f = com (B x) y (f x)
  com (later i P) x y = ?

module _ (funExt : ∀ {a b}{A : ★_ a}{B : A → ★_ b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g)where
  com-cont : (P : Proto){A : Tele P → ★}{B : Tele (dual P) → ★} → El P A → El (dual P) B → Σ (Tele P) A × Σ (Tele (dual P)) B
  com-cont end p q = (_ , p)  , (_ , q)
  com-cont (Π' A B) p (m , q) with com-cont (B m) (p m) q
  ... | (X , a) , (Y , b) = ((m , X) , a) , (m , Y) , b
  com-cont (Σ' A B) (m , p) q with com-cont (B m) p (q m)
  ... | (X , a) , (Y , b) = ((m , X) , a) , (m , Y) , b
  com-cont (later i P) p q = ?
-}
{-
data Process (A : ★): Proto → ★₁ where
  send : ∀ {M P} (m : M) → Process A (P m) → Process A (Σ' M P)
  recv : ∀ {M P} → ((m : M) → Process A (P m)) → Process A (Π' M P)
  end  : A → Process A end
  -}

data ProcessF (this : Proto → ★₁): Proto → ★₁ where
  send : ∀ {M P} (m : M) → this (P m) → ProcessF this (Σ' M P)
  recv : ∀ {M P} → ((m : M) → this (P m)) → ProcessF this (Π' M P)
  -- mu   : ∀ {P} → this (♭ P) → ProcessF this (mu P)
  -- nu   : ∀ {P} → ∞ (this (♭ P)) → ProcessF this (nu P)

data Process (A : ★) : Proto → ★₁ where
  do  : ∀ {P} → ProcessF (Process A) P → Process A P
  end : A → Process A end

data Proc : Proto → ★₁ where
  do  : ∀ {P} → ProcessF Proc P → Proc P
  end : Proc end

proc : ∀ {A P} → Process A P → Proc (P >> (A ×' end))
proc (do (send m x)) = do (send m (proc x))
proc (do (recv x)) = do (recv (λ m → proc (x m)))
proc (end x) = do (send x end)

process : ∀ {A P} → Proc (P >> (A ×' end)) → Process A P
process {P = end} (do (send m _)) = end m
process {P = Π' A₁ B} (do (recv x)) = do (recv (λ m → process (x m)))
process {P = Σ' A₁ B} (do (send m p)) = do (send m (process p))

data Sim : Proto → Proto → ★₁ where
  left  : ∀ {P Q} → ProcessF (flip Sim Q) P → Sim P Q
  right : ∀ {P Q} → ProcessF (Sim P) Q → Sim P Q
  end   : Sim end end

SimL : Proto → Proto → ★₁
SimL P Q = ProcessF (flip Sim Q) P

SimR : Proto → Proto → ★₁
SimR P Q = ProcessF (Sim P) Q

sendR : ∀ {M P Q} (m : M) → Sim P (Q m) → Sim P (Σ' M Q)
sendR m = right ∘ send m

sendL : ∀ {M P Q} (m : M) → Sim (P m) Q → Sim (Σ' M P) Q
sendL m = left ∘ send m

recvR : ∀ {M P Q} → ((m : M) → Sim P (Q m)) → Sim P (Π' M Q)
recvR = right ∘ recv

recvL : ∀ {M P Q} → ((m : M) → Sim (P m) Q) → Sim (Π' M P) Q
recvL = left ∘ recv

_⟹_ : Proto → Proto → ★₁
P ⟹ Q = Sim (dual P) Q

_⟹ᴾ_ : Proto → Proto → ★₁
P ⟹ᴾ Q = ∀ {A} → Process A (dual P) → Process A Q

sim-id : ∀ P → Sim (dual P) P
sim-id end = end
sim-id (Π' A B) = recvR (λ m → sendL m (sim-id (B m)))
sim-id (Σ' A B) = recvL (λ m → sendR m (sim-id (B m)))
--sim-id (mu P) = right (mu (left (nu (♯ sim-id (♭ P)))))
--sim-id (nu P) = left (mu (right (nu (♯ (sim-id (♭ P))))))

sim-id! : ∀ P → Sim P (dual P)
sim-id! end = end
sim-id! (Π' A B) = recvL (λ m → sendR m (sim-id! (B m)))
sim-id! (Σ' A B) = recvR (λ m → sendL m (sim-id! (B m)))

sim-comp : ∀ {P Q R} → Sim P Q → Sim (dual Q) R → Sim P R
sim-compL : ∀ {P Q R} → SimL P Q → Sim (dual Q) R → SimL P R
sim-compR : ∀ {P Q R} → Sim P Q → SimR (dual Q) R → SimR P R
-- sim-compRL : ∀ {P Q R} → SimR P Q → SimL (dual Q) R → Sim P R

sim-comp (right (send m PQ)) (left (recv QR)) = sim-comp PQ (QR m)
sim-comp (right (recv PQ))   (left (send m QR)) = sim-comp (PQ m) QR
-- sim-comp (right (mu x)) (left (nu x₁)) = sim-comp x (♭ x₁)
-- sim-comp (right (nu x)) (left (mu x₁)) = sim-comp (♭ x) x₁
sim-comp end QR = QR
sim-comp (left PQ)  QR = left (sim-compL PQ QR)
sim-comp (right PQ) (right QR) = right (sim-compR (right PQ) QR)

{-
sim-compRL (send m PQ) (recv QR)   = sim-comp PQ (QR m)
sim-compRL (recv PQ)   (send m QR) = sim-comp (PQ m) QR
-}

sim-compL (send m PQ) QR = send m (sim-comp PQ QR)
sim-compL (recv PQ)   QR = recv (λ m → sim-comp (PQ m) QR)
-- sim-compL (mu PQ) QR = mu (sim-comp PQ QR)
-- sim-compL (nu PQ) QR = nu (♯ sim-comp (♭ PQ) QR)

sim-compR PQ (send m QR) = send m (sim-comp PQ QR)
sim-compR PQ (recv QR)   = recv (λ m → sim-comp PQ (QR m))
-- sim-comp PQ (mu QR) = mu (sim-comp PQ QR)
-- sim-comp PQ (nu QR) = nu (♯ sim-comp PQ (♭ QR))

-- sim-comp (sendR m ?) (sendR m' ?)

_♦_ : ∀ {P Q R} → Sim P Q → Sim (dual Q) R → Sim P R
_♦_ = sim-comp

♦-end-L : ∀ {P Q} → Sim P end → Sim end Q → Sim P Q
♦-end-L (left (send m PE)) EQ = sendL m (♦-end-L PE EQ)
♦-end-L (left (recv   PE)) EQ = recvL (λ m → ♦-end-L (PE m) EQ)
♦-end-L end                EQ = EQ
♦-end-L (right ()) _

♦-end-R : ∀ {P Q} → Sim P end → Sim end Q → Sim P Q
♦-end-R PE (right (send m EQ)) = sendR m (♦-end-R PE EQ)
♦-end-R PE (right (recv   EQ)) = recvR λ m → ♦-end-R PE (EQ m)
♦-end-R PE end                 = PE
♦-end-R _  (left ())

testL : ♦-end-L {𝟚 ×' end} {𝟚 ×' end} (sendL 0₂ end) (sendR 1₂ end)
      ≢ ♦-end-R {𝟚 ×' end} {𝟚 ×' end} (sendL 0₂ end) (sendR 1₂ end)
testL ()

{-

!ˢ : ∀ {P Q} → Sim P Q → Sim Q P
!ˢ (left (send m x)) = sendR m (!ˢ x)
!ˢ (left (recv x)) = recvR (λ m → !ˢ (x m))
!ˢ (right (send m x)) = sendL m (!ˢ x)
!ˢ (right (recv x)) = recvL (λ m → !ˢ (x m))
!ˢ end = end

module _ (funExt : ∀ {a}{b}{A : ★_ a}{B : A → ★_ b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g) where
    !!ˢ :
      ∀ {P Q}
        (PQ : Sim P Q)
      → !ˢ (!ˢ PQ) ≡ PQ
    !!ˢ (left (send m x)) = cong (sendL m) (!!ˢ x)
    !!ˢ (left (recv x)) = cong recvL (funExt λ m → !!ˢ (x m))
    !!ˢ (right (send m x)) = cong (sendR m) (!!ˢ x)
    !!ˢ (right (recv x)) = cong recvR (funExt λ m → !!ˢ (x m))
    !!ˢ end = refl

    sim-comp-end : ∀ {P} (PE : Sim P end) → sim-comp PE end ≡ PE
    sim-comp-end (left (send m PE)) = cong (sendL m) (sim-comp-end PE)
    sim-comp-end (left (recv PE)) = cong recvL (funExt (λ x → sim-comp-end (PE x)))
    sim-comp-end (right ())
    sim-comp-end end = refl

    sim-comp-end' : ∀ {P Q} (PE : Sim P end) (EQ : Sim end Q) → sim-comp PE EQ ≡ {!!}
    sim-comp-end' PE EQ = {!!}

    sim-comp-left :
      ∀ {P Q R}
        (PQ : SimL P Q)
        (QR : Sim (dual Q) R)
      → sim-comp (left PQ) QR ≡ left (sim-compL PQ QR)
    sim-comp-left PQ QR = refl

    sim-comp-right :
      ∀ {P Q R}
        (PQ : SimR P Q)
        (QR : SimR (dual Q) R)
      → sim-comp (right PQ) (right QR) ≡ right (sim-compR (right PQ) QR)
    sim-comp-right (send m x) QR = refl
    sim-comp-right (recv x) QR = refl

    sim-comp-assoc :
      ∀ {P Q R S}
        (PQ : Sim P Q)
        (QR : Sim (dual Q) R)
        (RS : Sim (dual R) S)
      → sim-comp (sim-comp PQ QR) RS ≡ sim-comp PQ (sim-comp QR RS)
    sim-comp-assoc (left (send m PQ)) QR RS = cong (sendL m) (sim-comp-assoc PQ QR RS)
    sim-comp-assoc (left (recv PQ)) QR RS = cong recvL (funExt (λ m → sim-comp-assoc (PQ m) QR RS))
    sim-comp-assoc (right (send m PQ)) (left (recv QR)) RS = sim-comp-assoc PQ (QR m) RS
    sim-comp-assoc (right (send m PQ)) (right (send m₁ QR)) RS = {!!}
    sim-comp-assoc (right (send m PQ)) (right (recv QR)) (left (send m₁ RS)) with QR m₁
    sim-comp-assoc (right (send m PQ)) (right (recv _ )) (left (send m₁ RS)) | left (recv QR) = sim-comp-assoc PQ (QR m) RS
    sim-comp-assoc (right (send m PQ)) (right (recv _ )) (left (send m₁ RS)) | right QR = {!!}
    sim-comp-assoc (right (send m PQ)) (right (recv QR)) (right (send m₁ RS))
      = {!sim-comp-assoc (sendR m PQ) (QR ?) ?!}
    sim-comp-assoc (right (send m PQ)) (right (recv x)) (right (recv x₁)) = {!!}
    sim-comp-assoc (right (recv PQ)) QR RS = {!!}
    sim-comp-assoc end QR RS = refl

⟹-comp : ∀ {P Q R} → P ⟹ Q → Q ⟹ R → P ⟹ R
⟹-comp = sim-comp

sim-unit : ∀ {P} → Sim end P → Process 𝟙 P
sim-unit (left ())
sim-unit (right (send m x)) = do (send m (sim-unit x))
sim-unit (right (recv x)) = do (recv (λ m → sim-unit (x m)))
sim-unit end = end 0₁

sim→proc : ∀ {P} → Sim end P → Proc P
sim→proc (left ())
sim→proc (right (send m x)) = do (send m (sim→proc x))
sim→proc (right (recv x)) = do (recv (λ m → sim→proc (x m)))
sim→proc end = end

unit-sim : ∀ {P} → Process 𝟙 P → Sim end P
unit-sim (do (send m x)) = right (send m (unit-sim x))
unit-sim (do (recv x)) = right (recv (λ m → unit-sim (x m)))
unit-sim (end x) = end

proc→sim : ∀ {P} → Proc P → Sim end P
proc→sim (do (send m x)) = right (send m (proc→sim x))
proc→sim (do (recv x)) = right (recv (λ m → proc→sim (x m)))
proc→sim end = end

⟹-dual : ∀ {P Q} → P ⟹ dual Q → Q ⟹ dual P
⟹-dual = !ˢ

{-
toEl : ∀ {P A} → Process A P → El P (const A)
toEl (end x) = x
toEl (do (recv f)) = λ x → toEl (f x)
toEl (do (send m x)) = m , toEl x
-}

idP : ∀ {A} → Process A (Π' A (const end))
idP = do (recv end)

dual² : ∀ {P A} → Process A P → Process A (dual (dual P))
dual² (end x) = end x
dual² (do (recv x)) = do (recv (λ m → dual² (x m)))
dual² (do (send m x)) = do (send m (dual² x))

apply-sim0 : ∀ {P Q} → P ⟹ Q → Proc P → Proc Q
apply-sim0 PQ P = sim→proc (sim-comp (proc→sim P) PQ)

apply-sim1 : ∀ {P Q} → Sim P Q → Proc (dual Q) → Proc P
apply-sim1 PQ Q = sim→proc (!ˢ (sim-comp PQ (!ˢ (proc→sim Q))))

apply-sim2 : ∀ {P Q} → Sim P Q → Proc (dual P) → Proc Q
apply-sim2 PQ P = apply-sim1 (!ˢ PQ) P

apply-sim : ∀ {P Q} → Sim P Q → P ⟹ᴾ Q
apply-sim (left (send m x)) (do (recv x₁)) = apply-sim x (x₁ m)
apply-sim (left (recv x)) (do (send m x₁)) = apply-sim (x m) x₁
apply-sim (right (send m x)) P₂ = do (send m (apply-sim x P₂))
apply-sim (right (recv x)) P₂ = do (recv (λ m → apply-sim (x m) P₂))
apply-sim end P = P

apply-sim' : ∀ {P Q} → Sim P Q → Q ⟹ᴾ P -- ∀ {A} → Process A Q → Process A (dual P)
apply-sim' PQ P = apply-sim (!ˢ PQ) P

apply : ∀ {P Q A} → P ⟹ Q → Process A P → Process A Q
apply PQ P = apply-sim PQ (dual² P)

module _ (funExt : ∀ {a}{b}{A : ★_ a}{B : A → ★_ b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g) where
{-
  apply-comp : ∀ {P Q R A}(PQ : Sim P Q)(QR : Sim (dual Q) R)(p : Process A (dual P)) → apply-sim (sim-comp PQ QR) p ≡ apply QR (apply-sim PQ p)
  apply-comp (left (send m x)) QR (do (recv x₁)) = apply-comp x QR (x₁ m)
  apply-comp (left (recv x)) QR (do (send m x₁)) = apply-comp (x m) QR x₁
  apply-comp (right (send m x)) (left (recv x₁)) p = apply-comp x (x₁ m) p
  apply-comp (right (send m x)) (right (recv x₁)) p = cong (λ X → do (recv X))
    (funExt (λ m' → apply-comp (right (send m x)) (x₁ m') p))
  apply-comp (right (send m x)) (right (send m₁ x₁)) p
    rewrite apply-comp (right (send m x)) x₁ p = refl
  apply-comp (right (recv x)) (left (send m x₁)) p = apply-comp (x m) x₁ p
  apply-comp (right (recv x)) (right (send m x₁)) p
    rewrite apply-comp (right (recv x)) x₁ p = refl
  apply-comp (right (recv x)) (right (recv x₁)) p = cong (λ X → do (recv X))
    (funExt (λ m → apply-comp (right (recv x)) (x₁ m) p))
  apply-comp end QR (do ())
  apply-comp end QR (end x) = refl
  -}

  apply-comp : ∀ {P Q R}(EP : Sim end P)(PQ : Sim (dual P) Q)(QR : Sim (dual Q) R)
               → sim-comp EP (sim-comp PQ QR) ≡ sim-comp (sim-comp EP PQ) QR
  apply-comp (left ()) PQ QR
  apply-comp (right (send m EP)) (left (recv PQ)) QR = apply-comp EP (PQ m) QR
  apply-comp (right (send m EP)) (right (send m₁ x)) QR = {!apply-comp!}
  apply-comp (right (send m EP)) (right (recv x)) QR = {!!}
  apply-comp (right (recv x)) PQ QR = {!!}
  apply-comp end PQ QR = refl

               {-
  apply-comp (left (send m x)) QR (do (recv x₁)) = apply-comp x QR (x₁ m)
  apply-comp (left (recv x)) QR (do (send m x₁)) = apply-comp (x m) QR x₁
  apply-comp (right (send m x)) (left (recv x₁)) p = apply-comp x (x₁ m) p
  apply-comp (right (send m x)) (right (recv x₁)) p = cong (λ X → do (recv X))
    (funExt (λ m' → apply-comp (right (send m x)) (x₁ m') p))
  apply-comp (right (send m x)) (right (send m₁ x₁)) p
    rewrite apply-comp (right (send m x)) x₁ p = refl
  apply-comp (right (recv x)) (left (send m x₁)) p = apply-comp (x m) x₁ p
  apply-comp (right (recv x)) (right (send m x₁)) p
    rewrite apply-comp (right (recv x)) x₁ p = refl
  apply-comp (right (recv x)) (right (recv x₁)) p = cong (λ X → do (recv X))
    (funExt (λ m → apply-comp (right (recv x)) (x₁ m) p))
  apply-comp end QR (do ())
  apply-comp end QR (end x) = refl

{-
_>>=P_ : ∀ {A B P}{Q : Tele P → Proto} → Process A P → ((p : Tele P) → A → Process B (Q p)) → Process B (P >>≡ Q)
send m p >>=P k = send m (p >>=P (λ p₁ → k (m , p₁)))
recv x >>=P k = recv (λ m → x m >>=P (λ p → k (m , p)))
end x >>=P k = k 0₁ x


  {-
module _ where
  bind-com : (P : Proto)(Q : Tele P → Proto)(R : Tele (dual P) → Proto)
    (X : Tele (P >>≡ Q) → ★)(Y : Tele (dual P >>≡ R) → ★)
    → El (P >>≡ Q) X → El (dual P >>≡ R) Y → ? × ?
-- -}
-- -}
-- -}
-- -}
-- -}
