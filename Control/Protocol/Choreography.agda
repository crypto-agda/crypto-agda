
-- {-# OPTIONS --without-K #-}
open import Coinduction
open import Function.NP
open import Type
open import Level.NP
open import Data.Product
open import Data.One

open import Relation.Binary.PropositionalEquality.NP

module Control.Protocol.Choreography where

Π· : ∀ {a b}(A : ★_ a) → (B : ..(_ : A) → ★_ b) → ★_ (a ⊔ b)
Π· A B = ..(x : A) → B x

data ☐ {a}(A : ★_ a) : ★_ a where
  [_] : ..(x : A) → ☐ A

un☐ : ∀ {a b}{A : ★_ a}{B : ☐ A → ★_ b} → (..(x : A) → B [ x ]) → Π (☐ A) B
un☐ f [ x ] = f x

map☐ : ∀ {a b}{A : ★_ a}{B : ★_ b} → (..(x : A) → B) → ☐ A → ☐ B
map☐ f [ x ] = [ f x ]

data InOut : ★ where
  In Out : InOut

dualInOut : InOut → InOut
dualInOut In  = Out
dualInOut Out = In

data Proto : ★₁ where
  end : Proto
  com  : (q : InOut)(M : ★)(P : M → Proto) → Proto

infix 0 _≡ᴾ_
data _≡ᴾ_ : Proto → Proto → ★₁ where
  end : end ≡ᴾ end
  com : ∀ q M {P Q} → (∀ m → P m ≡ᴾ Q m) → com q M P ≡ᴾ com q M Q

pattern Π' M P = com In  M P
pattern Σ' M P = com Out M P
{-
Π' : (M : ★)(P : M → Proto) → Proto
Π' M P = com In  M P

Σ' : (M : ★)(P : M → Proto) → Proto
Σ' M P = com Out M P
-}

ΠS' : (M : ★)(P : ..(_ : M) → Proto) → Proto
ΠS' M P = Π' (☐ M) (λ { [ m ] → P m })

ΣS' : (M : ★)(P : ..(_ : M) → Proto) → Proto
ΣS' M P = Σ' (☐ M) (λ { [ m ] → P m })

⟦_⟧ΠΣ : InOut → (M : ★) (P : M → ★) → ★
⟦_⟧ΠΣ In  = Π
⟦_⟧ΠΣ Out = Σ

⟦_⟧ : Proto → ★
⟦ end       ⟧ = 𝟙
⟦ com q M P ⟧ = ⟦ q ⟧ΠΣ M λ x → ⟦ P x ⟧

data Choreo (I : ★) : ★₁ where
  _-[_]→_⁏_ : (A : I) (M : ★) (B : I) (ℂ : ..(m : M) → Choreo I) → Choreo I
  _-[_]→★⁏_ : (A : I) (M : ★)         (ℂ :   (m : M) → Choreo I) → Choreo I
  end       : Choreo I

_-[_]→ø⁏_ : ∀ {I}(A : I) (M : ★)         (ℂ : ..(m : M) → Choreo I) → Choreo I
A -[ M ]→ø⁏ ℂ = A -[ ☐ M ]→★⁏ λ { [ m ] → ℂ m }

data [_/_≡_] {I} : Choreo I → I → Proto → ★₁ where
  IΣD : ∀ {A B   M ℂ ℂA} → (∀   m → [ ℂ m / A ≡ ℂA m ]) → [ (A -[ M ]→ B ⁏ ℂ) / A ≡ Σ' M ℂA ]
  IΠD : ∀ {A B   M ℂ ℂB} → (∀   m → [ ℂ m / B ≡ ℂB m ]) → [ (A -[ M ]→ B ⁏ ℂ) / B ≡ Π' M ℂB ]
--  IΠS : ∀ {A B C M ℂ ℂC} → (∀ ..m → [ ℂ m / C ≡ ℂC m ]) → [ (A -[ M ]→ B ⁏ ℂ) / C ≡ Π' (☐ M) ℂC ]
  ★ΣD : ∀ {A     M ℂ ℂA} → (∀   m → [ ℂ m / A ≡ ℂA m ]) → [ (A -[ M ]→★⁏   ℂ) / A ≡ Σ' M ℂA ]
  ★ΠD : ∀ {A B   M ℂ ℂB} → (∀   m → [ ℂ m / B ≡ ℂB m ]) → [ (A -[ M ]→★⁏   ℂ) / B ≡ Π' M ℂB ]
  --øΣD : ∀ {A     M ℂ ℂA} → (∀ ..m → [ ℂ m / A ≡ ℂA m ]) → [ (A -[ M ]→ø⁏   ℂ) / A ≡ Σ' S M ℂA ]
  --øΠD : ∀ {A B   M ℂ ℂB} → (∀ ..m → [ ℂ m / B ≡ ℂB m ]) → [ (A -[ M ]→ø⁏   ℂ) / B ≡ Π' S M ℂB ]
  end : ∀ {A} → [ end / A ≡ end ]

Trace : Proto → Proto
Trace end          = end
Trace (com _ A B) = Σ' A λ m → Trace (B m)

dual : Proto → Proto
dual end = end
dual (com q A B) = com (dualInOut q) A (λ x → dual (B x))

module _
  (funExt : ∀ {a}{b}{A : ★_ a}{B : A → ★_ b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g)
  where
    ≡ᴾ-sound : ∀ {P Q} → P ≡ᴾ Q → P ≡ Q
    ≡ᴾ-sound end           = refl
    ≡ᴾ-sound (com q M P≡Q) = cong (com q M) (funExt λ m → ≡ᴾ-sound (P≡Q m))

≡ᴾ-refl : ∀ P → P ≡ᴾ P
≡ᴾ-refl end         = end
≡ᴾ-refl (com q M P) = com q M (λ m → ≡ᴾ-refl (P m))

Trace-idempotent : ∀ P → Trace (Trace P) ≡ᴾ Trace P
Trace-idempotent end = end
Trace-idempotent (com q M P) = Σ' M λ m → Trace-idempotent (P m)

Trace-dual-oblivious : ∀ P → Trace (dual P) ≡ᴾ Trace P
Trace-dual-oblivious end = end
Trace-dual-oblivious (com q M P) = Σ' M λ m → Trace-dual-oblivious (P m)

Tele : Proto → ★
Tele P = ⟦ Trace P ⟧

_>>≡_ : (P : Proto) → (Tele P → Proto) → Proto
end >>≡ Q = Q _
com π A B >>≡ Q = com π A (λ x → B x >>≡ (λ xs → Q (x , xs)))

_>>_ : Proto → Proto → Proto
P >> Q = P >>≡ λ _ → Q

++Tele : ∀ (P : Proto){Q : Tele P → Proto} (xs : Tele P) → Tele (Q xs) → Tele (P >>≡ Q)
++Tele end         _        ys = ys
++Tele (com q M P) (x , xs) ys = x , ++Tele (P x) xs ys

right-unit : ∀ (P : Proto) → (P >>≡ λ x → end) ≡ᴾ P
right-unit end = end
right-unit (com q M P) = com q M λ m → right-unit (P m)

assoc : ∀ (P : Proto)(Q : Tele P → Proto)(R : Tele (P >>≡ Q) → Proto)
        → P >>≡ (λ x → Q x >>≡ (λ y → R (++Tele P x y))) ≡ᴾ ((P >>≡ Q) >>≡ R)
assoc end         Q R = ≡ᴾ-refl (Q _ >>≡ R)
assoc (com q M P) Q R = com q M λ m → assoc (P m) (λ ms → Q (m , ms)) (λ ms → R (m , ms))

_×'_ : Set → Proto → Proto
A ×' B = Σ' A λ _ → B

_→'_ : Set → Proto → Proto
A →' B = Π' A λ _ → B

data DualInOut : InOut → InOut → ★ where
  DInOut : DualInOut In  Out
  DOutIn : DualInOut Out In

data Dual : Proto → Proto → ★₁ where
  end : Dual end end
  Π·Σ : ∀ {A B B'} → (∀ x → Dual (B x) (B' x)) → Dual (Π' A B) (Σ' A B')
  Σ·Π : ∀ {A B B'} → (∀ x → Dual (B x) (B' x)) → Dual (Σ' A B) (Π' A B')

data Sing {a} {A : ★_ a} : ..(x : A) → ★_ a where
  sing : ∀ x → Sing x

-- Commit = λ M R → Σ' D (☐ M) λ { [ m ] → Π' D R λ r → Σ' D (Sing m) (λ _ → end) }
Commit = λ M R → ΣS' M λ m → Π' R λ r → Σ' (Sing m) (λ _ → end)

commit : ∀ M R (m : M)  → ⟦ Commit M R ⟧
commit M R m = [ m ] , (λ x → (sing m) , _)

decommit : ∀ M R (r : R) → ⟦ dual (Commit M R) ⟧
decommit M R r = λ { [ m ] → r , (λ x → 0₁) }

data [_&_≡_]InOut : InOut → InOut → InOut → ★₁ where
  ΠXX : ∀ {X} → [ In & X  ≡ X ]InOut
  XΠX : ∀ {X} → [ X  & In ≡ X ]InOut

&InOut-comm : ∀ {P Q R} → [ P & Q ≡ R ]InOut → [ Q & P ≡ R ]InOut
&InOut-comm ΠXX = XΠX
&InOut-comm XΠX = ΠXX

data [_&_≡_] : Proto → Proto → Proto → ★₁ where
  end& : ∀ {P} → [ end & P ≡ P ]
  &end : ∀ {P} → [ P & end ≡ P ]
  D&D  : ∀ {qP qQ qR M P Q R}(q : [ qP & qQ ≡ qR ]InOut)(P& : ∀   m → [ P m     & Q m     ≡ R m ]) → [ com qP    M  P & com qQ    M  Q ≡ com qR M R ]
  S&D  : ∀ {qP qQ qR M P Q R}(q : [ qP & qQ ≡ qR ]InOut)(P& : ∀   m → [ P [ m ] & Q m     ≡ R m ]) → [ com qP (☐ M) P & com qQ    M  Q ≡ com qR M R ]
  D&S  : ∀ {qP qQ qR M P Q R}(q : [ qP & qQ ≡ qR ]InOut)(P& : ∀   m → [ P m     & Q [ m ] ≡ R m ]) → [ com qP    M  P & com qQ (☐ M) Q ≡ com qR M R ]

&-comm : ∀ {P Q R} → [ P & Q ≡ R ] → [ Q & P ≡ R ]
&-comm end& = &end
&-comm &end = end&
&-comm (D&D q P&) = D&D (&InOut-comm q) (λ m → &-comm (P& m))
&-comm (S&D q P&) = D&S (&InOut-comm q) (λ m → &-comm (P& m))
&-comm (D&S q P&) = S&D (&InOut-comm q) (λ m → &-comm (P& m))

DualInOut-sym : ∀ {P Q} → DualInOut P Q → DualInOut Q P
DualInOut-sym DInOut = DOutIn
DualInOut-sym DOutIn = DInOut

Dual-sym : ∀ {P Q} → Dual P Q → Dual Q P
Dual-sym end = end
Dual-sym (Π·Σ f) = Σ·Π (λ x → Dual-sym (f x))
Dual-sym (Σ·Π f) = Π·Σ (λ x → Dual-sym (f x))

DualInOut-spec : ∀ P → DualInOut P (dualInOut P)
DualInOut-spec In  = DInOut
DualInOut-spec Out = DOutIn

Dual-spec : ∀ P → Dual P (dual P)
Dual-spec end = end
Dual-spec (com In M P) = Π·Σ (λ x → Dual-spec (P x))
Dual-spec (com Out M P) = Σ·Π (λ x → Dual-spec (P x))

module _ (funExt : ∀ {a b}{A : ★_ a}{B : A → ★_ b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g)where
  dual-Tele : ∀ P → Tele (dual P) ≡ Tele P
  dual-Tele P = cong ⟦_⟧ (≡ᴾ-sound funExt (Trace-dual-oblivious P))

El : (P : Proto) → (Tele P → ★) → ★
El end         X = X _
El (com q M P) X = ⟦ q ⟧ΠΣ M λ x → El (P x) (λ y → X (x , y))

module ElBind (funExt : ∀ {a b}{A : ★_ a}{B : A → ★_ b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g)where

  bind-spec : (P : Proto){Q : Tele P → Proto}{X : Tele (P >>≡ Q) → ★} → El (P >>≡ Q) X ≡ El P (λ x → El (Q x) (λ y → X (++Tele P x y)))
  bind-spec end         = refl
  bind-spec (com q M P) = cong (⟦ q ⟧ΠΣ M) (funExt λ m → bind-spec (P m))


module _ {A B} where
  run-com : (P : Proto) → El P (const A) → El (dual P) (const B) → A × B
  run-com end      a       b       = a , b
  run-com (Π' M P) p       (m , q) = run-com (P m) (p m) q
  run-com (Σ' M P) (m , p) q       = run-com (P m) p (q m)

com-cont : (P : Proto){A : Tele P → ★}{B : Tele (dual P) → ★} → El P A → El (dual P) B → Σ (Tele P) A × Σ (Tele (dual P)) B
com-cont end p q = (_ , p)  , (_ , q)
com-cont (Π' A B) p (m , q) with com-cont (B m) (p m) q
... | (X , a) , (Y , b) = ((m , X) , a) , (m , Y) , b
com-cont (Σ' A B) (m , p) q with com-cont (B m) p (q m)
... | (X , a) , (Y , b) = ((m , X) , a) , (m , Y) , b

data ProcessF (this : Proto → ★₁): Proto → ★₁ where
  recv : ∀ {M P} → ((m : M) → this (P m)) → ProcessF this (Π' M P)
  send : ∀ {M P} (m : M) → this (P m) → ProcessF this (Σ' M P)

recvS : ∀ {this : Proto → ★₁}{M}{P : ☐ M → Proto} → (..(m : M) → this (P [ m ])) → ProcessF this (Π' (☐ M) P)
recvS = recv ∘ un☐

sendS : ∀ {this : Proto → ★₁}{M}{P : ☐ M → Proto} ..(m : M) → this (P [ m ]) → ProcessF this (Σ' (☐ M) P)
sendS m = send [ m ]

data Process (A : ★) : Proto → ★₁ where
  do  : ∀ {P} → ProcessF (Process A) P → Process A P
  end : A → Process A end

mutual
  SimL : Proto → Proto → ★₁
  SimL P Q = ProcessF (flip Sim Q) P

  SimR : Proto → Proto → ★₁
  SimR P Q = ProcessF (Sim P) Q

  data Sim : Proto → Proto → ★₁ where
    left  : ∀ {q M P Q} → SimL (com q M P) Q → Sim (com q M P) Q
    right : ∀ {P q M Q} → SimR P (com q M Q) → Sim P (com q M Q)
    end   : Sim end end

_⟹_ : Proto → Proto → ★₁
P ⟹ Q = Sim (dual P) Q

_⟹ᴾ_ : Proto → Proto → ★₁
P ⟹ᴾ Q = ∀ {A} → Process A (dual P) → Process A Q

{-
sim& : ∀ {PA PB PAB} → [ PA & PB ≡ PAB ] → Sim end PA → Sim end PB → Sim end PAB
sim&R : ∀ {PA PB PAB} → [ PA & PB ≡ PAB ] → SimR end PA → SimR end PB → SimR end PAB

sim& P& (right ·PA) (right ·PB) = {! (sim&R P& ·PA ·PB)!}
sim& end& PA PB = PB
sim& &end PA PB = PA

sim&R (ΠDΣDΣS P&) (recv PQA)   (send m PQB) = sendS m (sim& (P& m) (PQA m) PQB)
sim&R (ΠDΠDΠD P&) (recv PQA)   (recv PQB)   = recv λ m → sim& (P& m) (PQA m) (PQB m)
sim&R (ΠS-S-S P&) (recvS PQA)   (recvS PQB)   = recvS λ m → sim& (P& m) (PQA m) (PQB m)
sim&R (ΠS-S-S P&) (recvS PQA)   (sendS m PQB) = sendS m (sim& (P& m) (PQA m) PQB)
sim&R (ΠS-D-D P&) (recvS PQA)   (recv PQB)   = recv λ m → sim& (P& m) (PQA m) (PQB m)
sim&R (ΠS-D-D P&) (recvS PQA)   (send m PQB) = send m (sim& (P& m) (PQA m) PQB)
sim&R (ΣDΠDΣS P&) (send m PQA) (recv PQB)   = sendS m (sim& (P& m) PQA (PQB m))
sim&R &end _ ()
-}

{-
sim&R (ΣDΠDΣS x) (send x₁ x₂) (recv x₃) = {!!}
-}

{-
sim& : ∀ {PA PB PAB QA QB QAB} → [ PA & PB ≡ PAB ] → [ QA & QB ≡ QAB ] → Sim PA QA → Sim PB QB → Sim PAB QAB
sim&L : ∀ {PA PB PAB QA QB QAB} → [ PA & PB ≡ PAB ] → [ QA & QB ≡ QAB ] → SimL PA QA → SimL PB QB → SimL PAB QAB
sim&R : ∀ {PA PB PAB QA QB QAB} → [ PA & PB ≡ PAB ] → [ QA & QB ≡ QAB ] → SimR PA QA → SimR PB QB → SimR PAB QAB

sim& P& Q& (left PQA) (left PQB) = left (sim&L P& Q& PQA PQB)
sim& P& Q& (left PQA) (right PQB) = {!!}
sim& P& Q& (left PQA) end = {!!}
sim& P& Q& (right x) PQB = {!!}
sim& P& Q& end PQB = {!!}

sim&L (ΠDΣDΣS P&) Q& (recv PQA)   (send m PQB) = sendS m (sim& (P& m) Q& (PQA m) PQB)
sim&L (ΠDΠDΠD P&) Q& (recv PQA)   (recv PQB)   = recv λ m → sim& (P& m) Q& (PQA m) (PQB m)
sim&L (ΠS-S-S P&) Q& (recvS PQA)   (recvS PQB)   = recvS λ m → sim& (P& m) Q& (PQA m) (PQB m)
sim&L (ΠS-S-S P&) Q& (recvS PQA)   (sendS m PQB) = sendS m (sim& (P& m) Q& (PQA m) PQB)
sim&L (ΠS-D-D P&) Q& (recvS PQA)   (recv PQB)   = recv λ m → sim& (P& m) Q& (PQA m) (PQB m)
sim&L (ΠS-D-D P&) Q& (recvS PQA)   (send m PQB) = send m (sim& (P& m) Q& (PQA m) PQB)
sim&L (ΣDΠDΣS P&) Q& (send m PQA) (recv PQB)   = sendS m (sim& (P& m) Q& PQA (PQB m))
sim&L &end Q& PQA ()

{-
sim&R (ΠDΣDΣS P&) Q& (recv PQA)   (send m PQB) = ?
sim&R (ΠDΠDΠD P&) Q& (recv PQA)   (recv PQB)   = ? -- recv λ m → sim& (P& m) Q& (PQA m) (PQB m)
sim&R (ΠS-S-S P&) Q& (recvS PQA)   (recvS PQB)   = ? -- recvS λ m → sim& (P& m) Q& (PQA m) (PQB m)
sim&R (ΠS-S-S P&) Q& (recvS PQA)   (sendS m PQB) = ? -- sendS m (sim& (P& m) Q& (PQA m) PQB)
sim&R (ΠS-D-D P&) Q& (recvS PQA)   (recv PQB)   = ? -- recv λ m → sim& (P& m) Q& (PQA m) (PQB m)
sim&R (ΠS-D-D P&) Q& (recvS PQA)   (send m PQB) = ? -- send m (sim& (P& m) Q& (PQA m) PQB)
sim&R (ΣDΠDΣS P&) Q& (send m PQA) (recv PQB)   = ? -- sendS m (sim& (P& m) Q& PQA (PQB m))
sim&R end& Q& PQA PQB = ?
-}
-}

sim-id : ∀ P → Sim (dual P) P
sim-id end = end
sim-id (Π' A B) = right (recv (λ x → left (send x (sim-id (B x)))))
sim-id (Σ' A B) = left (recv (λ x → right (send x (sim-id (B x)))))

sim-comp : ∀ {P Q Q' R} → Dual Q Q' → Sim P Q → Sim Q' R → Sim P R
sim-compRL : ∀ {P Q Q' R} → Dual Q Q' → SimR P Q → SimL Q' R → Sim P R
sim-compL : ∀ {P Q Q' R} → Dual Q Q' → SimL P Q → Sim Q' R → SimL P R
sim-compR : ∀ {P Q Q' R} → Dual Q Q' → Sim P Q → SimR Q' R → SimR P R

sim-comp Q-Q' (left x) QR = left (sim-compL Q-Q' x QR)
sim-comp Q-Q' (right x) (left x₁) = sim-compRL Q-Q' x x₁
sim-comp Q-Q' (right x) (right x₁) = right (sim-compR Q-Q' (right x) x₁)
sim-comp ()   (right x) end
sim-comp end end QR = QR

sim-compRL end () QR
sim-compRL (Π·Σ x₁) (recv x) (send x₂ x₃) = sim-comp (x₁ x₂) (x x₂) x₃
sim-compRL (Σ·Π x)  (send x₁ x₂) (recv x₃) = sim-comp (x x₁) x₂ (x₃ x₁)

sim-compL Q-Q' (recv PQ) QR = recv (λ m → sim-comp Q-Q' (PQ m) QR)
sim-compL Q-Q' (send m PQ) QR = send m (sim-comp Q-Q' PQ QR)

sim-compR Q-Q' PQ (recv QR)   = recv (λ m → sim-comp Q-Q' PQ (QR m))
sim-compR Q-Q' PQ (send m QR) = send m (sim-comp Q-Q' PQ QR)

_♦_ : ∀ {P Q R} → Sim P Q → Sim (dual Q) R → Sim P R
_♦_ = sim-comp (Dual-spec _)

⟹-comp : ∀ {P Q R} → P ⟹ Q → Q ⟹ R → P ⟹ R
⟹-comp = _♦_

!ˢ : ∀ {P Q} → Sim P Q → Sim Q P
sim-symL : ∀ {P Q} → SimL P Q → SimR Q P
sim-symR : ∀ {P Q} → SimR P Q → SimL Q P

!ˢ (left x) = right (sim-symL x)
!ˢ (right x) = left (sim-symR x)
!ˢ end = end

sim-symL (recv PQ)   = recv (λ m → !ˢ (PQ m))
sim-symL (send m PQ) = send m (!ˢ PQ)

sim-symR (recv PQ)   = recv (λ m → !ˢ (PQ m))
sim-symR (send m PQ) = send m (!ˢ PQ)

sim-unit : ∀ {P} → Sim end P → Process 𝟙 P
sim-unit (right (recv P)) = do (recv (λ m → sim-unit (P m)))
sim-unit (right (send m P)) = do (send m (sim-unit P))
sim-unit end = end 0₁

module _ where

  mod₁ : ∀ {A A' B : ★} → (A → A') → A × B → A' × B
  mod₁ = λ f → Data.Product.map f id

  mod₂ : ∀ {A B B' : ★} → (B → B') → A × B → A × B'
  mod₂ = λ f → Data.Product.map id f

  trace : ∀ {P P' Q Q'} → Dual P P' → Dual Q Q' →  Sim end P' → Sim P Q → Sim Q' end
        → Tele P × Tele Q
  trace (Π·Σ x₁) Q-Q' (right (send x x₂)) (left (recv x₃)) Q· = mod₁ (_,_ x) (trace (x₁ x) Q-Q' x₂ (x₃ x) Q·)
  trace (Σ·Π x₁) Q-Q' (right (recv x)) (left (send x₂ x₃)) Q· = mod₁ (_,_ x₂) (trace (x₁ x₂) Q-Q' (x x₂) x₃ Q·)
  trace P-P' (Π·Σ x₁) ·P (right (recv x)) (left (send x₂ x₃)) = mod₂ (_,_ x₂) (trace P-P' (x₁ x₂) ·P (x x₂) x₃)
  trace P-P' (Σ·Π x₁) ·P (right (send x x₂)) (left (recv x₃)) = mod₂ (_,_ x) (trace P-P' (x₁ x) ·P x₂ (x₃ x))
  trace P-P' Q-Q' ·P end Q· = _

  module _ {P Q : Proto} where
    _≈_ : (PQ PQ' : Sim P Q) → ★₁
    PQ ≈ PQ' = ∀ {P' Q'}(P-P' : Dual P P')(Q-Q' : Dual Q Q') → (·P : Sim end P')(Q· : Sim Q' end)
       → trace P-P' Q-Q' ·P PQ Q· ≡ trace P-P' Q-Q' ·P PQ' Q·

module _ {P Q : Proto} where
  infix 2 _∼_
  _∼_ : (PQ PQ' : Sim P Q) → ★₁
  PQ ∼ PQ' = ∀ {P'} → (P'-P : Dual P' P) → (øP : Sim end P')
           → sim-comp P'-P øP PQ ≡ sim-comp P'-P øP PQ'

module _
  (funExt : ∀ {a}{b}{A : ★_ a}{B : A → ★_ b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g)
  where

  Dual-sym-sym : ∀ {P Q} (P-Q : Dual P Q) → P-Q ≡ Dual-sym (Dual-sym P-Q)
  Dual-sym-sym end = refl
  Dual-sym-sym (Π·Σ x) = cong Π·Σ (funExt (λ y → Dual-sym-sym (x y)))
  Dual-sym-sym (Σ·Π x) = cong Σ·Π (funExt (λ y → Dual-sym-sym (x y)))

module _
  (funExt : ∀ {a}{b}{A : ★_ a}{B : A → ★_ b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g)
  where
  sim-comp-assoc-end : ∀ {P P' Q Q' R}(P-P' : Dual P P')(Q-Q' : Dual Q Q')
    (øP : Sim end P)(PQ : Sim P' Q)(QR : Sim Q' R)
    → sim-comp Q-Q' (sim-comp P-P' øP PQ) QR
    ≡ sim-comp P-P' øP (sim-comp Q-Q' PQ QR)
  sim-comp-assoc-end (Π·Σ x₁) Q-Q' (right (recv x)) (left (send x₂ x₃)) QR
    = sim-comp-assoc-end (x₁ x₂) Q-Q' (x x₂) x₃ QR
  sim-comp-assoc-end (Σ·Π x) Q-Q' (right (send x₁ x₂)) (left (recv x₃)) QR
    = sim-comp-assoc-end (x x₁) Q-Q' x₂ (x₃ x₁) QR
  sim-comp-assoc-end P-P' (Π·Σ x₁) (right øP) (right (recv x)) (left (send x₂ x₃))
    = sim-comp-assoc-end P-P' (x₁ x₂) (right øP) (x x₂) x₃
  sim-comp-assoc-end P-P' (Σ·Π x) (right øP) (right (send x₁ x₂)) (left (recv x₃))
    = sim-comp-assoc-end P-P' (x x₁) (right øP) x₂ (x₃ x₁)
  sim-comp-assoc-end P-P' Q-Q' (right øP) (right x) (right (recv x₁))
    = cong (right ∘ recv) (funExt (λ m → sim-comp-assoc-end P-P' Q-Q' (right øP) (right x) (x₁ m)))
  sim-comp-assoc-end P-P' Q-Q' (right øP) (right x) (right (send x₁ x₂))
    = cong (right ∘ send x₁) (sim-comp-assoc-end P-P' Q-Q' (right øP) (right x) x₂)
  sim-comp-assoc-end end Q-Q' end PQ QR = refl

  ♦-assoc-end : ∀ {P Q R}(øP : Sim end P)(PQ : Sim (dual P) Q)(QR : Sim (dual Q) R)
    → (øP ♦ PQ) ♦ QR ≡ øP ♦ (PQ ♦ QR)
  ♦-assoc-end = sim-comp-assoc-end (Dual-spec _) (Dual-spec _)

  open ≡-Reasoning
  sim-comp-assoc : ∀ {W P P' Q Q' R}(P-P' : Dual P P')(Q-Q' : Dual Q Q')
    (WP : Sim W P)(PQ : Sim P' Q)(QR : Sim Q' R)
    → sim-comp Q-Q' (sim-comp P-P' WP PQ) QR
    ∼ sim-comp P-P' WP (sim-comp Q-Q' PQ QR)
  sim-comp-assoc P-P' Q-Q' WP PQ QR {W'} W'-W øW'
    = sim-comp W'-W øW' (sim-comp Q-Q' (sim-comp P-P' WP PQ) QR)
    ≡⟨ sym (sim-comp-assoc-end W'-W Q-Q' øW' (sim-comp P-P' WP PQ) QR) ⟩
      sim-comp Q-Q' (sim-comp W'-W øW' (sim-comp P-P' WP PQ)) QR
    ≡⟨ cong (λ X → sim-comp Q-Q' X QR) (sym (sim-comp-assoc-end W'-W P-P' øW' WP PQ)) ⟩
      sim-comp Q-Q' (sim-comp P-P' (sim-comp W'-W øW' WP) PQ) QR
    ≡⟨ sim-comp-assoc-end P-P' Q-Q' (sim-comp W'-W øW' WP) PQ QR ⟩
      sim-comp P-P' (sim-comp W'-W øW' WP) (sim-comp Q-Q' PQ QR)
    ≡⟨ sim-comp-assoc-end W'-W P-P' øW' WP (sim-comp Q-Q' PQ QR) ⟩
      sim-comp W'-W øW' (sim-comp P-P' WP (sim-comp Q-Q' PQ QR))
    ∎

  ♦-assoc : ∀ {W P Q R}(WP : Sim W P)(PQ : Sim (dual P) Q)(QR : Sim (dual Q) R)
    → (WP ♦ PQ) ♦ QR ∼ WP ♦ (PQ ♦ QR)
  ♦-assoc = sim-comp-assoc (Dual-spec _) (Dual-spec _)


∼-ø : ∀ {P}{s s' : Sim end P} → s ∼ s' → s ≡ s'
∼-ø s∼s' = s∼s' end end

module _
  (funExt : ∀ {a}{b}{A : ★_ a}{B : A → ★_ b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g)
  where

  sim-!! : ∀ {P Q}(PQ : Sim P Q) → PQ ≡ !ˢ (!ˢ PQ)
  sim-!! (left (recv x))    = cong (left ∘ recv) (funExt λ m → sim-!! (x m))
  sim-!! (left (send x x₁)) = cong (left ∘ send x) (sim-!! x₁)
  sim-!! (right (recv x))    = cong (right ∘ recv) (funExt λ m → sim-!! (x m))
  sim-!! (right (send x x₁)) = cong (right ∘ send x) (sim-!! x₁)
  sim-!! end = refl

  sim-comp-!-end : ∀ {Q Q' R}(Q-Q' : Dual Q Q')(·Q : Sim end Q)(Q'R : Sim Q' R)
    → sim-comp (Dual-sym Q-Q') (!ˢ Q'R) (!ˢ ·Q) ≡ !ˢ (sim-comp Q-Q' ·Q Q'R)
  sim-comp-!-end (Π·Σ x₁) (right (recv x)) (left (send x₂ x₃)) = sim-comp-!-end (x₁ x₂) (x x₂) x₃
  sim-comp-!-end (Σ·Π x) (right (send x₁ x₂)) (left (recv x₃)) = sim-comp-!-end (x x₁) x₂ (x₃ x₁)
  sim-comp-!-end Q-Q' (right x) (right (recv x₁))
    = cong (left ∘ recv) (funExt (λ x₂ → sim-comp-!-end Q-Q' (right x) (x₁ x₂)))
  sim-comp-!-end Q-Q' (right x) (right (send x₁ x₂))
    = cong (left ∘ send x₁) (sim-comp-!-end Q-Q' (right x) x₂)
  sim-comp-!-end end end QR = {!!}

  open ≡-Reasoning
  module _ {P Q}{s s' : Sim P Q} where
    !ˢ-cong : s ∼ s' → !ˢ s ∼ !ˢ s'
    !ˢ-cong s∼s' Q'-Q øQ'
      = sim-comp Q'-Q øQ' (!ˢ s)
      ≡⟨ {!!} ⟩
        sim-comp Q'-Q øQ' (!ˢ (sim-comp (Dual-spec Q) s (sim-id _)))
      ≡⟨ {!!} ⟩
        sim-comp Q'-Q øQ' (!ˢ s')
      ∎

  postulate
    sim-comp-assoc-end' : ∀ {P Q Q' R R'}(Q-Q' : Dual Q Q')(R-R' : Dual R R')
      (PQ : Sim P Q)(QR : Sim Q' R )(Rø : Sim R' end)
      → sim-comp R-R' (sim-comp Q-Q' PQ QR) Rø
      ≡ sim-comp Q-Q' PQ (sim-comp R-R' QR Rø)


  sim-comp-! : ∀ {P Q Q' R}(Q-Q' : Dual Q Q')(PQ : Sim P Q)(Q'R : Sim Q' R)
    → sim-comp (Dual-sym Q-Q') (!ˢ Q'R) (!ˢ PQ) ∼ !ˢ (sim-comp Q-Q' PQ Q'R)
  sim-comp-! Q-Q' PQ Q'R {R'} R'-R øR'
    = sim-comp R'-R øR' (sim-comp (Dual-sym Q-Q') (!ˢ Q'R) (!ˢ PQ))
    ≡⟨ sim-!! (sim-comp R'-R øR' (sim-comp (Dual-sym Q-Q') (!ˢ Q'R) (!ˢ PQ))) ⟩
      !ˢ( !ˢ ((sim-comp R'-R øR' (sim-comp (Dual-sym Q-Q') (!ˢ Q'R) (!ˢ PQ)))))
    ≡⟨ cong (!ˢ ∘ !ˢ) (sym (sim-comp-assoc-end funExt R'-R (Dual-sym Q-Q') øR' (!ˢ Q'R) (!ˢ PQ))) ⟩
      !ˢ
        (!ˢ
         (sim-comp (Dual-sym Q-Q') (sim-comp R'-R øR' (!ˢ Q'R)) (!ˢ PQ)))
    ≡⟨ cong !ˢ (sym (sim-comp-!-end (Dual-sym Q-Q') (sim-comp R'-R øR' (!ˢ Q'R)) (!ˢ PQ))) ⟩
      !ˢ
        (sim-comp (Dual-sym (Dual-sym Q-Q')) (!ˢ (!ˢ PQ))
         (!ˢ (sim-comp R'-R øR' (!ˢ Q'R))))
    ≡⟨ cong₂ (λ X Y → !ˢ (sim-comp X Y (!ˢ (sim-comp R'-R øR' (!ˢ Q'R)))))
         (sym (Dual-sym-sym funExt Q-Q')) (sym (sim-!! PQ)) ⟩
     !ˢ (sim-comp Q-Q' PQ (!ˢ (sim-comp R'-R øR' (!ˢ Q'R))))
    ≡⟨ cong (!ˢ ∘ sim-comp Q-Q' PQ) (sym (sim-comp-!-end R'-R øR' (!ˢ Q'R))) ⟩
      !ˢ
        (sim-comp Q-Q' PQ
         (sim-comp (Dual-sym R'-R) (!ˢ (!ˢ Q'R)) (!ˢ øR')))
    ≡⟨ cong
         (λ X → !ˢ (sim-comp Q-Q' PQ (sim-comp (Dual-sym R'-R) X (!ˢ øR'))))
         (sym (sim-!! Q'R)) ⟩
      !ˢ (sim-comp Q-Q' PQ (sim-comp (Dual-sym R'-R) Q'R (!ˢ øR')))
    -- ≡⟨ cong !ˢ (sym (sim-comp-assoc-end' Q-Q' (Dual-sym R'-R) PQ Q'R (!ˢ øR'))) ⟩
    ≡⟨ ∼-ø {!!}⟩
      !ˢ (sim-comp (Dual-sym R'-R) (sim-comp Q-Q' PQ Q'R) (!ˢ øR'))
    ≡⟨ cong (λ X → !ˢ (sim-comp (Dual-sym R'-R) X (!ˢ øR'))) (sim-!! (sim-comp Q-Q' PQ Q'R)) ⟩
      !ˢ (sim-comp (Dual-sym R'-R) (!ˢ (!ˢ (sim-comp Q-Q' PQ Q'R)))
                                   (!ˢ øR'))
    ≡⟨ cong !ˢ (sim-comp-!-end R'-R øR' (!ˢ (sim-comp Q-Q' PQ Q'R))) ⟩
      !ˢ (!ˢ (sim-comp R'-R øR' (!ˢ (sim-comp Q-Q' PQ Q'R))))
    ≡⟨ sym (sim-!! (sim-comp R'-R øR' (!ˢ (sim-comp Q-Q' PQ Q'R)))) ⟩
      sim-comp R'-R øR' (!ˢ (sim-comp Q-Q' PQ Q'R))
    ∎

  ♦-! : ∀ {P Q R}(PQ : Sim P Q)(QR : Sim (dual Q) R)
    → !ˢ (PQ ♦ QR) ∼ (!ˢ QR) ♦ (!ˢ {!PQ!})
  ♦-! = {!!}
{-

unit-sim : ∀ {P} → Process 𝟙 P → Sim end P
unit-sim (do (send m x)) = right (send m (unit-sim x))
unit-sim (do (recv x)) = right (recv (λ m → unit-sim (x m)))
unit-sim (end x) = end

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

apply-sim : ∀ {P Q} → Sim P Q → P ⟹ᴾ Q
apply-sim (left (send m x)) (do (recv x₁)) = apply-sim x (x₁ m)
apply-sim (left (recv x)) (do (send m x₁)) = apply-sim (x m) x₁
apply-sim (right (send m x)) P₂ = do (send m (apply-sim x P₂))
apply-sim (right (recv x)) P₂ = do (recv (λ m → apply-sim (x m) P₂))
apply-sim end P = P

apply-sim' : ∀ {P Q} → Sim P Q → Q ⟹ᴾ P -- ∀ {A} → Process A Q → Process A (dual P)
apply-sim' PQ P = apply-sim (sim-sym PQ) P

apply : ∀ {P Q A} → P ⟹ Q → Process A P → Process A Q
apply PQ P = apply-sim PQ (dual² P)

module _ (funExt : ∀ {a}{b}{A : ★_ a}{B : A → ★_ b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g) where
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
