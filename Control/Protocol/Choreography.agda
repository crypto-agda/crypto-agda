
-- {-# OPTIONS --without-K #-}
open import Coinduction
open import Function.NP
open import Type
open import Level
open import Data.Product
open import Data.One

open import Relation.Binary.PropositionalEquality.NP

module Control.Protocol.Choreography where

Π· : ∀ {a b}(A : ★_ a) → (B : ..(_ : A) → ★_ b) → ★_ (a ⊔ b)
Π· A B = ..(x : A) → B x

{-
record Σ· {a b} (A : Set a) (B : ..(_ : A) → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    {-..-}proj₁· : A
    proj₂· : B proj₁·
-}
data Σ· {a b} (A : Set a) (B : ..(_ : A) → Set b) : Set (a ⊔ b) where
  _,_ : ..(proj₁· : A) (proj₂· : B proj₁·) → Σ· A B

data Mod : ★ where S D : Mod

→M : ∀ {a b} → Mod → ★_ a → ★_ b → ★_ (a ⊔ b)
→M S A B = ..(_ : A) → B
→M D A B = A → B

ΠM : ∀ {a b}(m : Mod) → (A : ★_ a) → (B : →M m A (★_ b)) → ★_ (a ⊔ b)
ΠM S A B = Π· A B
ΠM D A B = Π A B

appM' : ∀ {a b}(m : Mod){A : ★_ a}{B : ★_ b}(P : →M m A B) → A → B
appM' S P x = P x
appM' D P x = P x

appM : ∀ {a b}(m : Mod){A : ★_ a}{B : →M m A (★_ b)}(P : ΠM m A B)(x : A) → appM' m B x
appM S P x = P x
appM D P x = P x

data ΠΣ : ★ where
  Π' Σ' : ΠΣ

data Proto : ★₁ where
  end : Proto
  mk  : (q : ΠΣ)(d : Mod)(A : ★)(B : →M d A Proto) → Proto

data Choreo (I : ★) : ★₁ where
  _-[_]→_⁏_ : (A : I) (M : ★) (B : I) (ℂ : ..(m : M) → Choreo I) → Choreo I
  _-[_]→★⁏_ : (A : I) (M : ★)         (ℂ :   (m : M) → Choreo I) → Choreo I
  ø         : Choreo I

data [_/_≡_] {I} : Choreo I → I → Proto → ★₁ where
  ΣD :  ∀ {A B   M ℂ ℂA} → (∀ m → [ ℂ m / A ≡ ℂA m ]) → [ (A -[ M ]→ B ⁏ ℂ) / A ≡ mk Σ' D M ℂA ]
  ΠD :  ∀ {A B   M ℂ ℂB} → (∀ m → [ ℂ m / B ≡ ℂB m ]) → [ (A -[ M ]→ B ⁏ ℂ) / B ≡ mk Π' D M ℂB ]
  ΠS :  ∀ {A B C M ℂ ℂC} → (∀ m → [ ℂ m / C ≡ ℂC m ]) → [ (A -[ M ]→ B ⁏ ℂ) / C ≡ mk Π' S M ℂC ]

Tele : Proto → ★
Tele end = 𝟙
Tele (mk Π' D A B) = Σ A λ x → Tele (B x)
Tele (mk Σ' D A B) = Σ A λ x → Tele (B x)
Tele (mk Π' S A B) = Σ· A λ x → Tele (B x)
Tele (mk Σ' S A B) = Σ· A λ x → Tele (B x)

{-
_>>≡_ : (P : Proto) → (Tele P → Proto) → Proto
end >>≡ Q = Q _
Π' A B >>≡ Q = Π' A (λ x → B x >>≡ (λ xs → Q (x , xs)))
Σ' A B >>≡ Q = Σ' A (λ x → B x >>≡ (λ xs → Q (x , xs)))
later i P >>≡ Q = ?

++Tele : ∀ (P : Proto)(Q : Tele P → Proto) → (x : Tele P) → Tele (Q x) → Tele (P >>≡ Q)
++Tele end Q x y = y
++Tele (Π' M C) Q (m , x) y = m , ++Tele (C m) (λ x₁ → Q (m , x₁)) x y
++Tele (Σ' M C) Q (m , x) y = m , ++Tele (C m) _ x y
++Tele (later i P) Q x y = ?

module _ (funExt : ∀ {a}{b}{A : ★_ a}{B : ★_ b}{f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g) where
  right-unit : ∀ (P : Proto) → (P >>≡ λ x → end) ≡ P
  right-unit end = refl
  right-unit (Π' M C) = let p = funExt (λ x → right-unit (C x)) in cong (Π' M) p
  right-unit (Σ' M C) = cong (Σ' M) (funExt (λ x → right-unit (C x)))
  right-unit (later i P) = ?

  assoc : ∀ (P : Proto)(Q : Tele P → Proto)(R : Tele (P >>≡ Q) → Proto)
        → P >>≡ (λ x → Q x >>≡ (λ y → R (++Tele P Q x y))) ≡ ((P >>≡ Q) >>≡ R)
  assoc end Q R = refl
  assoc (Π' M C₁) Q R = cong (Π' M) (funExt (λ x → assoc (C₁ x) (λ xs → Q (x , xs)) (λ xs → R (x , xs))))
  assoc (Σ' M C₁) Q R = cong (Σ' M) (funExt (λ x → assoc (C₁ x) (λ xs → Q (x , xs)) (λ xs → R (x , xs))))
  assoc (later i P) Q R = ?

_>>_ : Proto → Proto → Proto
P >> Q = P >>≡ λ _ → Q
-}

_×'_ : Set → Proto → Proto
A ×' B = mk Σ' D A λ _ → B

_→'_ : Set → Proto → Proto
A →' B = mk Π' D A λ _ → B

dualΠΣ : ΠΣ → ΠΣ
dualΠΣ Π' = Σ'
dualΠΣ Σ' = Π'

dual : Proto → Proto
dual end = end
dual (mk q S A B) = mk (dualΠΣ q) S A (λ x → dual (B x))
dual (mk q D A B) = mk (dualΠΣ q) D A (λ x → dual (B x))

data DualΠΣ : ΠΣ → ΠΣ → ★ where
  DΠΣ : DualΠΣ Π' Σ'
  DΣΠ : DualΠΣ Σ' Π'

data Dual : Proto → Proto → ★₁ where
  end : Dual end end
  S : ∀ {A B B' π σ} → DualΠΣ π σ → (∀ ..x → Dual (B x) (B' x)) → Dual (mk π S A B) (mk σ S A B')
  D : ∀ {A B B' π σ} → DualΠΣ π σ → (∀   x → Dual (B x) (B' x)) → Dual (mk π D A B) (mk σ D A B')

data [_&_≡_] : Proto → Proto → Proto → ★₁ where
 -- comm   : ∀ {P Q R} → [ P & Q ≡ R ] → [ Q & P ≡ R ]
  end&   : ∀ {P} → [ end & P ≡ P ]
  ΠS-S-S : ∀ {q M P Q R} → (∀ ..m → [ P m & Q m ≡ R m ]) → [ mk Π' S M P & mk q  S M Q ≡ mk q  S M R ]
  ΠS-D-D : ∀ {q M P Q R} → (∀   m → [ P m & Q m ≡ R m ]) → [ mk Π' S M P & mk q  D M Q ≡ mk q  D M R ]
  ΠDΣDΣS : ∀   {M P Q R} → (∀   m → [ P m & Q m ≡ R m ]) → [ mk Π' D M P & mk Σ' D M Q ≡ mk Σ' S M R ]
  ΠDΠDΠD : ∀   {M P Q R} → (∀   m → [ P m & Q m ≡ R m ]) → [ mk Π' D M P & mk Π' D M Q ≡ mk Π' D M R ]

  &end    : ∀ {P} → [ P & end ≡ P ]
--  ΠS-S-S : ∀ {q M P Q R} → (∀ ..m → [ P m & Q m ≡ R m ]) → [ mk Π' S M P & mk q  S M Q ≡ mk q  S M R ]
--  ΠS-D-D : ∀ {q M P Q R} → (∀   m → [ P m & Q m ≡ R m ]) → [ mk Π' S M P & mk q  D M Q ≡ mk q  D M R ]
  ΣDΠDΣS : ∀   {M P Q R} → (∀   m → [ P m & Q m ≡ R m ]) → [ mk Σ' D M P & mk Π' D M Q ≡ mk Σ' S M R ]

DualΠΣ-sym : ∀ {P Q} → DualΠΣ P Q → DualΠΣ Q P
DualΠΣ-sym DΠΣ = DΣΠ
DualΠΣ-sym DΣΠ = DΠΣ

Dual-sym : ∀ {P Q} → Dual P Q → Dual Q P
Dual-sym end = end
Dual-sym (S d f) = S (DualΠΣ-sym d) (λ x → Dual-sym (f x))
Dual-sym (D d f) = D (DualΠΣ-sym d) (λ x → Dual-sym (f x))

DualΠΣ-spec : ∀ P → DualΠΣ P (dualΠΣ P)
DualΠΣ-spec Π' = DΠΣ
DualΠΣ-spec Σ' = DΣΠ

Dual-spec : ∀ P → Dual P (dual P)
Dual-spec end = end
Dual-spec (mk π S A B) = S (DualΠΣ-spec π) (λ x → Dual-spec (B x))
Dual-spec (mk π D A B) = D (DualΠΣ-spec π) (λ x → Dual-spec (B x))

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

data ProcessF (this : Proto → ★₁): Proto → ★₁ where
  recvD : ∀ {M P} → (ΠM D M λ m → this (P m)) → ProcessF this (mk Π' D M P)
  recvS : ∀ {M P} → (ΠM S M λ m → this (P m)) → ProcessF this (mk Π' S M P)
  sendD : ∀ {M P} → ΠM D M (λ m → this (P m) → ProcessF this (mk Σ' D M P))
  sendS : ∀ {M P} → ΠM S M (λ m → this (P m) → ProcessF this (mk Σ' S M P))

data Process (A : ★) : Proto → ★₁ where
  do  : ∀ {P} → ProcessF (Process A) P → Process A P
  end : A → Process A end

mutual
  SimL : Proto → Proto → ★₁
  SimL P Q = ProcessF (flip Sim Q) P

  SimR : Proto → Proto → ★₁
  SimR P Q = ProcessF (Sim P) Q

  data Sim : Proto → Proto → ★₁ where
    left  : ∀ {q d M P Q} → SimL (mk q d M P) Q → Sim (mk q d M P) Q
    right : ∀ {P q d M Q} → SimR P (mk q d M Q) → Sim P (mk q d M Q)
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

sim&R (ΠDΣDΣS P&) (recvD PQA)   (sendD m PQB) = sendS m (sim& (P& m) (PQA m) PQB)
sim&R (ΠDΠDΠD P&) (recvD PQA)   (recvD PQB)   = recvD λ m → sim& (P& m) (PQA m) (PQB m)
sim&R (ΠS-S-S P&) (recvS PQA)   (recvS PQB)   = recvS λ m → sim& (P& m) (PQA m) (PQB m)
sim&R (ΠS-S-S P&) (recvS PQA)   (sendS m PQB) = sendS m (sim& (P& m) (PQA m) PQB)
sim&R (ΠS-D-D P&) (recvS PQA)   (recvD PQB)   = recvD λ m → sim& (P& m) (PQA m) (PQB m)
sim&R (ΠS-D-D P&) (recvS PQA)   (sendD m PQB) = sendD m (sim& (P& m) (PQA m) PQB)
sim&R (ΣDΠDΣS P&) (sendD m PQA) (recvD PQB)   = sendS m (sim& (P& m) PQA (PQB m))
sim&R &end _ ()
-}

{-
sim&R (ΣDΠDΣS x) (sendD x₁ x₂) (recvD x₃) = {!!}
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

sim&L (ΠDΣDΣS P&) Q& (recvD PQA)   (sendD m PQB) = sendS m (sim& (P& m) Q& (PQA m) PQB)
sim&L (ΠDΠDΠD P&) Q& (recvD PQA)   (recvD PQB)   = recvD λ m → sim& (P& m) Q& (PQA m) (PQB m)
sim&L (ΠS-S-S P&) Q& (recvS PQA)   (recvS PQB)   = recvS λ m → sim& (P& m) Q& (PQA m) (PQB m)
sim&L (ΠS-S-S P&) Q& (recvS PQA)   (sendS m PQB) = sendS m (sim& (P& m) Q& (PQA m) PQB)
sim&L (ΠS-D-D P&) Q& (recvS PQA)   (recvD PQB)   = recvD λ m → sim& (P& m) Q& (PQA m) (PQB m)
sim&L (ΠS-D-D P&) Q& (recvS PQA)   (sendD m PQB) = sendD m (sim& (P& m) Q& (PQA m) PQB)
sim&L (ΣDΠDΣS P&) Q& (sendD m PQA) (recvD PQB)   = sendS m (sim& (P& m) Q& PQA (PQB m))
sim&L &end Q& PQA ()

{-
sim&R (ΠDΣDΣS P&) Q& (recvD PQA)   (sendD m PQB) = ?
sim&R (ΠDΠDΠD P&) Q& (recvD PQA)   (recvD PQB)   = ? -- recvD λ m → sim& (P& m) Q& (PQA m) (PQB m)
sim&R (ΠS-S-S P&) Q& (recvS PQA)   (recvS PQB)   = ? -- recvS λ m → sim& (P& m) Q& (PQA m) (PQB m)
sim&R (ΠS-S-S P&) Q& (recvS PQA)   (sendS m PQB) = ? -- sendS m (sim& (P& m) Q& (PQA m) PQB)
sim&R (ΠS-D-D P&) Q& (recvS PQA)   (recvD PQB)   = ? -- recvD λ m → sim& (P& m) Q& (PQA m) (PQB m)
sim&R (ΠS-D-D P&) Q& (recvS PQA)   (sendD m PQB) = ? -- sendD m (sim& (P& m) Q& (PQA m) PQB)
sim&R (ΣDΠDΣS P&) Q& (sendD m PQA) (recvD PQB)   = ? -- sendS m (sim& (P& m) Q& PQA (PQB m))
sim&R end& Q& PQA PQB = ?
-}
-}

sim-id : ∀ P → Sim (dual P) P
sim-id end = end
sim-id (mk Π' S A B) = right (recvS (λ x → left (sendS x (sim-id (B x)))))
sim-id (mk Π' D A B) = right (recvD (λ x → left (sendD x (sim-id (B x)))))
sim-id (mk Σ' S A B) = left (recvS (λ x → right (sendS x (sim-id (B x)))))
sim-id (mk Σ' D A B) = left (recvD (λ x → right (sendD x (sim-id (B x)))))

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
sim-compRL (S DΠΣ x₁) (recvS x) (sendS x₂ x₃) = sim-comp (x₁ x₂) (x x₂) x₃
sim-compRL (D DΠΣ x₁) (recvD x) (sendD x₂ x₃) = sim-comp (x₁ x₂) (x x₂) x₃
sim-compRL (S DΣΠ x)  (sendS x₁ x₂) (recvS x₃) = sim-comp (x x₁) x₂ (x₃ x₁)
sim-compRL (D DΣΠ x)  (sendD x₁ x₂) (recvD x₃) = sim-comp (x x₁) x₂ (x₃ x₁)

sim-compL Q-Q' (recvD PQ) QR = recvD (λ m → sim-comp Q-Q' (PQ m) QR)
sim-compL Q-Q' (recvS PQ) QR = recvS (λ m → sim-comp Q-Q' (PQ m) QR)
sim-compL Q-Q' (sendD m PQ) QR = sendD m (sim-comp Q-Q' PQ QR)
sim-compL Q-Q' (sendS m PQ) QR = sendS m (sim-comp Q-Q' PQ QR)

sim-compR Q-Q' PQ (recvD QR)   = recvD (λ m → sim-comp Q-Q' PQ (QR m))
sim-compR Q-Q' PQ (recvS QR)   = recvS (λ x → sim-comp Q-Q' PQ (QR x))
sim-compR Q-Q' PQ (sendD m QR) = sendD m (sim-comp Q-Q' PQ QR)
sim-compR Q-Q' PQ (sendS m QR) = sendS m (sim-comp Q-Q' PQ QR)

{-
sim-comp : ∀ {P Q Q' R} → Dual Q Q' → Sim P Q → Sim Q' R → Sim P R
sim-comp Q-Q' (left (recvD PQ)) QR = left (recvD (λ m → sim-comp Q-Q' (PQ m) QR))
sim-comp Q-Q' (left (recvS PQ)) QR = left (recvS (λ m → sim-comp Q-Q' (PQ m) QR))
sim-comp Q-Q' (left (sendD m PQ)) QR = left (sendD m (sim-comp Q-Q' PQ QR))
sim-comp Q-Q' (left (sendS m PQ)) QR = left (sendS m (sim-comp Q-Q' PQ QR))
sim-comp end (right ()) (left x₁)
sim-comp end end QR = QR
sim-comp end PQ end = PQ
sim-comp (ΠΣ'S Q-Q') (right (recvS PQ)) (left (sendS m QR)) = sim-comp (Q-Q' m) (PQ m) QR
sim-comp (ΠΣ'D Q-Q') (right (recvD PQ)) (left (sendD m QR)) = sim-comp (Q-Q' m) (PQ m) QR
sim-comp (ΣΠ'S Q-Q') (right (sendS m PQ)) (left (recvS QR)) = sim-comp (Q-Q' m) PQ (QR m)
sim-comp (ΣΠ'D Q-Q') (right (sendD m PQ)) (left (recvD QR)) = sim-comp (Q-Q' m) PQ (QR m)
sim-comp Q-Q' PQ (right (recvD QR)) = right (recvD (λ m → sim-comp Q-Q' PQ (QR m)))
sim-comp Q-Q' PQ (right (recvS QR)) = right (recvS (λ x → sim-comp Q-Q' PQ (QR x)))
sim-comp Q-Q' PQ (right (sendD m QR)) = right (sendD m (sim-comp Q-Q' PQ QR))
sim-comp Q-Q' PQ (right (sendS m QR)) = right (sendS m (sim-comp Q-Q' PQ QR))
-}

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

sim-symL (recvD PQ)   = recvD (λ m → !ˢ (PQ m))
sim-symL (recvS PQ)   = recvS (λ m → !ˢ (PQ m))
sim-symL (sendD m PQ) = sendD m (!ˢ PQ)
sim-symL (sendS m PQ) = sendS m (!ˢ PQ)

sim-symR (recvD PQ)   = recvD (λ m → !ˢ (PQ m))
sim-symR (recvS PQ)   = recvS (λ m → !ˢ (PQ m))
sim-symR (sendD m PQ) = sendD m (!ˢ PQ)
sim-symR (sendS m PQ) = sendS m (!ˢ PQ)

sim-unit : ∀ {P} → Sim end P → Process 𝟙 P
sim-unit (right (recvD P)) = do (recvD (λ m → sim-unit (P m)))
sim-unit (right (recvS P)) = do (recvS (λ m → sim-unit (P m)))
sim-unit (right (sendD m P)) = do (sendD m (sim-unit P))
sim-unit (right (sendS m P)) = do (sendS m (sim-unit P))
sim-unit end = end 0₁

module _ where

  mod₁ : ∀ {A A' B : ★} → (A → A') → A × B → A' × B
  mod₁ = λ f → Data.Product.map f id

  mod₂ : ∀ {A B B' : ★} → (B → B') → A × B → A × B'
  mod₂ = λ f → Data.Product.map id f

  trace : ∀ {P P' Q Q'} → Dual P P' → Dual Q Q' →  Sim end P' → Sim P Q → Sim Q' end
        → Tele P × Tele Q
  trace (S DΠΣ x₁) Q-Q' (right (sendS x x₂)) (left (recvS x₃)) Q· = mod₁ (_,_ x) (trace (x₁ x) Q-Q' x₂ (x₃ x) Q·)
  trace (S DΣΠ x₁) Q-Q' (right (recvS x)) (left (sendS x₂ x₃)) Q· = mod₁ (_,_ x₂) (trace (x₁ x₂) Q-Q' (x x₂) x₃ Q·)
  trace (D DΠΣ x₁) Q-Q' (right (sendD x x₂)) (left (recvD x₃)) Q· = mod₁ (_,_ x) (trace (x₁ x) Q-Q' x₂ (x₃ x) Q·)
  trace (D DΣΠ x₁) Q-Q' (right (recvD x)) (left (sendD x₂ x₃)) Q· = mod₁ (_,_ x₂) (trace (x₁ x₂) Q-Q' (x x₂) x₃ Q·)
  trace P-P' (S DΠΣ x₁) ·P (right (recvS x)) (left (sendS x₂ x₃)) = mod₂ (_,_ x₂) (trace P-P' (x₁ x₂) ·P (x x₂) x₃)
  trace P-P' (S DΣΠ x₁) ·P (right (sendS x x₂)) (left (recvS x₃)) = mod₂ (_,_ x) (trace P-P' (x₁ x) ·P x₂ (x₃ x))
  trace P-P' (D DΠΣ x₁) ·P (right (recvD x)) (left (sendD x₂ x₃)) = mod₂ (_,_ x₂) (trace P-P' (x₁ x₂) ·P (x x₂) x₃)
  trace P-P' (D DΣΠ x₁) ·P (right (sendD x x₂)) (left (recvD x₃)) = mod₂ (_,_ x) (trace P-P' (x₁ x) ·P x₂ (x₃ x))
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
  (funExtD : ∀ {a}{b}{A : ★_ a}{B : A → ★_ b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g)
  (funExtS : ∀ {a}{b}{A : ★_ a}{B : ..(_ : A) → ★_ b}{f g : ..(x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g)
  where

  Dual-sym-sym : ∀ {P Q} (P-Q : Dual P Q) → P-Q ≡ Dual-sym (Dual-sym P-Q)
  Dual-sym-sym end = refl
  Dual-sym-sym (S DΠΣ x) = cong (S DΠΣ) (funExtS (λ y → Dual-sym-sym (x y)))
  Dual-sym-sym (D DΠΣ x) = cong (D DΠΣ) (funExtD (λ y → Dual-sym-sym (x y)))
  Dual-sym-sym (S DΣΠ x) = cong (S DΣΠ) (funExtS (λ y → Dual-sym-sym (x y)))
  Dual-sym-sym (D DΣΠ x) = cong (D DΣΠ) (funExtD (λ y → Dual-sym-sym (x y)))

module _
  (funExtD : ∀ {a}{b}{A : ★_ a}{B : A → ★_ b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g)
  (funExtS : ∀ {a}{b}{A : ★_ a}{B : ..(_ : A) → ★_ b}{f g : ..(x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g)
  where
  sim-comp-assoc-end : ∀ {P P' Q Q' R}(P-P' : Dual P P')(Q-Q' : Dual Q Q')
    (øP : Sim end P)(PQ : Sim P' Q)(QR : Sim Q' R)
    → sim-comp Q-Q' (sim-comp P-P' øP PQ) QR
    ≡ sim-comp P-P' øP (sim-comp Q-Q' PQ QR)
  sim-comp-assoc-end (S DΠΣ x₁) Q-Q' (right (recvS x)) (left (sendS x₂ x₃)) QR
    = sim-comp-assoc-end (x₁ x₂) Q-Q' (x x₂) x₃ QR
  sim-comp-assoc-end (D DΠΣ x₁) Q-Q' (right (recvD x)) (left (sendD x₂ x₃)) QR
    = sim-comp-assoc-end (x₁ x₂) Q-Q' (x x₂) x₃ QR
  sim-comp-assoc-end (S DΣΠ x) Q-Q' (right (sendS x₁ x₂)) (left (recvS x₃)) QR
    = sim-comp-assoc-end (x x₁) Q-Q' x₂ (x₃ x₁) QR
  sim-comp-assoc-end (D DΣΠ x) Q-Q' (right (sendD x₁ x₂)) (left (recvD x₃)) QR
    = sim-comp-assoc-end (x x₁) Q-Q' x₂ (x₃ x₁) QR
  sim-comp-assoc-end P-P' (S DΠΣ x₁) (right øP) (right (recvS x)) (left (sendS x₂ x₃))
    = sim-comp-assoc-end P-P' (x₁ x₂) (right øP) (x x₂) x₃
  sim-comp-assoc-end P-P' (D DΠΣ x₁) (right øP) (right (recvD x)) (left (sendD x₂ x₃))
    = sim-comp-assoc-end P-P' (x₁ x₂) (right øP) (x x₂) x₃
  sim-comp-assoc-end P-P' (S DΣΠ x) (right øP) (right (sendS x₁ x₂)) (left (recvS x₃))
    = sim-comp-assoc-end P-P' (x x₁) (right øP) x₂ (x₃ x₁)
  sim-comp-assoc-end P-P' (D DΣΠ x) (right øP) (right (sendD x₁ x₂)) (left (recvD x₃))
    = sim-comp-assoc-end P-P' (x x₁) (right øP) x₂ (x₃ x₁)
  sim-comp-assoc-end P-P' Q-Q' (right øP) (right x) (right (recvD x₁))
    = cong (right ∘ recvD) (funExtD (λ m → sim-comp-assoc-end P-P' Q-Q' (right øP) (right x) (x₁ m)))
  sim-comp-assoc-end P-P' Q-Q' (right øP) (right x) (right (recvS x₁))
    = cong (right ∘ recvS) (funExtS (λ m → sim-comp-assoc-end P-P' Q-Q' (right øP) (right x) (x₁ m)))
  sim-comp-assoc-end P-P' Q-Q' (right øP) (right x) (right (sendD x₁ x₂))
    = cong (right ∘ sendD x₁) (sim-comp-assoc-end P-P' Q-Q' (right øP) (right x) x₂)
  sim-comp-assoc-end P-P' Q-Q' (right øP) (right x) (right (sendS x₁ x₂))
    = cong (right ∘ sendS x₁) (sim-comp-assoc-end P-P' Q-Q' (right øP) (right x) x₂)
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
  (funExtD : ∀ {a}{b}{A : ★_ a}{B : A → ★_ b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g)
  (funExtS : ∀ {a}{b}{A : ★_ a}{B : ..(_ : A) → ★_ b}{f g : ..(x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g)
  where

  sim-!! : ∀ {P Q}(PQ : Sim P Q) → PQ ≡ !ˢ (!ˢ PQ)
  sim-!! (left (recvD x))    = cong (left ∘ recvD) (funExtD λ m → sim-!! (x m))
  sim-!! (left (recvS x))    = cong (left ∘ recvS) (funExtS λ m → sim-!! (x m))
  sim-!! (left (sendD x x₁)) = cong (left ∘ sendD x) (sim-!! x₁)
  sim-!! (left (sendS x x₁)) = cong (left ∘ sendS x) (sim-!! x₁)
  sim-!! (right (recvD x))    = cong (right ∘ recvD) (funExtD λ m → sim-!! (x m))
  sim-!! (right (recvS x))    = cong (right ∘ recvS) (funExtS λ m → sim-!! (x m))
  sim-!! (right (sendD x x₁)) = cong (right ∘ sendD x) (sim-!! x₁)
  sim-!! (right (sendS x x₁)) = cong (right ∘ sendS x) (sim-!! x₁)
  sim-!! end = refl

  sim-comp-!-end : ∀ {Q Q' R}(Q-Q' : Dual Q Q')(·Q : Sim end Q)(Q'R : Sim Q' R)
    → sim-comp (Dual-sym Q-Q') (!ˢ Q'R) (!ˢ ·Q) ≡ !ˢ (sim-comp Q-Q' ·Q Q'R)
  sim-comp-!-end (S DΠΣ x₁) (right (recvS x)) (left (sendS x₂ x₃)) = sim-comp-!-end (x₁ x₂) (x x₂) x₃
  sim-comp-!-end (D DΠΣ x₁) (right (recvD x)) (left (sendD x₂ x₃)) = sim-comp-!-end (x₁ x₂) (x x₂) x₃
  sim-comp-!-end (S DΣΠ x) (right (sendS x₁ x₂)) (left (recvS x₃)) = sim-comp-!-end (x x₁) x₂ (x₃ x₁)
  sim-comp-!-end (D DΣΠ x) (right (sendD x₁ x₂)) (left (recvD x₃)) = sim-comp-!-end (x x₁) x₂ (x₃ x₁)
  sim-comp-!-end Q-Q' (right x) (right (recvD x₁))
    = cong (left ∘ recvD) (funExtD (λ x₂ → sim-comp-!-end Q-Q' (right x) (x₁ x₂)))
  sim-comp-!-end Q-Q' (right x) (right (recvS x₁))
    = cong (left ∘ recvS) (funExtS (λ x₂ → sim-comp-!-end Q-Q' (right x) (x₁ x₂)))
  sim-comp-!-end Q-Q' (right x) (right (sendD x₁ x₂))
    = cong (left ∘ sendD x₁) (sim-comp-!-end Q-Q' (right x) x₂)
  sim-comp-!-end Q-Q' (right x) (right (sendS x₁ x₂))
    = cong (left ∘ sendS x₁) (sim-comp-!-end Q-Q' (right x) x₂)
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
    ≡⟨ cong (!ˢ ∘ !ˢ) (sym (sim-comp-assoc-end funExtD funExtS R'-R (Dual-sym Q-Q') øR' (!ˢ Q'R) (!ˢ PQ))) ⟩
      !ˢ
        (!ˢ
         (sim-comp (Dual-sym Q-Q') (sim-comp R'-R øR' (!ˢ Q'R)) (!ˢ PQ)))
    ≡⟨ cong !ˢ (sym (sim-comp-!-end (Dual-sym Q-Q') (sim-comp R'-R øR' (!ˢ Q'R)) (!ˢ PQ))) ⟩
      !ˢ
        (sim-comp (Dual-sym (Dual-sym Q-Q')) (!ˢ (!ˢ PQ))
         (!ˢ (sim-comp R'-R øR' (!ˢ Q'R))))
    ≡⟨ cong₂ (λ X Y → !ˢ (sim-comp X Y (!ˢ (sim-comp R'-R øR' (!ˢ Q'R)))))
         (sym (Dual-sym-sym funExtD funExtS Q-Q')) (sym (sim-!! PQ)) ⟩
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
