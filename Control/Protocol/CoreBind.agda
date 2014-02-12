-- {-# OPTIONS --without-K #-}
open import Coinduction
open import Function.NP
open import Type
open import Level
open import Data.Product
open import Data.One

open import Relation.Binary.PropositionalEquality

module Control.Protocol.CoreBind where
open import Control.Strategy renaming (Strategy to Client) public

data Inf : ★ where
  mu nu : Inf

data Proto : ★₁ where
  end : Proto
  Π' Σ' : (A : ★)(B : A → Proto) → Proto
  later : Inf → ∞ Proto → Proto

{-
Tele : Proto → ★
Tele end = 𝟙
Tele (Π' A B) = Σ A λ x → Tele (B x)
Tele (Σ' A B) = Σ A λ x → Tele (B x)
Tele (later i P) = ?

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
A ×' B = Σ' A λ _ → B

_→'_ : Set → Proto → Proto
A →' B = Π' A λ _ → B

dualInf : Inf → Inf
dualInf mu = nu
dualInf nu = mu

dual : Proto → Proto
dual end = end
dual (Π' A B) = Σ' A (λ x → dual (B x))
dual (Σ' A B) = Π' A (λ x → dual (B x))
dual (later i P) = later (dualInf i) (♯ (dual (♭ P)))

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
elInf : Inf → ★₁ → ★₁
elInf mu x = x
elInf nu x = ∞ x

data ProcessF (this : Proto → ★₁): Proto → ★₁ where
  send : ∀ {M P} (m : M) → this (P m) → ProcessF this (Σ' M P)
  recv : ∀ {M P} → ((m : M) → this (P m)) → ProcessF this (Π' M P)
  latr : ∀ {P} i → elInf i (this (♭ P)) → ProcessF this (later i P)

data Process (A : ★) : Proto → ★₁ where
  do  : ∀ {P} → ProcessF (Process A) P → Process A P
  end : A → Process A end

data Sim : Proto → Proto → ★₁ where
  left  : ∀ {P Q} → ProcessF (flip Sim Q) P → Sim P Q
  right : ∀ {P Q} → ProcessF (Sim P) Q → Sim P Q
  end   : Sim end end

_⟹_ : Proto → Proto → ★₁
P ⟹ Q = Sim (dual P) Q

_⟹ᴾ_ : Proto → Proto → ★₁
P ⟹ᴾ Q = ∀ {A} → Process A (dual P) → Process A Q

sim-id : ∀ P → Sim (dual P) P
sim-id end = end
sim-id (Π' A B) = right (recv (λ m → left (send m (sim-id (B m)))))
sim-id (Σ' A B) = left (recv (λ m → right (send m (sim-id (B m)))))
sim-id (later mu P) = right (latr mu (left (latr nu (♯ sim-id (♭ P)))))
sim-id (later nu P) = left (latr mu (right (latr nu (♯ (sim-id (♭ P))))))

sim-comp : ∀ {P Q R} → Sim P Q → Sim (dual Q) R → Sim P R
sim-comp (left (send m x)) QR = left (send m (sim-comp x QR))
sim-comp (left (recv x)) QR = left (recv (λ m → sim-comp (x m) QR))
sim-comp (left (latr mu x)) QR = left (latr mu (sim-comp x QR))
sim-comp (left (latr nu x)) QR = left (latr nu (♯ sim-comp (♭ x) QR))
sim-comp (right (send m x)) (left (recv x₁)) = sim-comp x (x₁ m)
sim-comp (right (recv x)) (left (send m x₁)) = sim-comp (x m) x₁
sim-comp (right (latr mu x)) (left (latr .nu x₁)) = sim-comp x (♭ x₁)
sim-comp (right (latr nu x)) (left (latr .mu x₁)) = sim-comp (♭ x) x₁
sim-comp PQ (right (send m x)) = right (send m (sim-comp PQ x))
sim-comp PQ (right (recv x)) = right (recv (λ m → sim-comp PQ (x m)))
sim-comp PQ (right (latr mu x)) = right (latr mu (sim-comp PQ x))
sim-comp PQ (right (latr nu x)) = right (latr nu (♯ sim-comp PQ (♭ x)))
sim-comp end QR = QR
{-
sim-comp end QR = QR
sim-comp (right (send m x)) (left (recv x₁)) = sim-comp x (x₁ m)
sim-comp (right (recv x)) (left (send m x₁)) = sim-comp (x m) x₁
sim-comp (left (send m x)) QR = left (send m (sim-comp x QR))
sim-comp (left (recv x)) QR = left (recv (λ m → sim-comp (x m) QR))
sim-comp PQ (right (send m₁ x₁)) = right (send m₁ (sim-comp PQ x₁))
sim-comp PQ (right (recv x₁)) = right (recv (λ m₁ → sim-comp PQ (x₁ m₁)))

⟹-comp : ∀ {P Q R} → P ⟹ Q → Q ⟹ R → P ⟹ R
⟹-comp = sim-comp

sim-sym : ∀ {P Q} → Sim P Q → Sim Q P
sim-sym (left (send m x)) = right (send m (sim-sym x))
sim-sym (left (recv x)) = right (recv (λ m → sim-sym (x m)))
sim-sym (right (send m x)) = left (send m (sim-sym x))
sim-sym (right (recv x)) = left (recv (λ m → sim-sym (x m)))
sim-sym end = end

sim-unit : ∀ {P} → Sim end P → Process 𝟙 P
sim-unit (left ())
sim-unit (right (send m x)) = do (send m (sim-unit x))
sim-unit (right (recv x)) = do (recv (λ m → sim-unit (x m)))
sim-unit end = end 0₁

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
{-

module _ (funExt : ∀ {a}{b}{A : ★_ a}{B : A → ★_ b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g) where
  apply-comp : ∀ {P Q R A}(PQ : Sim P Q)(QR : Sim (dual Q) R)(p : Process A (dual P)) → apply-sim (sim-comp PQ QR) p ≡ apply QR (apply-sim PQ p)
  apply-comp (left (send m x)) QR (do (recv x₁)) = apply-comp x QR (x₁ m)
  apply-comp (left (recv x)) QR (do (send m x₁)) = apply-comp (x m) QR x₁
  apply-comp (right (send m x)) (left (recv x₁)) p = apply-comp x (x₁ m) p
  apply-comp (right (send m x)) (right (recv x₁)) p = cong (λ X → do (recv X))
    (funExt (λ m' → apply-comp (right (send m x)) (x₁ m') p))
  apply-comp (right (send m x)) (right (send m₁ x₁)) p
    rewrite apply-comp (right (send m x)) x₁ p = {!!}
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
