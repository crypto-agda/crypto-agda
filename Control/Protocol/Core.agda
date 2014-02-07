open import Function
open import Type
open import Level
open import Data.Product

module Control.Protocol.Core where
open import Control.Strategy renaming (Strategy to Client) public

Π : ∀ {ℓ ℓ'}(A : ★_ ℓ)(B : A → ★_ ℓ') → ★_ (ℓ ⊔ ℓ')
Π A B = (x : A) → B x

data Proto : ★₁ where
  end : Proto
  Π' Σ' : (A : ★)(B : A → Proto) → Proto
  Client' Server' : (Q : ★)(R : Q → ★)(B : Proto) → Proto

_×'_ : Set → Proto → Proto
A ×' B = Σ' A λ _ → B

_→'_ : Set → Proto → Proto
A →' B = Π' A λ _ → B

dual : Proto → Proto
dual end = end
dual (Π' A B) = Σ' A (λ x → dual (B x))
dual (Σ' A B) = Π' A (λ x → dual (B x))
dual (Client' Q R B) = Server' Q R (dual B)
dual (Server' Q R B) = Client' Q R (dual B)

module _ (Q : ★)(R : Q → ★)(A : ★) where
  record Server : ★
  record ServerResponse (q : Q) : ★

  record Server where
    coinductive
    constructor _,_
    field
      srv-done : A
      srv-ask  : ∀ q → ServerResponse q

  record ServerResponse q where
    constructor _,_
    field
      srv-resp : R q
      srv-cont : Server
open Server public
open ServerResponse public

Server′ : (Q R A : ★) → ★
Server′ Q R = Server Q (const R)

module _ {Q A B : ★}{R : Q → ★} where
  Server-Com : Server Q R A → Client Q R B → A × B
  Server-Com server (ask q? cont) = let sr = srv-ask server q? in Server-Com (srv-cont sr) (cont (srv-resp sr))
  Server-Com server (done x) = srv-done server , x
--

module _ X where
  El : Proto → ★
  El end = X
  El (Π' A B) = Π A λ x → El (B x)
  El (Σ' A B) = Σ A λ x → El (B x)
  El (Client' Q R B) = Client Q R (El B)
  El (Server' Q R B) = Server Q R (El B)


module _ {A B} where
  com : (P : Proto) → El A P → El B (dual P) → A × B
  com end a b = a , b
  com (Π' A B) f (x , y) = com (B x) (f x) y
  com (Σ' A B) (x , y) f = com (B x) y (f x)
  com (Client' Q R P) c s = let (x , y) = Server-Com s c in com P y x
  com (Server' Q R P) s c = let (x , y) = Server-Com s c in com P x y
