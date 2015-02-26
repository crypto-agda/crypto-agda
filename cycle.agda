{-# OPTIONS --with-K #-}
open import Function.NP
open import Data.Nat.Base
open import Data.List using ([]; _∷_; List; length)
open import Data.List.Any
open Membership-≡ using () renaming (_∈_ to _∈ᴸ_)
open import Data.Product.NP
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.NP
import Data.Stream as S
open S using (here; there; Stream) renaming (_∈_ to _∈ˢ_)
open import Level.NP

module cycle (let ℓ = ₀){-a-} (A : Set ℓ) (f : Endo A) where

is-prop : ∀ {ℓ} → Set ℓ → Set ℓ
is-prop A = (a b : A) → a ≡ b

is-contr : ∀ {ℓ} → Set ℓ → Set ℓ
is-contr A = ∃ λ (a : A) → (b : A) → a ≡ b

foldl : {A : Set} → A → (A → A) → ℕ → A
foldl z s zero    = z
foldl z s (suc n) = foldl (s z) s n

fold-factor : ∀ {A : Set} {z : A} {s} n → s (fold z s n) ≡ fold (s z) s n
fold-factor zero = refl
fold-factor {s = s} (suc n) = ap s (fold-factor n)

fold-foldl : ∀ {A : Set} {z : A} {s} n → fold z s n ≡ foldl z s n
fold-foldl zero = refl
fold-foldl (suc n) = fold-factor n ∙ fold-foldl n

_$⟨_⟩l_ : {A : Set} → Endo A → ℕ → Endo A
_$⟨_⟩l_ f n z = foldl z f n

infixr 5 _∷_
{-
    p : x ↦* f (f (f x))
    p = (x ∷ f x ∷ f (f x) ∷ [ f (f (f x)) ])
-}
data _↦*_ : (x z : A) → Set ℓ where
  [_] : (x : A) → x ↦* x
  _∷_ : (x : A) {z : A} → f x ↦* z → x ↦* z

↺ : (x : A) → Set ℓ
↺ x = f x ↦* x

listC : ∀ {x z} → x ↦* z → List A
listC [ y ] = []
listC (y ∷ c) = y ∷ listC c

listC' : ∀ {x z} → x ↦* z → List A
listC' [ y ] = y ∷ []
listC' (y ∷ c) = y ∷ listC' c

lenC : ∀ {x z} → x ↦* z → ℕ
lenC = length ∘ listC

C-specl : ∀ {x z}(c : x ↦* z) → f $⟨ lenC c ⟩l x ≡ z
C-specl [ _ ]   = refl
C-specl (_ ∷ c) = C-specl c

uniq-↦* : (x z : A) → Set _
uniq-↦* x z = is-contr (x ↦* z)

∈iterate→↦* : ∀ {x z} → z ∈ˢ S.iterate f x → x ↦* z
∈iterate→↦* here = [ _ ]
∈iterate→↦* (there p) = _ ∷ ∈iterate→↦* p

↦*→∈iterate : ∀ {x z} → x ↦* z → z ∈ˢ S.iterate f x
↦*→∈iterate [ _ ] = here
↦*→∈iterate (_ ∷ c) = there (↦*→∈iterate c)

infix 0 _∈_ _∉_ _∈?_ _∈!_ _⊆ᴸ_ _ᴸ⊆_

data _∈_ (y : A){z : A} : {x : A} → x ↦* z → Set ℓ where
  here  : ∀ {c : y ↦* z} → y ∈ c
  there : ∀ {x}{c : f x ↦* z}(p : y ∈ c) → y ∈ x ∷ c
module ∈ = _∈_

there-inj : ∀ {x y z}{c : f x ↦* z}{p q : y ∈ c} → ∈.there p ≡ there q → p ≡ q
there-inj refl = refl

_∉_ : {x : A}(y : A){z : A} → x ↦* z → Set ℓ
y ∉ c = ¬(y ∈ c)

-- `z ∈? c`, `z` occurs at most once in `c`.
_∈?_ : {x : A} (y : A) {z : A} → x ↦* z → Set _ 
y ∈? c = is-prop (y ∈ c)

-- `z ∈! c`, z occurs exactly once in `c`.
_∈!_ : {x : A} (y : A) {z : A} → x ↦* z → Set _ 
z ∈! c = is-contr (z ∈ c)

module _ {x z x' z' : A}(c : x ↦* z)(c' : x' ↦* z') where
  infix 0 _⊆_ _⊆?_ _?⊆_ _?⊆?_ _⊆!_ _!⊆_ _!⊆!_ _?⊆!_ _!⊆?_
  _⊆_   = {m : A} → m ∈  c → m ∈  c'
  _!⊆!_ = {m : A} → m ∈! c → m ∈! c'
  _⊆!_  = {m : A} → m ∈  c → m ∈! c'
  _!⊆_  = {m : A} → m ∈! c → m ∈  c'
  _?⊆?_ = {m : A} → m ∈? c → m ∈? c'
  _⊆?_  = {m : A} → m ∈  c → m ∈? c'
  _?⊆_  = {m : A} → m ∈? c → m ∈  c'
  _?⊆!_ = {m : A} → m ∈? c → m ∈! c'
  _!⊆?_ = {m : A} → m ∈! c → m ∈? c'

_⊆ᴸ_ : {x z : A}(c : x ↦* z)(l : List A) → Set ℓ
c ⊆ᴸ l = ∀ {m : A} → m ∈ c → m ∈ᴸ l

_ᴸ⊆_ : (l : List A){x z : A}(c : x ↦* z) → Set ℓ
l ᴸ⊆ c = ∀ {m : A} → m ∈ᴸ l → m ∈ c

∈ᴸ-listC' : ∀ {x z}(c : x ↦* z) → x ∈ᴸ (listC' c)
∈ᴸ-listC' [ _ ]   = here refl
∈ᴸ-listC' (_ ∷ _) = here refl

⊆ᴸ-refl : ∀ {x z}{c : x ↦* z} → c ⊆ᴸ listC' c
⊆ᴸ-refl {c = c}      here     = ∈ᴸ-listC' c
⊆ᴸ-refl {c = _ ∷ c} (there p) = there (⊆ᴸ-refl p)

ᴸ⊆-refl : ∀ {x z}{c : x ↦* z} → listC' c ᴸ⊆ c
ᴸ⊆-refl {c = [ _ ]} (here refl) = here
ᴸ⊆-refl {c = [ _ ]} (there ())
ᴸ⊆-refl {c = _ ∷ _} (here refl) = here
ᴸ⊆-refl {c = _ ∷ _} (there p)   = there (ᴸ⊆-refl p)

module _ {x z : A}{c : x ↦* z} where
  module _ {y : A} where
    ∈+∈?→∈! : y ∈ c → y ∈? c → y ∈! c
    ∈+∈?→∈! p p? = p , p? p

    ∈!→∈ : y ∈! c → y ∈ c
    ∈!→∈ = fst

    ∈!→∈? : y ∈! c → y ∈? c
    ∈!→∈? (p , p-prop) q r = ! p-prop q ∙ p-prop r

  refl-!⊆ : c !⊆ c
  refl-!⊆ = ∈!→∈

  refl-!⊆? : c !⊆? c
  refl-!⊆? = ∈!→∈?

  refl-⊆ : c ⊆ c
  refl-⊆ = id

  refl-?⊆? : c ?⊆? c
  refl-?⊆? = id

  refl-!⊆! : c !⊆! c
  refl-!⊆! = id

last∈ : {x z : A}(c : x ↦* z) → z ∈ c
last∈ [ _ ]   = here
last∈ (_ ∷ c) = there (last∈ c)

infixr 4 _++_
_++_ : {x y z : A}(c : x ↦* y)(c' : y ↦* z) → x ↦* z
[ _ ]   ++ c' = c'
(m ∷ c) ++ c' = m ∷ (c ++ c')

shift : {x y z : A}(c : x ↦* y)(c' : y ↦* z) → c' ⊆ (c ++ c')
shift [ z ]   c' p = p
shift (y ∷ c) c' p = there (shift c c' p)

inject : {x y z : A}(c : x ↦* y)(c' : y ↦* z) → c ⊆ (c ++ c')
inject c c'   here     = here
inject ._ c' (there p) = there (inject _ c' p)

drop : {x y z : A}{c : x ↦* z}(p : y ∈ c) → y ↦* z
drop {c = c}  here     = c
drop         (there p) = drop p

take : {x y z : A}{c : x ↦* z}(p : y ∈ c) → x ↦* y
take  here     = [ _ ]
take (there p) = _ ∷ take p

take++drop : ∀ {x z : A}{c : x ↦* z}(p : z ∈ c) → take p ++ drop p ≡ c
take++drop here = refl
take++drop (there p) = ap (_∷_ _) (take++drop p)

∷-?⊆? : {x z : A}{c : f x ↦* z} → x ∷ c ?⊆? c
∷-?⊆? ch p q = there-inj (ch (there p) (there q))

is-chain : {x z : A} → x ↦* z → Set _
is-chain c = ∀ {y} → y ∈? c

is-cycle : {x : A} → ↺ x → Set _
is-cycle = is-chain

_↦C_ : (x z : A) → Set ℓ
x ↦C z = Σ (x ↦* z) is-chain

-- a cycle of even size is split in two, a cycle of odd size is reordered
-- [1] --> [1]
-- [1,2] --> [1],[2]
-- [1,2,3] --> [1,3,2] --> [1,2,3]
-- [1,2,3,4] --> [1,2],[3,4] --> [1],[2],[3],[4]
-- [1,2,3,4,5] --> [1,3,5,2,4] --> [1,5,4,3,2]

module _ {x z : A} where
  is-club : (c : x ↦* z) → Set ℓ
  is-club c = (is-chain c) × (f z ∈ c)

  chain-∷ : {c : f x ↦* z} → is-chain (x ∷ c) → is-chain c
  chain-∷ ch p q = ∷-?⊆? ch p q

  module _ {c : x ↦* z} where
    chain→⊆! : is-chain c → c ⊆! c
    chain→⊆! ch p = p , ch p

    club→chain : is-club c → is-chain c
    club→chain = fst

    club→∈ : is-club c → f z ∈ c
    club→∈ = snd

    club→∈! : is-club c → f z ∈! c
    club→∈! (ch , p) = chain→⊆! ch p

↺-club : ∀ {x}{c : ↺ x} → is-chain c → is-club c
↺-club ch = ch , here


-- -}
-- -}
-- -}
-- -}
-- -}
