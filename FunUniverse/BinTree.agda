module FunUniverse.BinTree where

open import Type hiding (★)
open import Function
open import Data.Nat.NP using (ℕ; zero; suc; _≤_; s≤s; _+_; module ℕ≤; module ℕ°)
open import Data.Nat.Properties
open import Data.Bool
open import Data.Vec using (_++_)
open import Data.Bits
--import Data.Bits.Search as Search
--open Search.SimpleSearch
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Composition.Horizontal
open import Composition.Vertical
open import Composition.Forkable

data Tree {a} (A : ★ a) : ℕ → ★ a where
  leaf : ∀ {n} → A → Tree A n
  fork : ∀ {n} (left right : Tree A n) → Tree A (suc n)

fromFun : ∀ {n a} {A : ★ a} → (Bits n → A) → Tree A n
fromFun {zero}  f = leaf (f [])
fromFun {suc n} f = fork (fromFun (f ∘ 0∷_)) (fromFun (f ∘ 1∷_))

toFun : ∀ {n a} {A : ★ a} → Tree A n → Bits n → A
toFun (leaf x) _ = x
toFun (fork left right) (b ∷ bs) = toFun (if b then right else left) bs

toFun∘fromFun : ∀ {n a} {A : ★ a} (f : Bits n → A) → toFun (fromFun f) ≗ f
toFun∘fromFun {zero}  f []        = refl
toFun∘fromFun {suc n} f (false {-0b-} ∷ bs) = toFun∘fromFun {n} (f ∘ 0∷_) bs
toFun∘fromFun {suc n} f (true  {-1b-} ∷ bs) = toFun∘fromFun {n} (f ∘ 1∷_) bs

fold : ∀ {n a} {A : ★ a} (op : A → A → A) → Tree A n → A
fold _   (leaf x) = x
fold _·_ (fork t₀ t₁) = fold _·_ t₀ · fold _·_ t₁

{-
search≡fold∘fromFun : ∀ {n a} {A : ★ a} op (f : Bits n → A) → search op f ≡ fold op (fromFun f)
search≡fold∘fromFun {zero}  op f = refl
search≡fold∘fromFun {suc n} op f
  rewrite search≡fold∘fromFun op (f ∘ 0∷_)
        | search≡fold∘fromFun op (f ∘ 1∷_) = refl
-}

leafⁿ : ∀ {n a} {A : ★ a} → A → Tree A n
leafⁿ {zero}  x = leaf x
leafⁿ {suc n} x = fork t t where t = leafⁿ x

expand : ∀ {n a} {A : ★ a} → Tree A n → Tree A n
expand (leaf x) = leafⁿ x
expand (fork t₀ t₁) = fork (expand t₀) (expand t₁)

fromConst≡leafⁿ : ∀ {n a} {A : ★ a} (x : A) → fromFun (const x) ≡ leafⁿ {n} x
fromConst≡leafⁿ {zero}  _ = refl
fromConst≡leafⁿ {suc n} x rewrite fromConst≡leafⁿ {n} x = refl

fromFun∘toFun : ∀ {n a} {A : ★ a} (t : Tree A n) → fromFun (toFun t) ≡ expand t
fromFun∘toFun (leaf x) = fromConst≡leafⁿ x
fromFun∘toFun (fork t₀ t₁) = cong₂ fork (fromFun∘toFun t₀) (fromFun∘toFun t₁)

lookup : ∀ {n a} {A : ★ a} → Bits n → Tree A n → A
lookup = flip toFun

map : ∀ {n a b} {A : ★ a} {B : ★ b} → (A → B) → Tree A n → Tree B n
map f (leaf x) = leaf (f x)
map f (fork t₀ t₁) = fork (map f t₀) (map f t₁)

weaken≤ : ∀ {m n a} {A : ★ a} → m ≤ n → Tree A m → Tree A n
weaken≤ _       (leaf x)          = leaf x
weaken≤ (s≤s p) (fork left right) = fork (weaken≤ p left) (weaken≤ p right)

m≤n+m : ∀ m n → m ≤ n + m
m≤n+m m n = ℕ≤.trans (m≤m+n m n) (ℕ≤.reflexive (ℕ°.+-comm m n))

weaken+ : ∀ n {m a} {A : ★ a} → Tree A m → Tree A (n + m)
weaken+ n = weaken≤ (m≤n+m _ n)

_>>=_ : ∀ {n₁ n₂ a b} {A : ★ a} {B : ★ b}
        → Tree A n₁ → (A → Tree B n₂) → Tree B (n₁ + n₂)
leaf {n} x >>= f = weaken+ n (f x)
fork ℓ r   >>= f = fork (ℓ >>= f) (r >>= f)

join : ∀ {c₁ c₂ a} {A : ★ a} → Tree (Tree A c₂) c₁ → Tree A (c₁ + c₂)
join t = t >>= id

_→ᵗ_ : (i o : ℕ) → ★₀
i →ᵗ o = Tree (Bits o) i

_>>>_ : ∀ {m n a} {A : ★ a} → Tree (Bits m) n → Tree A m → Tree A n
f >>> g = map (flip lookup g) f

_***_ : ∀ {i₀ i₁ o₀ o₁} → i₀ →ᵗ o₀ → i₁ →ᵗ o₁ → (i₀ + i₁) →ᵗ (o₀ + o₁)
(f *** g) = join (map (λ xs → map (_++_ xs) g) f)

hcomposable : HComposable _→ᵗ_
hcomposable = mk _>>>_

vcomposable : VComposable _+_ _→ᵗ_
vcomposable = mk _***_

forkable : Forkable suc _→ᵗ_
forkable = mk fork

-- This is probably useless by now
data Rot {a} {A : ★ a} : ∀ {n} (left right : Tree A n) → ★ a where
  leaf : ∀ {n} x → Rot {n = n} (leaf x) (leaf x)
  fork : ∀ {n} {left₀ left₁ right₀ right₁ : Tree A n} →
         Rot left₀ left₁ →
         Rot right₀ right₁ →
         Rot (fork left₀ right₀) (fork left₁ right₁)
  krof : ∀ {n} {left₀ left₁ right₀ right₁ : Tree A n} →
         Rot left₀ right₁ →
         Rot right₀ left₁ →
         Rot (fork left₀ right₀) (fork left₁ right₁)

Rot-refl : ∀ {n a} {A : ★ a} → Reflexive (Rot {A = A} {n})
Rot-refl {x = leaf x} = leaf x
Rot-refl {x = fork left right} = fork Rot-refl Rot-refl

Rot-sym : ∀ {n a} {A : ★ a} → Symmetric (Rot {A = A} {n})
Rot-sym (leaf x) = leaf x
Rot-sym (fork p₀ p₁) = fork (Rot-sym p₀) (Rot-sym p₁)
Rot-sym (krof p₀ p₁) = krof (Rot-sym p₁) (Rot-sym p₀)

Rot-trans : ∀ {n a} {A : ★ a} → Transitive (Rot {A = A} {n})
Rot-trans (leaf x) q = q
Rot-trans (fork p₀ p₁) (fork q₀ q₁) = fork (Rot-trans p₀ q₀) (Rot-trans p₁ q₁)
Rot-trans (fork p₀ p₁) (krof q₀ q₁) = krof (Rot-trans p₀ q₀) (Rot-trans p₁ q₁)
Rot-trans (krof p₀ p₁) (fork q₀ q₁) = krof (Rot-trans p₀ q₁) (Rot-trans p₁ q₀)
Rot-trans (krof p₀ p₁) (krof q₀ q₁) = fork (Rot-trans p₀ q₁) (Rot-trans p₁ q₀)
