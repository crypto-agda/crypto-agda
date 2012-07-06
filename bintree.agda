module bintree where

open import Function
open import Data.Nat.NP using (ℕ; zero; suc; _≤_; s≤s; _+_; module ℕ≤; module ℕ°)
open import Data.Nat.Properties
open import Data.Bool
open import Data.Vec using (_++_)
open import Data.Bits
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import composable
open import vcomp
open import forkable

data Tree {a} (A : Set a) : ℕ → Set a where
  leaf : ∀ {n} → A → Tree A n
  fork : ∀ {n} (left right : Tree A n) → Tree A (suc n)

fromFun : ∀ {n a} {A : Set a} → (Bits n → A) → Tree A n
fromFun {zero}  f = leaf (f [])
fromFun {suc n} f = fork (fromFun (f ∘ 0∷_)) (fromFun (f ∘ 1∷_))

toFun : ∀ {n a} {A : Set a} → Tree A n → Bits n → A
toFun (leaf x) _ = x
toFun (fork left right) (b ∷ bs) = toFun (if b then right else left) bs

toFun∘fromFun : ∀ {n a} {A : Set a} (f : Bits n → A) → toFun (fromFun f) ≗ f
toFun∘fromFun {zero}  f []        = refl
toFun∘fromFun {suc n} f (false {-0b-} ∷ bs) = toFun∘fromFun {n} (f ∘ 0∷_) bs
toFun∘fromFun {suc n} f (true  {-1b-} ∷ bs) = toFun∘fromFun {n} (f ∘ 1∷_) bs

fold : ∀ {n a} {A : Set a} (op : A → A → A) → Tree A n → A
fold _   (leaf x) = x
fold _·_ (fork t₀ t₁) = fold _·_ t₀ · fold _·_ t₁

search≡fold∘fromFun : ∀ {n a} {A : Set a} op (f : Bits n → A) → search op f ≡ fold op (fromFun f)
search≡fold∘fromFun {zero}  op f = refl
search≡fold∘fromFun {suc n} op f
  rewrite search≡fold∘fromFun op (f ∘ 0∷_)
        | search≡fold∘fromFun op (f ∘ 1∷_) = refl

leafⁿ : ∀ {n a} {A : Set a} → A → Tree A n
leafⁿ {zero}  x = leaf x
leafⁿ {suc n} x = fork t t where t = leafⁿ x

expand : ∀ {n a} {A : Set a} → Tree A n → Tree A n
expand (leaf x) = leafⁿ x
expand (fork t₀ t₁) = fork (expand t₀) (expand t₁)

fromConst≡leafⁿ : ∀ {n a} {A : Set a} (x : A) → fromFun (const x) ≡ leafⁿ {n} x
fromConst≡leafⁿ {zero}  _ = refl
fromConst≡leafⁿ {suc n} x rewrite fromConst≡leafⁿ {n} x = refl

fromFun∘toFun : ∀ {n a} {A : Set a} (t : Tree A n) → fromFun (toFun t) ≡ expand t
fromFun∘toFun (leaf x) = fromConst≡leafⁿ x
fromFun∘toFun (fork t₀ t₁) = cong₂ fork (fromFun∘toFun t₀) (fromFun∘toFun t₁)

lookup : ∀ {n a} {A : Set a} → Bits n → Tree A n → A
lookup = flip toFun

map : ∀ {n a b} {A : Set a} {B : Set b} → (A → B) → Tree A n → Tree B n
map f (leaf x) = leaf (f x)
map f (fork t₀ t₁) = fork (map f t₀) (map f t₁)

weaken≤ : ∀ {m n a} {A : Set a} → m ≤ n → Tree A m → Tree A n
weaken≤ _       (leaf x)          = leaf x
weaken≤ (s≤s p) (fork left right) = fork (weaken≤ p left) (weaken≤ p right)

m≤n+m : ∀ m n → m ≤ n + m
m≤n+m m n = ℕ≤.trans (m≤m+n m n) (ℕ≤.reflexive (ℕ°.+-comm m n))

weaken+ : ∀ n {m a} {A : Set a} → Tree A m → Tree A (n + m)
weaken+ n = weaken≤ (m≤n+m _ n)

join : ∀ {c₁ c₂ a} {A : Set a} → Tree (Tree A c₂) c₁ → Tree A (c₁ + c₂)
join {c} (leaf x)          = weaken+ c x
join     (fork left right) = fork (join left) (join right)

_>>>_ : ∀ {m n a} {A : Set a} → Tree (Bits m) n → Tree A m → Tree A n
f >>> g = map (flip lookup g) f

_→ᵗ_ : (i o : ℕ) → Set
i →ᵗ o = Tree (Bits o) i

composable : Composable _→ᵗ_
composable = mk _>>>_

_***_ : ∀ {i₀ i₁ o₀ o₁} → i₀ →ᵗ o₀ → i₁ →ᵗ o₁ → (i₀ + i₁) →ᵗ (o₀ + o₁)
(f *** g) = join (map (λ xs → map (_++_ xs) g) f)

vcomposable : VComposable _+_ _→ᵗ_
vcomposable = mk _***_

forkable : Forkable suc _→ᵗ_
forkable = mk fork

data Rot {a} {A : Set a} : ∀ {n} (left right : Tree A n) → Set a where
  leaf : ∀ {n} x → Rot {n = n} (leaf x) (leaf x)
  fork : ∀ {n} {left₀ left₁ right₀ right₁ : Tree A n} →
         Rot left₀ left₁ →
         Rot right₀ right₁ →
         Rot (fork left₀ right₀) (fork left₁ right₁)
  krof : ∀ {n} {left₀ left₁ right₀ right₁ : Tree A n} →
         Rot left₀ right₁ →
         Rot right₀ left₁ →
         Rot (fork left₀ right₀) (fork left₁ right₁)

Rot-refl : ∀ {n a} {A : Set a} → Reflexive (Rot {A = A} {n})
Rot-refl {x = leaf x} = leaf x
Rot-refl {x = fork left right} = fork Rot-refl Rot-refl

Rot-sym : ∀ {n a} {A : Set a} → Symmetric (Rot {A = A} {n})
Rot-sym (leaf x) = leaf x
Rot-sym (fork p₀ p₁) = fork (Rot-sym p₀) (Rot-sym p₁)
Rot-sym (krof p₀ p₁) = krof (Rot-sym p₁) (Rot-sym p₀)

Rot-trans : ∀ {n a} {A : Set a} → Transitive (Rot {A = A} {n})
Rot-trans (leaf x) q = q
Rot-trans (fork p₀ p₁) (fork q₀ q₁) = fork (Rot-trans p₀ q₀) (Rot-trans p₁ q₁)
Rot-trans (fork p₀ p₁) (krof q₀ q₁) = krof (Rot-trans p₀ q₀) (Rot-trans p₁ q₁)
Rot-trans (krof p₀ p₁) (fork q₀ q₁) = krof (Rot-trans p₀ q₁) (Rot-trans p₁ q₀)
Rot-trans (krof p₀ p₁) (krof q₀ q₁) = fork (Rot-trans p₀ q₁) (Rot-trans p₁ q₀)

data AC {a} {A : Set a} : ∀ {m n} (left : Tree A m) (right : Tree A n) → Set a where
  ε : ∀ {n} {t : Tree A n} → AC t t

  _⁏_ : ∀ {m n o} {t : Tree A m} {u : Tree A n} {v : Tree A o} → AC t u → AC u v → AC t v

  first : ∀ {n} {left₀ left₁ right : Tree A n} →
         AC left₀ left₁ →
         AC (fork left₀ right) (fork left₁ right)

  swp : ∀ {m n} {left : Tree A m} {right : Tree A n} →
         AC (fork left right) (fork right left)

  assoc : ∀ {n} {t₀ t₁ : Tree A n} {t₂ : Tree A (suc n)} →
          AC (fork (fork t₀ t₁) t₂) (fork t₀ (fork t₁ t₂))
