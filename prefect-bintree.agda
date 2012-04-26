module prefect-bintree where

open import Function
open import Data.Nat.NP
open import Data.Bool
open import Data.Bits
open import Data.Vec using (Vec; _++_)

data Tree {a} (A : Set a) : ℕ → Set a where
  leaf : (x : A) → Tree A zero
  fork : ∀ {n} (left right : Tree A n) → Tree A (suc n)

fromFun : ∀ {n a} {A : Set a} → (Bits n → A) → Tree A n
fromFun {zero} f = leaf (f [])
fromFun {suc n} f = fork (fromFun (f ∘ 0∷_)) (fromFun (f ∘ 1∷_))

toFun : ∀ {n a} {A : Set a} → Tree A n → Bits n → A
toFun (leaf x) _ = x
toFun (fork left right) (b ∷ bs) = toFun (if b then right else left) bs

lookup : ∀ {n a} {A : Set a} → Bits n → Tree A n → A
lookup = flip toFun

-- Returns the flat vector of leaves underlying the perfect binary tree.
toVec : ∀ {n a} {A : Set a} → Tree A n → Vec A (2^ n)
toVec (leaf x)     = x ∷ []
toVec (fork t₀ t₁) = toVec t₀ ++ toVec t₁

lookup' : ∀ {m n a} {A : Set a} → Bits m → Tree A (m + n) → Tree A n
lookup' [] t = t
lookup' (b ∷ bs) (fork t t₁) = lookup' bs (if b then t₁ else t)


update' : ∀ {m n a} {A : Set a} → Bits m → Tree A n → Tree A (m + n) → Tree A (m + n)
update' [] val tree = val
update' (b ∷ key) val (fork tree tree₁) = if b then fork tree (update' key val tree₁) 
                                               else fork (update' key val tree) tree₁

map : ∀ {n a b} {A : Set a} {B : Set b} → (A → B) → Tree A n → Tree B n
map f (leaf x) = leaf (f x)
map f (fork t₀ t₁) = fork (map f t₀) (map f t₁)

open import Relation.Binary
open import Data.Star

data Swp {a} {A : Set a} : ∀ {n} (left right : Tree A n) → Set a where
  left : ∀ {n} {left₀ left₁ right : Tree A n} →
         Swp left₀ left₁ →
         Swp (fork left₀ right) (fork left₁ right)
  right : ∀ {n} {left right₀ right₁ : Tree A n} →
         Swp right₀ right₁ →
         Swp (fork left right₀) (fork left right₁)
  swp₁ : ∀ {n} {left right : Tree A n} →
         Swp (fork left right) (fork right left)
  swp₂ : ∀ {n} {t₀₀ t₀₁ t₁₀ t₁₁ : Tree A n} →
         Swp (fork (fork t₀₀ t₀₁) (fork t₁₀ t₁₁)) (fork (fork t₁₁ t₀₁) (fork t₁₀ t₀₀))

Swp★ : ∀ {a} {A : Set a} {n} (left right : Tree A n) → Set a
Swp★ = Star Swp

Swp-sym : ∀ {n a} {A : Set a} → Symmetric (Swp {A = A} {n})
Swp-sym (left s)  = left (Swp-sym s)
Swp-sym (right s) = right (Swp-sym s)
Swp-sym swp₁      = swp₁
Swp-sym swp₂      = swp₂

data Rot {a} {A : Set a} : ∀ {n} (left right : Tree A n) → Set a where
  leaf : ∀ x → Rot (leaf x) (leaf x)
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
Rot-refl {x = fork _ _} = fork Rot-refl Rot-refl

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

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Negation

module new-approach where

  open import Data.Empty

  import Function.Inverse as FI
  open FI using (_↔_; module Inverse; _InverseOf_)
  open import Function.Related
  import Function.Equality
  import Relation.Binary.PropositionalEquality as P

  data _∈_ {a}{A : Set a}(x : A) : {n : ℕ} → Tree A n → Set a where
    here  : x ∈ leaf x
    left  : {n : ℕ}{t₁ t₂ : Tree A n} → x ∈ t₁ → x ∈ fork t₁ t₂
    right : {n : ℕ}{t₁ t₂ : Tree A n} → x ∈ t₂ → x ∈ fork t₁ t₂

  toBits : ∀ {a}{A : Set a}{x : A}{n : ℕ}{t : Tree A n} → x ∈ t → Bits n
  toBits here = []
  toBits (left key) = 0b ∷ toBits key
  toBits (right key) = 1b ∷ toBits key

  ∈-lookup : ∀ {a}{A : Set a}{x : A}{n : ℕ}{t : Tree A n}(path : x ∈ t) → lookup (toBits path) t ≡ x
  ∈-lookup here = refl
  ∈-lookup (left path) = ∈-lookup path
  ∈-lookup (right path) = ∈-lookup path

  lookup-∈ : ∀ {a}{A : Set a}{n : ℕ}(key : Bits n)(t : Tree A n) → lookup key t ∈ t
  lookup-∈ [] (leaf x) = here
  lookup-∈ (true ∷ key) (fork tree tree₁) = right (lookup-∈ key tree₁)
  lookup-∈ (false ∷ key) (fork tree tree₁) = left (lookup-∈ key tree)

  _≈_ : ∀ {a}{A : Set a}{n : ℕ} → Tree A n → Tree A n → Set _
  t₁ ≈ t₂ = ∀ x → (x ∈ t₁) ↔ (x ∈ t₂) 

  ≈-refl : {a : _}{A : Set a}{n : ℕ}{t : Tree A n} → t ≈ t
  ≈-refl _ = FI.id

  move : ∀ {a}{A : Set a}{n : ℕ}{t s : Tree A n}{x : A} → t ≈ s → x ∈ t → x ∈ s
  move t≈s x∈t = Inverse.to (t≈s _) Function.Equality.⟨$⟩ x∈t

  swap₀ : ∀ {a}{A : Set a}{n : ℕ}(t₁ t₂ : Tree A n) → fork t₁ t₂ ≈ fork t₂ t₁
  swap₀ t₁ t₂ = λ x → record 
    { to         = →-to-⟶ swap
    ; from       = →-to-⟶ swap
    ; inverse-of = record { left-inverse-of  = swap-inv 
                          ; right-inverse-of = swap-inv } 
    } where
       swap : ∀ {a}{A : Set a}{x : A}{n : ℕ}{t₁ t₂ : Tree A n} → x ∈ fork t₁ t₂ → x ∈ fork t₂ t₁
       swap (left path)  = right path
       swap (right path) = left path

       swap-inv : ∀ {a}{A : Set a}{x : A}{n : ℕ}{t₁ t₂ : Tree A n}(p : x ∈ fork t₁ t₂) → swap (swap p) ≡ p
       swap-inv (left p)  = refl
       swap-inv (right p) = refl

  _⟨fork⟩_ : ∀ {a}{A : Set a}{n : ℕ}{t₁ t₂ s₁ s₂ : Tree A n} → t₁ ≈ s₁ → t₂ ≈ s₂ → fork t₁ t₂ ≈ fork s₁ s₂
  (t1≈s1 ⟨fork⟩ t2≈s2) y = record 
    { to         = to
    ; from       = from
    ; inverse-of = record { left-inverse-of  = frk-linv
                          ; right-inverse-of = frk-rinv  } 
    } where
        
        frk : ∀ {a}{A : Set a}{n : ℕ}{t₁ t₂ s₁ s₂ : Tree A n}{x : A} → t₁ ≈ s₁ → t₂ ≈ s₂ → x ∈ fork t₁ t₂ → x ∈ fork s₁ s₂
        frk t1≈s1 t2≈s2 (left x∈t1) = left (move t1≈s1 x∈t1)
        frk t1≈s1 t2≈s2 (right x∈t2) = right (move t2≈s2 x∈t2)
        
        to = →-to-⟶ (frk t1≈s1 t2≈s2)
        from = →-to-⟶ (frk (λ x → FI.sym (t1≈s1 x)) (λ x → FI.sym (t2≈s2 x)))

       
        open Function.Equality using (_⟨$⟩_)
        open import Function.LeftInverse

        frk-linv : from LeftInverseOf to
        frk-linv (left x) = cong left (_InverseOf_.left-inverse-of (Inverse.inverse-of (t1≈s1 y)) x)
        frk-linv (right x) = cong right (_InverseOf_.left-inverse-of (Inverse.inverse-of (t2≈s2 y)) x)

        frk-rinv : from RightInverseOf to -- ∀ x → to ⟨$⟩ (from ⟨$⟩ x) ≡ x
        frk-rinv (left x) = cong left (_InverseOf_.right-inverse-of (Inverse.inverse-of (t1≈s1 y)) x)
        frk-rinv (right x) = cong right (_InverseOf_.right-inverse-of (Inverse.inverse-of (t2≈s2 y)) x)

  Rot⟶≈ : ∀ {a}{A : Set a}{n : ℕ}{t₁ t₂ : Tree A n} → Rot t₁ t₂ → t₁ ≈ t₂
  Rot⟶≈ (leaf x)        y = FI.id
  Rot⟶≈ (fork rot rot₁) y = (Rot⟶≈ rot ⟨fork⟩ Rot⟶≈ rot₁) y
  Rot⟶≈ (krof {_} {l} {l'} {r} {r'} rot rot₁) y = 
        y ∈ fork l r ↔⟨ (Rot⟶≈ rot ⟨fork⟩ Rot⟶≈ rot₁) y ⟩
        y ∈ fork r' l' ↔⟨ swap₀ r' l' y ⟩ 
        y ∈ fork l' r' ∎
    where open EquationalReasoning

  put : {a : _}{A : Set a}{n : ℕ} → Bits n → A → Tree A n → Tree A n
  put [] val tree = leaf val
  put (x ∷ key) val (fork tree tree₁) = if x then fork tree (put key val tree₁) 
                                             else fork (put key val tree) tree₁

  -- move-me
  _∷≢_ : {n : ℕ}{xs ys : Bits n}(x : Bit) → x ∷ xs ≢ x ∷ ys → xs ≢ ys
  _∷≢_ x = contraposition $ cong $ _∷_ x

  ∈-put : {a : _}{A : Set a}{n : ℕ}(p : Bits n){x : A}(t : Tree A n) → x ∈ put p x t
  ∈-put [] t = here
  ∈-put (true ∷ p) (fork t t₁) = right (∈-put p t₁)
  ∈-put (false ∷ p) (fork t t₁) = left (∈-put p t)

  ∈-put-≢  : {a : _}{A : Set a}{n : ℕ}(p : Bits n){x y : A}{t : Tree A n}(path : x ∈ t)
          → p ≢ toBits path → x ∈ put p y t
  ∈-put-≢ [] here neg = ⊥-elim (neg refl)
  ∈-put-≢ (true ∷ p) (left path) neg   = left path
  ∈-put-≢ (false ∷ p) (left path) neg  = left (∈-put-≢ p path (false ∷≢ neg))
  ∈-put-≢ (true ∷ p) (right path) neg  = right (∈-put-≢ p path (true ∷≢ neg))
  ∈-put-≢ (false ∷ p) (right path) neg = right path

  swap : {a : _}{A : Set a}{n : ℕ} → (p₁ p₂ : Bits n) → Tree A n → Tree A n
  swap p₁ p₂ t = put p₁ a₂ (put p₂ a₁ t)
    where
      a₁ = lookup p₁ t
      a₂ = lookup p₂ t

  swap-perm₁ : {a : _}{A : Set a}{n : ℕ}{t : Tree A n}{x : A}(p : x ∈ t) → t ≈ swap (toBits p) (toBits p) t
  swap-perm₁ here         = ≈-refl 
  swap-perm₁ (left path)  = swap-perm₁ path ⟨fork⟩ ≈-refl
  swap-perm₁ (right path) = ≈-refl ⟨fork⟩ swap-perm₁ path

  swap-comm : {a : _}{A : Set a}{n : ℕ} (p₁ p₂ : Bits n)(t : Tree A n) → swap p₂ p₁ t ≡ swap p₁ p₂ t
  swap-comm [] [] (leaf x) = refl
  swap-comm (true ∷ p₁) (true ∷ p₂) (fork t t₁) = cong (fork t) (swap-comm p₁ p₂ t₁)
  swap-comm (true ∷ p₁) (false ∷ p₂) (fork t t₁) = refl
  swap-comm (false ∷ p₁) (true ∷ p₂) (fork t t₁) = refl
  swap-comm (false ∷ p₁) (false ∷ p₂) (fork t t₁) = cong (flip fork t₁) (swap-comm p₁ p₂ t)

  swap-perm₂ : {a : _}{A : Set a}{n : ℕ}{t : Tree A n}{x : A}(p' : Bits n)(p : x ∈ t) 
             → x ∈ swap (toBits p) p' t
  swap-perm₂ _ here = here
  swap-perm₂ (true ∷ p) (left path) rewrite ∈-lookup path = right (∈-put p _)
  swap-perm₂ (false ∷ p) (left path) = left (swap-perm₂ p path)
  swap-perm₂ (true ∷ p) (right path) = right (swap-perm₂ p path)
  swap-perm₂ (false ∷ p) (right path) rewrite ∈-lookup path = left (∈-put p _)

  swap-perm₃ : {a : _}{A : Set a}{n : ℕ}{t : Tree A n}{x : A}(p₁ p₂ : Bits n)(p : x ∈ t)
              → p₁ ≢ toBits p → p₂ ≢ toBits p → x ∈ swap p₁ p₂ t
  swap-perm₃ [] [] here neg₁ neg₂ = here
  swap-perm₃ (true ∷ p₁) (true ∷ p₂) (left path) neg₁ neg₂   = left path
  swap-perm₃ (true ∷ p₁) (false ∷ p₂) (left path) neg₁ neg₂  = left (∈-put-≢ _ path (false ∷≢ neg₂))
  swap-perm₃ (false ∷ p₁) (true ∷ p₂) (left path) neg₁ neg₂  = left (∈-put-≢ _ path (false ∷≢ neg₁))
  swap-perm₃ (false ∷ p₁) (false ∷ p₂) (left path) neg₁ neg₂ = left 
             (swap-perm₃ p₁ p₂ path (false ∷≢ neg₁) (false ∷≢ neg₂))
  swap-perm₃ (true ∷ p₁) (true ∷ p₂) (right path) neg₁ neg₂   = right
             (swap-perm₃ p₁ p₂ path (true ∷≢ neg₁) (true ∷≢ neg₂))
  swap-perm₃ (true ∷ p₁) (false ∷ p₂) (right path) neg₁ neg₂  = right (∈-put-≢ _ path (true ∷≢ neg₁))
  swap-perm₃ (false ∷ p₁) (true ∷ p₂) (right path) neg₁ neg₂  = right (∈-put-≢ _ path (true ∷≢ neg₂))
  swap-perm₃ (false ∷ p₁) (false ∷ p₂) (right path) neg₁ neg₂ = right path
