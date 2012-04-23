module flipbased-tree where

open import Function
open import Data.Bits
open import Data.Nat.NP
open import Data.Nat.Properties
open import bintree
open import Data.Product

import flipbased

-- “↺ n A” reads like: “toss n coins and then return a value of type A”
↺ : ∀ {a} n (A : Set a) → Set a
↺ = flip Tree

return↺ : ∀ {c a} {A : Set a} → A → ↺ c A
return↺ = leaf

runDet : ∀ {a} {A : Set a} → ↺ 0 A → A
runDet (leaf x) = x

toss : ↺ 1 Bit
toss = fork (leaf 0b) (leaf 1b)

weaken≤ : ∀ {m c a} {A : Set a} → m ≤ c → ↺ m A → ↺ c A
weaken≤ p (leaf x) = leaf x
weaken≤ (s≤s p) (fork left right) = fork (weaken≤ p left) (weaken≤ p right)

m≤n+m : ∀ m n → m ≤ n + m
m≤n+m m n = ℕ≤.trans (m≤m+n m n) (ℕ≤.reflexive (ℕ°.+-comm m n))

weaken+ : ∀ c {m a} {A : Set a} → ↺ m A → ↺ (c + m) A
weaken+ c = weaken≤ (m≤n+m _ c)

map↺ : ∀ {c a b} {A : Set a} {B : Set b} → (A → B) → ↺ c A → ↺ c B
map↺ f (leaf x) = leaf (f x)
map↺ f (fork left right) = fork (map↺ f left) (map↺ f right)

join↺ : ∀ {c₁ c₂ a} {A : Set a} → ↺ c₁ (↺ c₂ A) → ↺ (c₁ + c₂) A
join↺ {c} (leaf x)      = weaken+ c x
join↺     (fork left right) = fork (join↺ left) (join↺ right)

open flipbased ↺ toss weaken≤ leaf map↺ join↺ public

open import Data.Bool
open import Data.Bits
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

infix 4 _/2+_/2
infix 6 _/2
postulate
  [0,1] : Set
  0/1 : [0,1]
  1/1 : [0,1]
  _/2 : [0,1] → [0,1]
  _/2+_/2 : [0,1] → [0,1] → [0,1]
  _*/_ : [0,1] → [0,1] → [0,1]
  1-_ : [0,1] → [0,1]
-- sym _/2+_/2
-- 1 /2+ 1 /2 = 1/1
-- p /2+ p /2 = p
-- p /2+ (1- p) /2 = 1/2

  -- ·/1+_ : ℕ → Set
  -- /+/ : ℕ → [0,1] → [0,1] → [0,1]

  0/2+p/2≡p/2 : ∀ p → (0/1 /2+ p /2) ≡ p /2
  _/2+_/2-comm : ∀ x y → x /2+ y /2 ≡ y /2+ x /2
  1*q≡q : ∀ q → 1/1 */ q ≡ q
  0*q≡q : ∀ q → 0/1 */ q ≡ 0/1
  distr-*-/2+/2 : ∀ x y z → (x */ z) /2+ (y */ z) /2 ≡ (x /2+ y /2) */ z
  distr-/2-* : ∀ p q → (p /2) */ (q /2) ≡ ((p */ q) /2) /2
  0/2≡0 : 0/1 /2 ≡ 0/1
  1-_/2+1-_/2 : ∀ p q → (1- p) /2+ (1- q) /2 ≡ 1- (p /2+ q /2)

1/2^_ : ℕ → [0,1]
1/2^ zero = 1/1
1/2^ suc n = (1/2^ n)/2

1/2 : [0,1]
1/2 = 1/2^ 1
1/4 : [0,1]
1/4 = 1/2^ 2

data Pr[return↺_≡_]≡_ {a} {A : Set a} (x y : A) : [0,1] → Set a where
  Pr-≡ : x ≡ y → Pr[return↺ x ≡ y ]≡ 1/1
  Pr-≢ : x ≢ y → Pr[return↺ x ≡ y ]≡ 0/1

infix 2 Pr[_≡_]≡_
data Pr[_≡_]≡_ {a} {A : Set a} : ∀ {c} → ↺ c A → A → [0,1] → Set a where
  Pr-return : ∀ {c x y pr} (pf : Pr[return↺ x ≡ y ]≡ pr) → Pr[ return↺ {c = c} x ≡ y ]≡ pr

  Pr-fork : ∀ {c} {left right : ↺ c A} {x p q r}
            (eq : p /2+ q /2 ≡ r)
            (pf₀ : Pr[ left ≡ x ]≡ p)
            (pf₁ : Pr[ right ≡ x ]≡ q)
            → Pr[ fork left right ≡ x ]≡ r

Pr-fork′ : ∀ {c a} {A : Set a} {left right : ↺ c A} {x p q}
            → Pr[ left ≡ x ]≡ p
            → Pr[ right ≡ x ]≡ q
            → Pr[ fork left right ≡ x ]≡ (p /2+ q /2)
Pr-fork′ = Pr-fork refl

Pr-return-≡ : ∀ {c a} {A : Set a} {x : A} → Pr[ return↺ {c = c} x ≡ x ]≡ 1/1
Pr-return-≡ = Pr-return (Pr-≡ refl)

Pr-return-≢ : ∀ {c a} {A : Set a} {x y : A} → x ≢ y → Pr[ return↺ {c = c} x ≡ y ]≡ 0/1
Pr-return-≢ = Pr-return ∘ Pr-≢

import Function.Equality as F≡
import Function.Equivalence as F≈

_≈⇒_ : ∀ {c a} {A : Set a} (p₁ p₂ : ↺ c A) → Set a
p₁ ≈⇒ p₂ = ∀ {x pr} → Pr[ p₁ ≡ x ]≡ pr → Pr[ p₂ ≡ x ]≡ pr

_≈_ : ∀ {c a} {A : Set a} (p₁ p₂ : ↺ c A) → Set a
p₁ ≈ p₂ = ∀ {x pr} → (Pr[ p₁ ≡ x ]≡ pr) F≈.⇔ (Pr[ p₂ ≡ x ]≡ pr)

≈-refl : ∀ {c a} {A : Set a} → Reflexive {A = ↺ c A} _≈_
≈-refl = F≈.id

≈-sym : ∀ {c a} {A : Set a} {p₁ p₂ : ↺ c A} → p₁ ≈ p₂ → p₂ ≈ p₁
≈-sym η = F≈.sym η

≈-trans : ∀ {c a} {A : Set a} → Transitive {A = ↺ c A} _≈_
≈-trans f g = g F≈.∘ f

fork-sym⇒ : ∀ {c a} {A : Set a} {p₁ p₂ : ↺ c A} → fork p₁ p₂ ≈⇒ fork p₂ p₁
fork-sym⇒ (Pr-fork {p = p} {q} refl pf₁ pf₀) rewrite p /2+ q /2-comm = Pr-fork′ pf₀ pf₁

fork-sym : ∀ {c a} {A : Set a} {p₁ p₂ : ↺ c A} → fork p₁ p₂ ≈ fork p₂ p₁
fork-sym = F≈.equivalence fork-sym⇒ fork-sym⇒

Pr-fork-0 : ∀ {c a} {A : Set a} {left right : ↺ c A} {x : A} {p}
            → Pr[ left ≡ x ]≡ 0/1
            → Pr[ right ≡ x ]≡ p
            → Pr[ fork left right ≡ x ]≡ p /2
Pr-fork-0 {p = p} eq₁ eq₂ rewrite sym (0/2+p/2≡p/2 p) = Pr-fork′ eq₁ eq₂

ex₁ : ∀ x → Pr[ toss ≡ x ]≡ 1/2
ex₁ 1b = Pr-fork-0 (Pr-return-≢ (λ ())) Pr-return-≡
ex₁ 0b = F≈.Equivalence.to fork-sym F≡.⟨$⟩ (Pr-fork-0 (Pr-return-≢ (λ ())) Pr-return-≡)

Pr-map : ∀ {c a b} {A : Set a} {B : Set b} {Alg : ↺ c A} {x pr} {f : A → B} →
  (f-inj : ∀ {x y} → f x ≡ f y → x ≡ y) →
  Pr[ Alg ≡ x ]≡ pr →
  Pr[ ⟪ f · Alg ⟫ ≡ f x ]≡ pr
Pr-map f-inj (Pr-return (Pr-≡ refl)) = Pr-return (Pr-≡ refl)
Pr-map f-inj (Pr-return (Pr-≢ x≢y)) = Pr-return (Pr-≢ (x≢y ∘ f-inj))
Pr-map f-inj (Pr-fork eq pf₀ pf₁) = Pr-fork eq (Pr-map f-inj pf₀) (Pr-map f-inj pf₁)

Pr-same : ∀ {c a} {A : Set a} {Alg : ↺ c A} {x pr₀ pr₁} →
    pr₀ ≡ pr₁ →
    Pr[ Alg ≡ x ]≡ pr₀ →
    Pr[ Alg ≡ x ]≡ pr₁
Pr-same refl = id

Pr-weaken≤ : ∀ {c₀ c₁ a} {A : Set a} {Alg : ↺ c₀ A} {x pr} →
    (c₀≤c₁ : c₀ ≤ c₁) →
    Pr[ Alg ≡ x ]≡ pr →
    Pr[ weaken≤ c₀≤c₁ Alg ≡ x ]≡ pr
Pr-weaken≤ p (Pr-return pf) = Pr-return pf
Pr-weaken≤ (s≤s c₀≤c₁) (Pr-fork eq pf₀ pf₁)
  = Pr-fork eq (Pr-weaken≤ c₀≤c₁ pf₀) (Pr-weaken≤ c₀≤c₁ pf₁)

Pr-weaken+ : ∀ {c₀} c₁ {a} {A : Set a} {Alg : ↺ c₀ A} {x pr} →
    Pr[ Alg ≡ x ]≡ pr →
    Pr[ weaken+ c₁ Alg ≡ x ]≡ pr
Pr-weaken+ c₁ = Pr-weaken≤ (m≤n+m _ c₁)

Pr-map-0 : ∀ {c a b} {A : Set a} {B : Set b} {Alg : ↺ c A} {f : A → B} {x} → (∀ y → f y ≢ x)
           → Pr[ map↺ f Alg ≡ x ]≡ 0/1
Pr-map-0 {Alg = leaf x} f-prop = Pr-return (Pr-≢ (f-prop x))
Pr-map-0 {Alg = fork Alg Alg₁} f-prop = Pr-fork (trans (0/2+p/2≡p/2 0/1) 0/2≡0)
                                                (Pr-map-0 f-prop) (Pr-map-0 f-prop)

Pr-zip : ∀ {c₀ c₁ a b} {A : Set a} {B : Set b} {Alg₀ : ↺ c₀ A} {Alg₁ : ↺ c₁ B} {x y pr₁ pr₂} →
  Pr[ Alg₀ ≡ x ]≡ pr₁ →
  Pr[ Alg₁ ≡ y ]≡ pr₂ →
  Pr[ zip↺ Alg₀ Alg₁ ≡ (x , y) ]≡ (pr₁ */ pr₂)
Pr-zip {c₀} {pr₂ = pr₂} (Pr-return {x = x} (Pr-≡ refl)) pf₂
  rewrite 1*q≡q pr₂ = Pr-weaken+ c₀ (Pr-map {f = _,_ x} (cong proj₂) pf₂)
Pr-zip {c₀} {pr₂ = pr₂} (Pr-return {x = x} (Pr-≢ pf)) pf₂
  rewrite 0*q≡q pr₂ = Pr-weaken+ c₀ (Pr-map-0 (λ y x₁ → pf (cong proj₁ x₁)))
Pr-zip (Pr-fork refl pf₁ pf₂) pf₃ = Pr-fork (distr-*-/2+/2 _ _ _) (Pr-zip pf₁ pf₃) (Pr-zip pf₂ pf₃)

ex₂ : ∀ x y → Pr[ toss ⟨,⟩ toss ≡ (x , y) ]≡ 1/4
ex₂ x y = Pr-same (trans (distr-/2-* _ _) (cong (_/2 ∘ _/2) (1*q≡q _)))
                  (Pr-zip {Alg₀ = toss} {Alg₁ = toss} (ex₁ x) (ex₁ y))

pr-choose : ∀ {c a} {A : Set a} {p₀ p₁ : ↺ c A} {pr₀ pr₁ x}
             → Pr[ p₀ ≡ x ]≡ pr₀
             → Pr[ p₁ ≡ x ]≡ pr₁
             → Pr[ choose p₀ p₁ ≡ x ]≡ pr₀ /2+ pr₁ /2
pr-choose {c} {pr₀ = pr₀} {pr₁} pf₀ pf₁ =
  Pr-fork (pr₁ /2+ pr₀ /2-comm) (Pr-weaken+ 0 pf₁) (Pr-weaken+ 0 pf₀)

postulate
  pr-ret-xor : ∀ {x y pr} b
         → Pr[return↺ x ≡ y ]≡ pr
         → Pr[return↺ x ≡ b xor y ]≡ pr
-- pr-ret-xor b pf = {!!}

pr-xor'' : ∀ {c} {Alg : ↺ c Bit} {x pr} b
         → Pr[ Alg ≡ x ]≡ pr
         → Pr[ Alg ≡ b xor x ]≡ pr
pr-xor'' b (Pr-return pf) = Pr-return (pr-ret-xor b pf)
pr-xor'' b (Pr-fork refl pf₀ pf₁) = Pr-fork refl (pr-xor'' b pf₀) (pr-xor'' b pf₁)

pr-xor' : ∀ {c} {Alg : ↺ c Bit} {x pr b}
         → Pr[ Alg ≡ x ]≡ pr
         → Pr[ ⟪ _xor_ b · Alg ⟫ ≡ b xor x ]≡ pr
pr-xor' {b = b} = Pr-map (xor-inj {b})
  where
    -- move it!
    not-inj : ∀ {x y} → not x ≡ not y → x ≡ y
    not-inj {true} {true} = λ _ → refl
    not-inj {true} {false} = λ ()
    not-inj {false} {true} = λ ()
    not-inj {false} {false} = λ _ → refl
    xor-inj : ∀ {b x y} → b xor x ≡ b xor y → x ≡ y
    xor-inj {true} = not-inj
    xor-inj {false} = id

postulate
  pr-ret-not : ∀ {x y pr}
         → Pr[return↺ x ≡ y ]≡ pr
         → Pr[return↺ x ≡ not y ]≡ 1- pr
-- pr-ret-not = {!!}

pr-not : ∀ {c} {Alg : ↺ c Bit} {x pr}
         → Pr[ Alg ≡ x ]≡ pr
         → Pr[ Alg ≡ not x ]≡ 1- pr
pr-not (Pr-return pf) = Pr-return (pr-ret-not pf)
pr-not (Pr-fork refl pf pf₁) = Pr-fork (1- _ /2+1- _ /2) (pr-not pf) (pr-not pf₁)

postulate
  pr-xor : ∀ {c} {Alg : ↺ c Bit} {x pr b}
         → Pr[ Alg ≡ x ]≡ pr
         → Pr[ ⟪ _xor_ b · Alg ⟫ ≡ x ]≡ pr
-- pr-xor {b = b} = {!pr-not!}

postulate
  pr-toss-xor-toss : ∀ x → Pr[ toss ⟨xor⟩ toss ≡ x ]≡ 1/2
-- pr-toss-xor-toss x = {!!}

postulate
  ex₃ : ∀ {n} (x : Bits n) → Pr[ random ≡ x ]≡ 1/2^ n
