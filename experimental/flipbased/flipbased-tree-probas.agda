-- This module is an early draft of a previous attempt at probabilities of randomized programs.

open import Data.Bool.Properties
open import Data.Bool.NP
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Level using () renaming (_⊔_ to _L⊔_)
open import Function
open import Data.Nat.NP using (ℕ; zero; suc; _≤_; s≤s; _+_)
open import Data.Nat.Properties
open import Data.Product

open import Data.Bits
open import bintree
open import flipbased-tree hiding (weaken≤)

module flipbased-tree-probas where

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

1/2^_ : ℕ → [0,1]
1/2^ zero = 1/1
1/2^ suc n = (1/2^ n)/2

1/2 : [0,1]
1/2 = 1/2^ 1
1/4 : [0,1]
1/4 = 1/2^ 2

postulate
  0/2+p/2≡p/2 : ∀ p → (0/1 /2+ p /2) ≡ p /2
  /2+/2-refl : ∀ x → x /2+ x /2 ≡ x
  _/2+_/2-comm : ∀ x y → x /2+ y /2 ≡ y /2+ x /2
  */-comm : ∀ x y → x */ y ≡ y */ x
  1*q≡q : ∀ q → 1/1 */ q ≡ q
  0*q≡q : ∀ q → 0/1 */ q ≡ 0/1
  distr-*-/2+/2 : ∀ {x y z} → (x */ z) /2+ (y */ z) /2 ≡ (x /2+ y /2) */ z
  distr-/2-* : ∀ {p q} → (p /2) */ (q /2) ≡ ((p */ q) /2) /2
  0/2≡0 : 0/1 /2 ≡ 0/1
  1-1≡0 : 1- 1/1 ≡ 0/1
  1-0≡1 : 1- 0/1 ≡ 1/1
  1-1/2≡1/2 : 1- 1/2 ≡ 1/2
  1-_/2+1-_/2 : ∀ p q → (1- p) /2+ (1- q) /2 ≡ 1- (p /2+ q /2)

syntax Pr↺ P pr Alg = Pr[ Alg ! P ]≡ pr
data Pr↺ {a} {A : Set a} (P : A → [0,1] → Set a) (pr : [0,1]) : ∀ {c} → ↺ c A → Set a where
  Pr-return : ∀ {c x} (Px : P x pr) → Pr[ return↺ {c = c} x ! P ]≡ pr

  Pr-fork : ∀ {c} {left right : ↺ c A} {p q}
            (eq : p /2+ q /2 ≡ pr)
            (pf₀ : Pr[ left ! P ]≡ p)
            (pf₁ : Pr[ right ! P ]≡ q)
            → Pr[ fork left right ! P ]≡ pr

data Pr[return↺_≡_]≡_ {a} {A : Set a} (x y : A) : [0,1] → Set a where
  Pr-≡ : (x≡y : x ≡ y) → Pr[return↺ x ≡ y ]≡ 1/1
  Pr-≢ : (x≢y : x ≢ y) → Pr[return↺ x ≡ y ]≡ 0/1

infix 2 Pr[_≡_]≡_
Pr[_≡_]≡_ : ∀ {a} {A : Set a} {c} → ↺ c A → A → [0,1] → Set a
Pr[ Alg ≡ x ]≡ pr = Pr[ Alg ! flip Pr[return↺_≡_]≡_ x ]≡ pr

Pr[_≡*]≡_ : ∀ {a} {A : Set a} {c} → ↺ c A → [0,1] → Set a
Pr[ Alg ≡*]≡ pr = ∀ {x} → Pr[ Alg ≡ x ]≡ pr

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

1-Pr : ∀ {c a} {A : Set a} {Alg : ↺ c A} {p P Q}
       → (∀ {p x} → P x p → Q x (1- p))
       → Pr[ Alg ! P ]≡ p
       → Pr[ Alg ! Q ]≡ 1- p
1-Pr PQ (Pr-return pf) = Pr-return (PQ pf)
1-Pr PQ (Pr-fork refl pf pf₁) = Pr-fork (1- _ /2+1- _ /2) (1-Pr PQ pf) (1-Pr PQ pf₁)

Pr-ret-not : ∀ {p x y} → Pr[return↺ x ≡ y ]≡ p → Pr[return↺ x ≡ not y ]≡ (1- p)
Pr-ret-not (Pr-≡ x≡y) rewrite 1-1≡0 = Pr-≢ (not-¬ x≡y)
Pr-ret-not (Pr-≢ x≢y) rewrite 1-0≡1 = Pr-≡ (¬-not x≢y)

Pr-not⇒ : ∀ {c} {Alg : ↺ c Bit} {x pr}
         → Pr[ Alg ≡ x ]≡ pr
         → Pr[ Alg ≡ not x ]≡ 1- pr
Pr-not⇒ = 1-Pr Pr-ret-not

Pr-not⇐ : ∀ {c} {Alg : ↺ c Bit} {x pr}
         → Pr[ Alg ≡ not x ]≡ pr
         → Pr[ Alg ≡ x ]≡ 1- pr
Pr-not⇐ {Alg = Alg} {x} {pr} pf = subst (λ z → Pr[ Alg ≡ z ]≡ 1- pr) (not-involutive x) (Pr-not⇒ pf)

Pr-toss : ∀ x → Pr[ toss ≡ x ]≡ 1/2
Pr-toss true  {-1b-} = Pr-fork-0 (Pr-return-≢ (λ ())) Pr-return-≡
Pr-toss false {-0b-} = F≈.Equivalence.to fork-sym F≡.⟨$⟩ (Pr-fork-0 (Pr-return-≢ (λ ())) Pr-return-≡)

Pr-map : ∀ {c a b} {A : Set a} {B : Set b} {Alg : ↺ c A} {P Q pr} {F : [0,1] → [0,1]} {f : A → B} →
  (R : ∀ {pr x} → P x pr → Q (f x) (F pr)) →
  (F-R : ∀ {p q} → F p /2+ F q /2 ≡ F (p /2+ q /2)) →
  Pr[ Alg ! P ]≡ pr →
  Pr[ ⟪ f · Alg ⟫ ! Q ]≡ F pr
Pr-map R F-R (Pr-return pf) = Pr-return (R pf)
Pr-map R F-R (Pr-fork refl pf₀ pf₁) = Pr-fork F-R (Pr-map R F-R pf₀) (Pr-map R F-R pf₁)

Pr-return-inj : ∀ {a b} {A : Set a} {B : Set b} {x y pr} {f : A → B} →
  (f-inj-xy : f x ≡ f y → x ≡ y) →
  Pr[return↺ x ≡ y ]≡ pr →
  Pr[return↺ f x ≡ f y ]≡ pr
Pr-return-inj f-inj-xy (Pr-≡ refl) = Pr-≡ refl
Pr-return-inj f-inj-xy (Pr-≢ x≢y) = Pr-≢ (x≢y ∘ f-inj-xy)

Pr-map-inj : ∀ {c a b} {A : Set a} {B : Set b} {Alg : ↺ c A} {x pr} {f : A → B} →
  (f-inj : ∀ {x y} → f x ≡ f y → x ≡ y) →
  Pr[ Alg ≡ x ]≡ pr →
  Pr[ ⟪ f · Alg ⟫ ≡ f x ]≡ pr
Pr-map-inj f-inj pf = Pr-map {F = id} (Pr-return-inj f-inj) refl pf

Pr-same : ∀ {c a} {A : Set a} {Alg : ↺ c A} {x pr₀ pr₁} →
    pr₀ ≡ pr₁ →
    Pr[ Alg ≡ x ]≡ pr₀ →
    Pr[ Alg ≡ x ]≡ pr₁
Pr-same refl = id

Pr-weaken≤ : ∀ {c₀ c₁ a} {A : Set a} {Alg : ↺ c₀ A} {P pr} →
    (c₀≤c₁ : c₀ ≤ c₁) →
    Pr[ Alg ! P ]≡ pr →
    Pr[ weaken≤ c₀≤c₁ Alg ! P ]≡ pr
Pr-weaken≤ p (Pr-return pf) = Pr-return pf
Pr-weaken≤ (s≤s c₀≤c₁) (Pr-fork eq pf₀ pf₁)
  = Pr-fork eq (Pr-weaken≤ c₀≤c₁ pf₀) (Pr-weaken≤ c₀≤c₁ pf₁)

Pr-weaken+ : ∀ {c₀} c₁ {a} {A : Set a} {Alg : ↺ c₀ A} {P pr} →
    Pr[ Alg ! P ]≡ pr →
    Pr[ weaken+ c₁ Alg ! P ]≡ pr
Pr-weaken+ c₁ = Pr-weaken≤ (m≤n+m _ c₁)

Pr-map-0 : ∀ {c a b} {A : Set a} {B : Set b} {Alg : ↺ c A} {f : A → B} {x} → (∀ y → f y ≢ x)
           → Pr[ map↺ f Alg ≡ x ]≡ 0/1
Pr-map-0 {Alg = leaf x} f-prop = Pr-return (Pr-≢ (f-prop x))
Pr-map-0 {Alg = fork Alg Alg₁} f-prop = Pr-fork (trans (0/2+p/2≡p/2 0/1) 0/2≡0)
                                                (Pr-map-0 f-prop) (Pr-map-0 f-prop)

PR : ∀ {a} → Set a → Set _
PR {a} A = A → [0,1] → Set a

record Pr× {a b} {A : Set a} {B : Set b} (F : [0,1] → [0,1] → [0,1]) (PrA : PR A) (PrB : PR B) (xy : A × B) pr : Set (a L⊔ b) where
  constructor mk
  field
    {pr₀ pr₁} : [0,1]
    pr₀*pr₁≡pr : F pr₀ pr₁ ≡ pr
    prA : PrA (proj₁ xy) pr₀
    prB : PrB (proj₂ xy) pr₁

Pr!-zip : ∀ {c₀ c₁ a b} {A : Set a} {B : Set b} {Alg₀ : ↺ c₀ A} {Alg₁ : ↺ c₁ B} {P₀ P₁ pr₀ pr₁}
  {F}
  (F₀ : ∀ {pr₀ p q} → (F pr₀ p) /2+ (F pr₀ q) /2 ≡ F pr₀ (p /2+ q /2))
  (F₁ : ∀ {pr₁ p q} → (F p pr₁) /2+ (F q pr₁) /2 ≡ F (p /2+ q /2) pr₁)
  → Pr[ Alg₀ ! P₀ ]≡ pr₀
  → Pr[ Alg₁ ! P₁ ]≡ pr₁
  → Pr[ zip↺ Alg₀ Alg₁ ! Pr× F P₀ P₁ ]≡ F pr₀ pr₁
Pr!-zip {c₀} {pr₀ = pr₀} {F = F} F₀ F₁ (Pr-return Px) pf₁
  = Pr-weaken+ c₀ (Pr-map {F = F pr₀} (mk refl Px) F₀ pf₁)
Pr!-zip F₀ F₁ (Pr-fork refl pf₀ pf₁) pf₂ = Pr-fork F₁ (Pr!-zip F₀ F₁ pf₀ pf₂) (Pr!-zip F₀ F₁ pf₁ pf₂)

Pr!⇒ : ∀ {c a} {A : Set a} {P Q : PR A} {Alg : ↺ c A} {pr}
        → (∀ {x pr} → P x pr → Q x pr) → Pr[ Alg ! P ]≡ pr → Pr[ Alg ! Q ]≡ pr
Pr!⇒ P⇒Q (Pr-return Px) = Pr-return (P⇒Q Px)
Pr!⇒ P⇒Q (Pr-fork eq pf pf₁) = Pr-fork eq (Pr!⇒ P⇒Q pf) (Pr!⇒ P⇒Q pf₁)

Pr-zip : ∀ {c₀ c₁ a b} {A : Set a} {B : Set b} {Alg₀ : ↺ c₀ A} {Alg₁ : ↺ c₁ B} {x y pr₁ pr₂} →
  Pr[ Alg₀ ≡ x ]≡ pr₁ →
  Pr[ Alg₁ ≡ y ]≡ pr₂ →
  Pr[ zip↺ Alg₀ Alg₁ ≡ (x , y) ]≡ (pr₁ */ pr₂)
Pr-zip {x = x} {y} pf₀ pf₁ = Pr!⇒ helper' (Pr!-zip {F = _*/_} helper distr-*-/2+/2 pf₀ pf₁)
  where
    helper = λ {pr₀} {p} {q} → trans (trans (cong₂ _/2+_/2 (*/-comm _ _) (*/-comm _ _)) distr-*-/2+/2) (sym (*/-comm pr₀ (p /2+ q /2)))
    helper' : ∀ {xy pr} → Pr× _*/_ (flip Pr[return↺_≡_]≡_ x) (flip Pr[return↺_≡_]≡_ y) xy pr → Pr[return↺ xy ≡ x , y ]≡ pr
    helper' (mk {pr₁ = pr₃} refl (Pr-≡ refl) prB) rewrite 1*q≡q pr₃ = Pr-return-inj (cong proj₂) prB
    helper' (mk {pr₁ = pr₃} refl (Pr-≢ x≢y) prB) rewrite 0*q≡q pr₃ = Pr-≢ (x≢y ∘ cong proj₁)

Pr-zip↺-toss-toss : ∀ x y → Pr[ toss ⟨,⟩ toss ≡ (x , y) ]≡ 1/4
Pr-zip↺-toss-toss x y = Pr-same (trans distr-/2-* (cong (_/2 ∘ _/2) (1*q≡q _)))
                                 (Pr-zip {Alg₀ = toss} {Alg₁ = toss} (Pr-toss x) (Pr-toss y))

pr-choose : ∀ {c a} {A : Set a} {p₀ p₁ : ↺ c A} {pr₀ pr₁ x}
             → Pr[ p₀ ≡ x ]≡ pr₀
             → Pr[ p₁ ≡ x ]≡ pr₁
             → Pr[ choose p₀ p₁ ≡ x ]≡ pr₀ /2+ pr₁ /2
pr-choose {c} {pr₀ = pr₀} {pr₁} pf₀ pf₁ =
  Pr-fork (pr₁ /2+ pr₀ /2-comm) (Pr-weaken+ 0 pf₁) (Pr-weaken+ 0 pf₀)

Pr-≡xor⇒ : ∀ {c} {Alg : ↺ c Bit} {x} b
         → Pr[ Alg ≡ x ]≡ 1/2
         → Pr[ Alg ≡ b xor x ]≡ 1/2
Pr-≡xor⇒ true pf = Pr-same 1-1/2≡1/2 (Pr-not⇒ pf)
Pr-≡xor⇒ false pf = pf

Pr-≡xor⇐ : ∀ {c} {Alg : ↺ c Bit} {x} b
         → Pr[ Alg ≡ b xor x ]≡ 1/2
         → Pr[ Alg ≡ x ]≡ 1/2
Pr-≡xor⇐ {x = x} true pf  = Pr-same 1-1/2≡1/2 (Pr-not⇐ pf)
Pr-≡xor⇐ false pf = pf

Pr-xor : ∀ {c} {Alg : ↺ c Bit} {x b}
         → Pr[ Alg ≡ x ]≡ 1/2
         → Pr[ ⟪ _xor_ b · Alg ⟫ ≡ x ]≡ 1/2
Pr-xor {b = b} = Pr-≡xor⇐ b ∘ Pr-map-inj (xor-inj₁ b)

Pr-xor-toss : ∀ {i} → Pr[ ⟪ _xor_ i · toss ⟫ ≡*]≡ 1/2
Pr-xor-toss {i} = Pr-xor {b = i} (Pr-toss _)
