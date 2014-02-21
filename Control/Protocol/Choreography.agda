
-- {-# OPTIONS --without-K #-}
open import Coinduction
open import Function.NP
open import Type
open import Level.NP
open import Data.Product.NP renaming (map to ×-map; proj₁ to fst; proj₂ to snd)
open import Data.Zero
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr; [_,_] to [inl:_,inr:_])
open import Data.One hiding (_≟_)
open import Data.Two hiding (_≟_)
open import Data.Nat hiding (_⊔_)
open Data.Two.Indexed

open import Relation.Binary
open import Relation.Binary.PropositionalEquality.NP as ≡

module Control.Protocol.Choreography where

Π· : ∀ {a b}(A : ★_ a) → (B : ..(_ : A) → ★_ b) → ★_ (a ⊔ b)
Π· A B = ..(x : A) → B x

data ☐ {a}(A : ★_ a) : ★_ a where
  [_] : ..(x : A) → ☐ A

un☐ : ∀ {a b}{A : ★_ a}{B : ☐ A → ★_ b} → (..(x : A) → B [ x ]) → Π (☐ A) B
un☐ f [ x ] = f x

  {-
data S<_> {a} {A : ★_ a} : ..(x : A) → ★_ a where
  S[_] : ∀ x → S< x >

unS : ∀ {a} {A : ★_ a} ..{x : A} → S< x > → A
unS S[ y ] = y
-}

data _≡☐_ {a} {A : ★_ a} (x : A) : ..(y : A) → ★_ a where
  refl : x ≡☐ x

record S<_> {a} {A : ★_ a} ..(x : A) : ★_ a where
  constructor S[_∥_]
  field
    unS : A
    isS : unS ≡☐ x
open S<_> public

S[_] : ∀ {a}{A : ★_ a} (x : A) → S< x >
S[ x ] = S[ x ∥ refl ]

_>>☐_ : ∀ {a b}{A : ★_ a}{B : ☐ A → ★_ b} (x : ☐ A) → (..(x : A) → B [ x ]) → B x
[ x ] >>☐ f = f x

-- This is not a proper map since the function takes a ..A.
map☐ : ∀ {a b}{A : ★_ a}{B : ★_ b} → (..(x : A) → B) → ☐ A → ☐ B
map☐ f [ x ] = [ f x ]

-- This does not work since a ☐ has to be relevant when eliminated.
-- join☐ : ∀ {a}{A : ★_ a} → ☐ (☐ A) → ☐ A

{- This is not a proper bind either.
_>>=☐_ : ∀ {a b}{A : ★_ a}{B : ★_ b} (x : ☐ A) → (..(x : A) → ☐ B) → ☐ B
_>>=☐_ = _>>☐_
-}

data InOut : ★ where
  In Out : InOut

dualᴵᴼ : InOut → InOut
dualᴵᴼ In  = Out
dualᴵᴼ Out = In

mutual
    record Com : ★₁ where
      constructor mk
      field
        io : InOut
        M  : ★
        P  : M → Proto

    data Proto : ★₁ where
      end : Proto
      com : Com → Proto

pattern com' q M P = com (mk q M P)

module ProtoRel (_≈ᴵᴼ_ : InOut → InOut → ★) where
    infix 0 _≈ᴾ_
    data _≈ᴾ_ : Proto → Proto → ★₁ where
      end : end ≈ᴾ end
      com : ∀ {q₀ q₁} (q : q₀ ≈ᴵᴼ q₁) M {P Q} → (∀ m → P m ≈ᴾ Q m) → com' q₀ M P ≈ᴾ com' q₁ M Q
open ProtoRel _≡_ public renaming (_≈ᴾ_ to _≡ᴾ_)

{-
infix 0 _≡ᴾ_
data _≡ᴾ_ : Proto → Proto → ★₁ where
  end : end ≡ᴾ end
  com : ∀ q M {P Q} → (∀ m → P m ≡ᴾ Q m) → com' q M P ≡ᴾ com' q M Q
  -}

pattern Πᶜ M P = mk In  M P
pattern Σᶜ M P = mk Out M P

pattern Πᴾ M P = com (mk In  M P)
pattern Σᴾ M P = com (mk Out M P)
{-
Π' : (M : ★)(P : M → Proto) → Proto
Π' M P = com In  M P

Σ' : (M : ★)(P : M → Proto) → Proto
Σ' M P = com Out M P
-}

Π☐ᴾ : (M : ★)(P : ..(_ : M) → Proto) → Proto
Π☐ᴾ M P = Πᴾ (☐ M) (λ { [ m ] → P m })

Σ☐ᴾ : (M : ★)(P : ..(_ : M) → Proto) → Proto
Σ☐ᴾ M P = Σᴾ (☐ M) (λ { [ m ] → P m })

mutual
    Trace : Proto → Proto
    Trace end     = end
    Trace (com c) = com (Traceᶜ c)

    Traceᶜ : Com → Com
    Traceᶜ c = Σᶜ (Com.M c) λ m → Trace (Com.P c m)

mutual
    dual : Proto → Proto
    dual end     = end
    dual (com c) = com (dualᶜ c)

    dualᶜ : Com → Com
    dualᶜ c = mk (dualᴵᴼ (Com.io c)) (Com.M c) λ m → dual (Com.P c m)

data IsTrace : Proto → ★₁ where
  end : IsTrace end
  com : ∀ M {P} (PT : ∀ m → IsTrace (P m)) → IsTrace (Σᴾ M P)

data IsSink : Proto → ★₁ where
  end : IsSink end
  com : ∀ M {P} (PT : ∀ m → IsSink (P m)) → IsSink (Πᴾ M P)

data Proto☐ : Proto → ★₁ where
  end : Proto☐ end
  com : ∀ q M {P} (P☐ : ∀ m → Proto☐ (P m)) → Proto☐ (com' q (☐ M) P)

⟦_⟧ᴵᴼ : InOut → (M : ★) (P : M → ★) → ★
⟦_⟧ᴵᴼ In  = Π
⟦_⟧ᴵᴼ Out = Σ

⟦_⟧ : Proto → ★
⟦ end        ⟧ = 𝟙
⟦ com' q M P ⟧ = ⟦ q ⟧ᴵᴼ M λ m → ⟦ P m ⟧

⟦_⊥⟧ : Proto → ★
⟦ P ⊥⟧ = ⟦ dual P ⟧

⟦_⟧⟨_≈_⟩ : (P : Proto) (p q : ⟦ P ⟧) → ★
⟦ end    ⟧⟨ p ≈ q ⟩ = 𝟙
⟦ Πᴾ M P ⟧⟨ p ≈ q ⟩ = (m : M) → ⟦ P m ⟧⟨ p m ≈ q m ⟩
⟦ Σᴾ M P ⟧⟨ p ≈ q ⟩ = Σ (fst p ≡ fst q) λ e → ⟦ P (fst q) ⟧⟨ subst (⟦_⟧ ∘ P) e (snd p) ≈ snd q ⟩

_×'_ : ★ → Proto → Proto
M ×' P = Σᴾ M λ _ → P

_→'_ : ★ → Proto → Proto
M →' P = Πᴾ M λ _ → P

data Accept? : ★ where
  accept reject : Accept?
data Is-accept : Accept? → ★ where
  accept : Is-accept accept

mutual
    data Dualᶜ : Com → Com → ★₁ where
      Π·Σ : ∀ {M P Q} → (∀ x → Dual (P x) (Q x)) → Dualᶜ (Πᶜ M P) (Σᶜ M Q)
      Σ·Π : ∀ {M P Q} → (∀ x → Dual (P x) (Q x)) → Dualᶜ (Σᶜ M P) (Πᶜ M Q)

    data Dual : Proto → Proto → ★₁ where
      end : Dual end end
      Π·Σ : ∀ {M P Q} → (∀ x → Dual (P x) (Q x)) → Dual (Πᴾ M P) (Σᴾ M Q)
      Σ·Π : ∀ {M P Q} → (∀ x → Dual (P x) (Q x)) → Dual (Σᴾ M P) (Πᴾ M Q)
      {-
      Π☐·Σ : ∀ {M P Q} → (∀ x → Dual (P [ x ]) (Q x)) → Dual (Πᴾ (☐ M) P) (Σᴾ M Q)
      Σ·Π☐ : ∀ {M P Q} → (∀ x → Dual (P x) (Q [ x ])) → Dual (Σᴾ M P) (Πᴾ (☐ M) Q)
      -}

      {-
data Choreo (I : ★) : ★₁ where
  _-[_]→_⁏_ : (A : I) (M : ★) (B : I) (ℂ : ..(m : M) → Choreo I) → Choreo I
  _-[_]→★⁏_ : (A : I) (M : ★)         (ℂ :   (m : M) → Choreo I) → Choreo I
  end       : Choreo I

module _ {I : ★} where 
    _-[_]→ø⁏_ : ∀ (A : I) (M : ★)         (ℂ : ..(m : M) → Choreo I) → Choreo I
    A -[ M ]→ø⁏ ℂ = A -[ ☐ M ]→★⁏ λ { [ m ] → ℂ m }

    _//_ : (ℂ : Choreo I) (p : I → 𝟚) → Proto
    (A -[ M ]→ B ⁏ ℂ) // p = com (case p A
                               0: case p B
                                    0: Πᶜ (☐ M) (λ { [ m ] → ℂ m // p })
                                    1: Πᶜ M     (λ     m   → ℂ m // p)
                               1: Σᶜ M (λ m → ℂ m // p))
    (A -[ M ]→★⁏   ℂ) // p = com' (case p A 0: In 1: Out) M λ m → ℂ m // p
    end               // p = end

    ℂObserver : Choreo I → Proto
    ℂObserver ℂ = ℂ // λ _ → 0₂

    ℂTrace : Choreo I → Proto
    ℂTrace ℂ = ℂ // λ _ → 1₂

    ℂTrace-IsTrace : ∀ ℂ → IsTrace (ℂTrace ℂ)
    ℂTrace-IsTrace (A -[ M ]→ B ⁏ ℂ) = com M λ m → ℂTrace-IsTrace (ℂ m)
    ℂTrace-IsTrace (A -[ M ]→★⁏   ℂ) = com M λ m → ℂTrace-IsTrace (ℂ m)
    ℂTrace-IsTrace end               = end

    ℂObserver-IsSink : ∀ ℂ → IsSink (ℂObserver ℂ)
    ℂObserver-IsSink (A -[ M ]→ B ⁏ ℂ) = com (☐ M) λ { [ m ] → ℂObserver-IsSink (ℂ m) }
    ℂObserver-IsSink (A -[ M ]→★⁏   ℂ) = com M λ m → ℂObserver-IsSink (ℂ m)
    ℂObserver-IsSink end = end

    data R : (p q r : 𝟚) → ★ where
      R011 : R 0₂ 1₂ 1₂
      R101 : R 1₂ 0₂ 1₂
      R000 : R 0₂ 0₂ 0₂
    R° : ∀ {I : ★} (p q r : I → 𝟚) → ★
    R° p q r = ∀ i → R (p i) (q i) (r i)

    module _ {p q r : I → 𝟚} where
        choreo-merge : (ℂ : Choreo I)(pqr : R° p q r) → ⟦ ℂ // p ⟧ → ⟦ ℂ // q ⟧ → ⟦ ℂ // r ⟧
        choreo-merge (A -[ M ]→ B ⁏ ℂ) pqr ℂp ℂq with p A | q A | r A | pqr A | p B | q B | r B | pqr B
        choreo-merge (A -[ M ]→ B ⁏ ℂ) pqr ℂp (m , ℂq) | .0₂ |  1₂ | .1₂ | R011 |  1₂ | .0₂ | .1₂ | R101 = m , choreo-merge (ℂ m) pqr (ℂp m) ℂq
        choreo-merge (A -[ M ]→ B ⁏ ℂ) pqr ℂp (m , ℂq) | .0₂ |  1₂ | .1₂ | R011 |  0₂ |  _  |  _  | _    = m , choreo-merge (ℂ m) pqr (ℂp [ m ]) ℂq
        choreo-merge (A -[ M ]→ B ⁏ ℂ) pqr (m , ℂp) ℂq |  1₂ | .0₂ | .1₂ | R101 | .0₂ |  1₂ | .1₂ | R011 = m , choreo-merge (ℂ m) pqr ℂp (ℂq m)
        choreo-merge (A -[ M ]→ B ⁏ ℂ) pqr (m , ℂp) ℂq |  1₂ | .0₂ | .1₂ | R101 |  _  |  0₂ |  _  | _    = m , choreo-merge (ℂ m) pqr ℂp (ℂq [ m ])
        choreo-merge (A -[ M ]→ B ⁏ ℂ) pqr ℂp ℂq       | .0₂ |  0₂ | .0₂ | R000 | .0₂ |  1₂ | .1₂ | R011 = λ m → choreo-merge (ℂ m) pqr (ℂp [ m ]) (ℂq m)
        choreo-merge (A -[ M ]→ B ⁏ ℂ) pqr ℂp ℂq       | .0₂ |  0₂ | .0₂ | R000 |  1₂ | .0₂ | .1₂ | R101 = λ m → choreo-merge (ℂ m) pqr (ℂp m) (ℂq [ m ])
        choreo-merge (A -[ M ]→ B ⁏ ℂ) pqr ℂp ℂq       | .0₂ |  0₂ | .0₂ | R000 |  0₂ |  0₂ | .0₂ | R000 = λ { [ m ] → choreo-merge (ℂ m) pqr (ℂp [ m ]) (ℂq [ m ]) }
        choreo-merge (A -[ M ]→★⁏ ℂ) pqr ℂp ℂq with p A | q A | r A | pqr A
        choreo-merge (A -[ M ]→★⁏ ℂ) pqr ℂp (m , ℂq) | .0₂ |  1₂ | .1₂ | R011 = m , choreo-merge (ℂ m) pqr (ℂp m) ℂq
        choreo-merge (A -[ M ]→★⁏ ℂ) pqr (m , ℂp) ℂq |  1₂ | .0₂ | .1₂ | R101 = m , choreo-merge (ℂ m) pqr ℂp (ℂq m)
        choreo-merge (A -[ M ]→★⁏ ℂ) pqr ℂp ℂq       | .0₂ |  0₂ | .0₂ | R000 = λ m → choreo-merge (ℂ m) pqr (ℂp m) (ℂq m)
        choreo-merge end pqr ℂp ℂq = _

        {-
    module _ {p q r pq qr pqr : I → 𝟚} where
        choreo-merge-assoc : (ℂ : Choreo I)(Rpqr : R° p qr pqr)(Rqr : R° q r qr)(Rpqr' : R° pq r pqr)(Rpq : R° p q pq) →
                             (ℂp : ⟦ ℂ // p ⟧) (ℂq : ⟦ ℂ // q ⟧) (ℂr : ⟦ ℂ // r ⟧)
                             → choreo-merge ℂ Rpqr ℂp (choreo-merge ℂ Rqr ℂq ℂr) ≡ choreo-merge ℂ Rpqr' (choreo-merge ℂ Rpq ℂp ℂq) ℂr
        choreo-merge-assoc = {!!}
        -}

    R-p-¬p-1 : ∀ (p : I → 𝟚) i → R (p i) (not (p i)) 1₂
    R-p-¬p-1 p i with p i
    R-p-¬p-1 p i | 1₂ = R101
    R-p-¬p-1 p i | 0₂ = R011

    choreo-bi : {p : I → 𝟚}(ℂ : Choreo I) → ⟦ ℂ // p ⟧ → ⟦ ℂ // (not ∘ p) ⟧ → ⟦ ℂTrace ℂ ⟧
    choreo-bi {p} ℂ ℂp ℂ¬p = choreo-merge ℂ (R-p-¬p-1 p) ℂp ℂ¬p

choreo2 : (ℂ : Choreo 𝟚) → ⟦ ℂ // id ⟧ → ⟦ ℂ // not ⟧ → ⟦ ℂTrace ℂ ⟧
choreo2 = choreo-bi

module Choreo3 where
  data 𝟛 : ★ where
    0₃ 1₃ 2₃ : 𝟛
  0₃? 1₃? 2₃? : 𝟛 → 𝟚
  0₃? 0₃ = 1₂
  0₃? _  = 0₂
  1₃? 1₃ = 1₂
  1₃? _  = 0₂
  2₃? 2₃ = 1₂
  2₃? _  = 0₂

  choreo3 : (ℂ : Choreo 𝟛) → ⟦ ℂ // 0₃? ⟧ → ⟦ ℂ // 1₃? ⟧ → ⟦ ℂ // 2₃? ⟧ → ⟦ ℂTrace ℂ ⟧
  choreo3 (0₃ -[ M ]→ 0₃ ⁏ ℂ) (m , p0) p1 p2 = m , choreo3 (ℂ m) p0 (p1 [ m ]) (p2 [ m ])
  choreo3 (0₃ -[ M ]→ 1₃ ⁏ ℂ) (m , p0) p1 p2 = m , choreo3 (ℂ m) p0 (p1 m) (p2 [ m ])
  choreo3 (0₃ -[ M ]→ 2₃ ⁏ ℂ) (m , p0) p1 p2 = m , choreo3 (ℂ m) p0 (p1 [ m ]) (p2 m)
  choreo3 (1₃ -[ M ]→ 0₃ ⁏ ℂ) p0 (m , p1) p2 = m , choreo3 (ℂ m) (p0 m) p1 (p2 [ m ])
  choreo3 (1₃ -[ M ]→ 1₃ ⁏ ℂ) p0 (m , p1) p2 = m , choreo3 (ℂ m) (p0 [ m ]) p1 (p2 [ m ])
  choreo3 (1₃ -[ M ]→ 2₃ ⁏ ℂ) p0 (m , p1) p2 = m , choreo3 (ℂ m) (p0 [ m ]) p1 (p2 m)
  choreo3 (2₃ -[ M ]→ 0₃ ⁏ ℂ) p0 p1 (m , p2) = m , choreo3 (ℂ m) (p0 m) (p1 [ m ]) p2
  choreo3 (2₃ -[ M ]→ 1₃ ⁏ ℂ) p0 p1 (m , p2) = m , choreo3 (ℂ m) (p0 [ m ]) (p1 m) p2
  choreo3 (2₃ -[ M ]→ 2₃ ⁏ ℂ) p0 p1 (m , p2) = m , choreo3 (ℂ m) (p0 [ m ]) (p1 [ m ]) p2
  choreo3 (0₃ -[ M ]→★⁏    ℂ) (m , p0) p1 p2 = m , choreo3 (ℂ m) p0 (p1 m) (p2 m)
  choreo3 (1₃ -[ M ]→★⁏    ℂ) p0 (m , p1) p2 = m , choreo3 (ℂ m) (p0 m) p1 (p2 m)
  choreo3 (2₃ -[ M ]→★⁏    ℂ) p0 p1 (m , p2) = m , choreo3 (ℂ m) (p0 m) (p1 m) p2
  choreo3 end p0 p1 p2 = _

  choreo3' : (ℂ : Choreo 𝟛) → ⟦ ℂ // 0₃? ⟧ → ⟦ ℂ // 1₃? ⟧ → ⟦ ℂ // 2₃? ⟧ → ⟦ ℂTrace ℂ ⟧
  choreo3' ℂ p0 p1 p2 = choreo-merge ℂ (R-p-¬p-1 0₃?) p0 (choreo-merge ℂ R-1-2-¬0 p1 p2)
     where R-1-2-¬0 : ∀ i → R (1₃? i) (2₃? i) (not (0₃? i))
           R-1-2-¬0 0₃ = R000
           R-1-2-¬0 1₃ = R101
           R-1-2-¬0 2₃ = R011
-}
module _
  (funExt : ∀ {a}{b}{A : ★_ a}{B : A → ★_ b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g)
  where
    ≡ᴾ-sound : ∀ {P Q} → P ≡ᴾ Q → P ≡ Q
    ≡ᴾ-sound end              = refl
    ≡ᴾ-sound (com refl M P≡Q) = cong (com' _ M) (funExt λ m → ≡ᴾ-sound (P≡Q m))

≡ᴾ-refl : ∀ P → P ≡ᴾ P
≡ᴾ-refl end         = end
≡ᴾ-refl (com' q M P) = com refl M λ m → ≡ᴾ-refl (P m)

dualᴵᴼ-involutive : ∀ io → dualᴵᴼ (dualᴵᴼ io) ≡ io
dualᴵᴼ-involutive In = refl
dualᴵᴼ-involutive Out = refl

dual-involutive : ∀ P → dual (dual P) ≡ᴾ P
dual-involutive end = end
dual-involutive (com' q M P) = com (dualᴵᴼ-involutive q) M (λ m → dual-involutive (P m))

Trace-idempotent : ∀ P → Trace (Trace P) ≡ᴾ Trace P
Trace-idempotent end         = end
Trace-idempotent (com' _ M P) = com refl M λ m → Trace-idempotent (P m)

Trace-dual-oblivious : ∀ P → Trace (dual P) ≡ᴾ Trace P
Trace-dual-oblivious end         = end
Trace-dual-oblivious (com' _ M P) = com refl M λ m → Trace-dual-oblivious (P m)

Sink : Proto → Proto
Sink = dual ∘ Trace

Tele : Proto → ★
Tele P = ⟦ Trace P ⟧

_>>=_ : (P : Proto) → (Tele P → Proto) → Proto
end       >>= Q = Q _
com' q M P >>= Q = com' q M λ m → P m >>= λ ms → Q (m , ms)

_>>_ : Proto → Proto → Proto
P >> Q = P >>= λ _ → Q

replicateᴾ : ℕ → Proto → Proto
replicateᴾ 0       P = end
replicateᴾ (suc n) P = P >> replicateᴾ n P

{-
++Tele : ∀ (P : Proto){Q : Tele P → Proto} (xs : Tele P) → Tele (Q xs) → Tele (P >>= Q)
++Tele end         _        ys = ys
++Tele (com' q M P) (x , xs) ys = x , ++Tele (P x) xs ys

>>=-right-unit : ∀ P → (P >> end) ≡ᴾ P
>>=-right-unit end         = end
>>=-right-unit (com' q M P) = com q M λ m → >>=-right-unit (P m)

>>=-assoc : ∀ (P : Proto)(Q : Tele P → Proto)(R : Tele (P >>= Q) → Proto)
            → P >>= (λ x → Q x >>= (λ y → R (++Tele P x y))) ≡ᴾ ((P >>= Q) >>= R)
>>=-assoc end         Q R = ≡ᴾ-refl (Q _ >>= R)
>>=-assoc (com' q M P) Q R = com q M λ m → >>=-assoc (P m) (λ ms → Q (m , ms)) (λ ms → R (m , ms))

mutual
    data [_&_≡_]ᶜ : Com → Com → Com → ★₁ where
      Π&   : ∀ q {M P Q R}(P& : ∀ m → [ P m     & Q m ≡ R m ]) → [ Πᶜ    M  P & mk q M Q ≡ mk q M R ]ᶜ
      Π☐&  : ∀ q {M P Q R}(P& : ∀ m → [ P [ m ] & Q m ≡ R m ]) → [ Πᶜ (☐ M) P & mk q M Q ≡ mk q M R ]ᶜ

    data [_&_≡_] : Proto → Proto → Proto → ★₁ where
      &-comm : ∀ {P Q R} → [ P & Q ≡ R ] → [ Q & P ≡ R ]
      end : ∀ {P} → [ end & P ≡ P ]
      com : ∀ {P Q R} → [ P & Q ≡ R ]ᶜ → [ com P & com Q ≡ com R ]

-- pattern Π&Σ P = Π& Σ' P
Π&Π : ∀ {M P Q R}(P& : ∀ m → [ P m & Q m ≡ R m ]) → [ Πᴾ M P & Πᴾ M Q ≡ Πᴾ M R ]
Π&Π P& = com (Π& In P&)
Π&Σ : ∀ {M P Q R}(P& : ∀ m → [ P m & Q m ≡ R m ]) → [ Πᴾ M P & Σᴾ M Q ≡ Σᴾ M R ]
Π&Σ P& = com (Π& Out P&)
Σ&Π : ∀ {M P Q R}(P& : ∀ m → [ P m & Q m ≡ R m ]) → [ Σᴾ M P & Πᴾ M  Q ≡ Σᴾ M R ]
Σ&Π P& = &-comm (Π&Σ (λ m → &-comm (P& m)))

&-dual : ∀ P → [ P & dual P ≡ Trace P ]
&-dual end      = end
&-dual (Σᴾ M P) = Σ&Π λ m → &-dual (P m)
&-dual (Πᴾ M P) = Π&Σ λ m → &-dual (P m)

Dual-sym : ∀ {P Q} → Dual P Q → Dual Q P
Dual-sym end = end
Dual-sym (Π·Σ f) = Σ·Π (λ x → Dual-sym (f x))
Dual-sym (Σ·Π f) = Π·Σ (λ x → Dual-sym (f x))
{-
Dual-sym (Π☐·Σ f) = {!Σ·Π (λ x → Dual-sym (f x))!}
Dual-sym (Σ·Π☐ f) = {!Π·Σ (λ x → Dual-sym (f x))!}
-}
-}

Dual-spec : ∀ P → Dual P (dual P)
Dual-spec end = end
Dual-spec (Πᴾ M P) = Π·Σ λ m → Dual-spec (P m)
Dual-spec (Σᴾ M P) = Σ·Π λ m → Dual-spec (P m)

{-
module _ (funExt : ∀ {a b}{A : ★_ a}{B : A → ★_ b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g)where
  dual-Tele : ∀ P → Tele (dual P) ≡ Tele P
  dual-Tele P = cong ⟦_⟧ (≡ᴾ-sound funExt (Trace-dual-oblivious P))

El : (P : Proto) → (Tele P → ★) → ★
El end         X = X _
El (com' q M P) X = ⟦ q ⟧ᴵᴼ M λ x → El (P x) (λ y → X (x , y))

module ElBind (funExt : ∀ {a b}{A : ★_ a}{B : A → ★_ b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g)where

  El->>= : (P : Proto){Q : Tele P → Proto}{X : Tele (P >>= Q) → ★} → El (P >>= Q) X ≡ El P (λ x → El (Q x) (λ y → X (++Tele P x y)))
  El->>= end         = refl
  El->>= (com' q M P) = cong (⟦ q ⟧ᴵᴼ M) (funExt λ m → El->>= (P m))

tele-com : ∀ P → ⟦ P ⟧ → ⟦ P ⊥⟧ → Tele P
tele-com end      _       _       = _
tele-com (Πᴾ M P) p       (m , q) = m , tele-com (P m) (p m) q
tele-com (Σᴾ M P) (m , p) q       = m , tele-com (P m) p (q m)
-}

>>=-com : (P : Proto){Q : Tele P → Proto}{R : Tele P → Proto}
          → ⟦ P >>= Q  ⟧
          → ⟦ P >>= R ⊥⟧
          → Σ (Tele P) (λ t → ⟦ Q t ⟧ × ⟦ R t ⊥⟧)
>>=-com end      p0       p1       = _ , p0 , p1
>>=-com (Σᴾ M P) (m , p0) p1       = first (_,_ m) (>>=-com (P m) p0 (p1 m))
>>=-com (Πᴾ M P) p0       (m , p1) = first (_,_ m) (>>=-com (P m) (p0 m) p1)

>>-com : (P : Proto){Q R : Proto}
       → ⟦ P >> Q  ⟧
       → ⟦ P >> R ⊥⟧
       → Tele P × ⟦ Q ⟧ × ⟦ R ⊥⟧
>>-com P p q = >>=-com P p q

data ProcessF (this : Proto → ★₁): Com → ★₁ where
  recv : ∀ {M P} (s : (m : M) → this (P m)) → ProcessF this (Πᶜ M P)
  send : ∀ {M P} (m : M) (s : this (P m)) → ProcessF this (Σᶜ M P)

recvS : ∀ {this : Proto → ★₁}{M}{P : ☐ M → Proto} → (..(m : M) → this (P [ m ])) → ProcessF this (Πᶜ (☐ M) P)
recvS = recv ∘ un☐

sendS : ∀ {this : Proto → ★₁}{M}{P : ☐ M → Proto} ..(m : M) → this (P [ m ]) → ProcessF this (Σᶜ (☐ M) P)
sendS m = send [ m ]

data Process : Proto → ★₁ where
  end : Process end
  com : ∀ {P} → ProcessF Process P → Process (com P)

mutual
  SimL : Com → Proto → ★₁
  SimL P Q = ProcessF (flip Sim Q) P

  SimR : Proto → Com → ★₁
  SimR P Q = ProcessF (Sim P) Q

  data Sim : Proto → Proto → ★₁ where
    comL : ∀ {P Q} (sL : SimL P Q) → Sim (com P) Q
    comR : ∀ {P Q} (sR : SimR P Q) → Sim P (com Q)
    end  : Sim end end

sendL : ∀ {M P Q} (m : M) → Sim (P m) Q → Sim (Σᴾ M P) Q
sendL m s = comL (send m s)

sendR : ∀ {M P Q} (m : M) → Sim P (Q m) → Sim P (Σᴾ M Q)
sendR m s = comR (send m s)

recvL : ∀ {M P Q} (s : (m : M) → Sim (P m) Q) → Sim (Πᴾ M P) Q
recvL s = comL (recv s)

recvR : ∀ {M P Q} (s : (m : M) → Sim P (Q m)) → Sim P (Πᴾ M Q)
recvR s = comR (recv s)

data _≈ˢ_ : ∀ {P Q} (s₀ s₁ : Sim P Q) → ★₁ where
  ≈-end : end ≈ˢ end
  ≈-sendL : ∀ {M} {P : M → Proto} {Q} (m : M) {s₀ s₁ : Sim (P m) Q}
          → s₀ ≈ˢ s₁
          → sendL {P = P} m s₀ ≈ˢ sendL m s₁
  ≈-sendR : ∀ {M P} {Q : M → Proto} (m : M) {s₀ s₁ : Sim P (Q m)}
          → s₀ ≈ˢ s₁
          → sendR {Q = Q} m s₀ ≈ˢ sendR m s₁
  ≈-recvL : ∀ {M P Q} {s₀ s₁ : (m : M) → Sim (P m) Q}
          → (p : ∀ m → s₀ m ≈ˢ s₁ m)
          → recvL {P = P} s₀ ≈ˢ recvL s₁
  ≈-recvR : ∀ {M P Q} {s₀ s₁ : (m : M) → Sim P (Q m)}
          → (p : ∀ m → s₀ m ≈ˢ s₁ m)
          → recvR {Q = Q} s₀ ≈ˢ recvR s₁
          {-
  ≈-sendLR : ∀ {Mℓ Mr P Q} (ℓ : Mℓ) (r : Mr) {s₀} {s₁ : Sim (P ℓ) (Q r)}
             → s₀ ≈ˢ sendL {P = P} ℓ (sendR {Q = Q} r s₁)
             → s₀ ≈ˢ sendR {Q = Q} r (sendL {P = P} ℓ s₁)
  ≈-sendRL : ∀ {Mℓ Mr P Q} (ℓ : Mℓ) (r : Mr) {s₀} {s₁ : Sim (P ℓ) (Q r)}
             → s₀ ≈ˢ sendR {Q = Q} r (sendL {P = P} ℓ s₁)
             → s₀ ≈ˢ sendL {P = P} ℓ (sendR {Q = Q} r s₁)
             -}
  {-
  ≈-sendLR : ∀ {Mℓ Mr P Q} (ℓ : Mℓ) (r : Mr) {s : Sim (P ℓ) (Q r)}
             → sendL {P = P} ℓ (sendR {Q = Q} r s) ≈ˢ sendR r (sendL ℓ s)
  ≈-sendRL : ∀ {Mℓ Mr P Q} (ℓ : Mℓ) (r : Mr) {s : Sim (P ℓ) (Q r)}
             → sendR r (sendL ℓ s) ≈ˢ sendL {P = P} ℓ (sendR {Q = Q} r s)
  ≈-sendLR : ∀ {Mℓ Mr P Q} (ℓ : Mℓ) (r : Mr) {s₀ s₁ : Sim (P ℓ) (Q r)}
             → s₀ ≈ˢ s₁
             → sendL {P = P} ℓ (sendR {Q = Q} r s₀) ≈ˢ sendR r (sendL ℓ s₁)
  ≈-sendRL : ∀ {Mℓ Mr P Q} (ℓ : Mℓ) (r : Mr) {s₀ s₁ : Sim (P ℓ) (Q r)}
             → s₀ ≈ˢ s₁
             → sendR r (sendL ℓ s₀) ≈ˢ sendL {P = P} ℓ (sendR {Q = Q} r s₁)
  -}
postulate
  ≈-sendLR : ∀ {Mℓ Mr P Q} (ℓ : Mℓ) (r : Mr) {s : Sim (P ℓ) (Q r)}
             → sendL {P = P} ℓ (sendR {Q = Q} r s) ≈ˢ sendR r (sendL ℓ s)
  ≈-sendRL : ∀ {Mℓ Mr P Q} (ℓ : Mℓ) (r : Mr) {s : Sim (P ℓ) (Q r)}
             → sendR r (sendL ℓ s) ≈ˢ sendL {P = P} ℓ (sendR {Q = Q} r s)
  ≈-sendR-recvL : ∀ {Mℓ Mr P Q} (r : Mr) {s : (ℓ : Mℓ) → Sim (P ℓ) (Q r)}
             → sendR r (recvL s) ≈ˢ recvL {P = P} (λ ℓ → sendR {Q = Q} r (s ℓ))
  ≈-recvR-sendL : ∀ {Mℓ Mr P Q} (r : Mr) {s : (ℓ : Mℓ) → Sim (P ℓ) (Q r)}
             → recvL {P = P} (λ ℓ → sendR {Q = Q} r (s ℓ)) ≈ˢ sendR r (recvL s)
  ≈-recvRL : ∀ {Mℓ Mr P Q} {s : (ℓ : Mℓ) (r : Mr) → Sim (P ℓ) (Q r)}
             → recvR (λ r → recvL (λ ℓ → s ℓ r)) ≈ˢ recvL {P = P} (λ ℓ → recvR {Q = Q} (s ℓ))
  ≈-recvLR : ∀ {Mℓ Mr P Q} {s : (ℓ : Mℓ) (r : Mr) → Sim (P ℓ) (Q r)}
             → recvL {P = P} (λ ℓ → recvR {Q = Q} (s ℓ)) ≈ˢ recvR (λ r → recvL (λ ℓ → s ℓ r))

≈ˢ-refl : ∀ {P Q} (s : Sim P Q) → s ≈ˢ s
≈ˢ-refl (comL (recv s)) = ≈-recvL (λ m → ≈ˢ-refl (s m))
≈ˢ-refl (comL (send m s)) = ≈-sendL m (≈ˢ-refl s)
≈ˢ-refl (comR (recv s)) = ≈-recvR (λ m → ≈ˢ-refl (s m))
≈ˢ-refl (comR (send m s)) = ≈-sendR m (≈ˢ-refl s)
≈ˢ-refl end = ≈-end

≈ˢ-sym : ∀ {P Q} {s₀ s₁ : Sim P Q} → s₀ ≈ˢ s₁ → s₁ ≈ˢ s₀
≈ˢ-sym ≈-end = ≈-end
≈ˢ-sym (≈-sendL m p) = ≈-sendL m (≈ˢ-sym p)
≈ˢ-sym (≈-sendR m p) = ≈-sendR m (≈ˢ-sym p)
≈ˢ-sym (≈-recvL x) = ≈-recvL (λ m → ≈ˢ-sym (x m))
≈ˢ-sym (≈-recvR x) = ≈-recvR (λ m → ≈ˢ-sym (x m))
{-
≈ˢ-sym (≈-sendLR ℓ r p) = {!≈-sendRL ℓ r ?!}
≈ˢ-sym (≈-sendRL ℓ r p) = {!≈-sendLR ℓ r!}
-}
{-
≈ˢ-sym (≈-sendLR ℓ r p) = ≈-sendRL ℓ r (≈ˢ-sym p)
≈ˢ-sym (≈-sendRL ℓ r p) = ≈-sendLR ℓ r (≈ˢ-sym p)
-}

≈ˢ-trans : ∀ {P Q} → Transitive (_≈ˢ_ {P} {Q})
≈ˢ-trans ≈-end q = q
≈ˢ-trans (≈-sendL m x) (≈-sendL .m x₁) = ≈-sendL m (≈ˢ-trans x x₁)
≈ˢ-trans (≈-sendR m x) (≈-sendR .m x₁) = ≈-sendR m (≈ˢ-trans x x₁)
≈ˢ-trans (≈-recvL x) (≈-recvL x₁) = ≈-recvL (λ m → ≈ˢ-trans (x m) (x₁ m))
≈ˢ-trans (≈-recvR x) (≈-recvR x₁) = ≈-recvR (λ m → ≈ˢ-trans (x m) (x₁ m))

data LR : ★ where
  `L `R : LR

[L:_R:_] : ∀ {a} {A : ★_ a} (l r : A) → LR → A 
[L: l R: r ] `L = l
[L: l R: r ] `R = r

_⊕ᴾ_ : (l r : Proto) → Proto
l ⊕ᴾ r = Σᴾ LR [L: l R: r ]

_&ᴾ_ : (l r : Proto) → Proto
l &ᴾ r = Πᴾ LR [L: l R: r ]

_>>ᶜ_ : (P : Com) → (Proto → Proto) → Com
P >>ᶜ S = record P { P = λ m → S (Com.P P m) }

module Equivalences
  (funExt : ∀ {a}{b}{A : ★_ a}{B : A → ★_ b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g)
  where

  record Equiv {A B : ★}(f : A → B) : ★ where
    field
      linv : B → A
      is-linv : ∀ x → linv (f x) ≡ x
      rinv : B → A
      is-rinv : ∀ x → f (rinv x) ≡ x

  idᴱ : ∀ {A} → Equiv {A} id
  idᴱ = record
            { linv = id
            ; is-linv = λ _ → refl
            ; rinv = id
            ; is-rinv = λ _ → refl
            }

  module _ {A B C}{g : B → C}{f : A → B} where
    _∘ᴱ_ : Equiv g → Equiv f → Equiv (g ∘ f)
    gᴱ ∘ᴱ fᴱ = record { linv = F.linv ∘ G.linv ; is-linv = λ x → cong F.linv (G.is-linv (f x)) ∙ F.is-linv x
                      ; rinv = F.rinv ∘ G.rinv ; is-rinv = λ x → cong g (F.is-rinv _) ∙ G.is-rinv x }
      where
        module G = Equiv gᴱ
        module F = Equiv fᴱ

  _≃_ : ★ → ★ → ★
  A ≃ B = Σ (A → B) Equiv

  module _ {a}{b}{A : ★_ a}{B : A → ★_ b} where
    Σ-ext : ∀ {x y : Σ A B} → (p : fst x ≡ fst y) → subst B p (snd x) ≡ snd y → x ≡ y
    Σ-ext refl = cong (_,_ _)

data ViewProc : ∀ P → ⟦ P ⟧ → ★₁ where
  send : ∀ M(P : M → Proto)(m : M)(p : ⟦ P m ⟧) → ViewProc (Σᴾ M P) (m , p)
  recv : ∀ M(P : M → Proto)(p : ((m : M) → ⟦ P m ⟧)) → ViewProc (Πᴾ M P) p
  end  : ViewProc end _

view-proc : ∀ P (p : ⟦ P ⟧) → ViewProc P p
view-proc end      _       = end
view-proc (Πᴾ M P) p       = recv _ _ p
view-proc (Σᴾ M P) (m , p) = send _ _ m p

data ViewCom : ∀ P → ⟦ com P ⟧ → ★₁ where
  send : ∀{M}(P : M → Proto)(m : M)(p : ⟦ P m ⟧) → ViewCom (Σᶜ M P) (m , p)
  recv : ∀{M}(P : M → Proto)(p : ((m : M) → ⟦ P m ⟧)) → ViewCom (Πᶜ M P) p

view-com : ∀ P (p : ⟦ com P ⟧) → ViewCom P p
view-com (Πᶜ M P) p       = recv _ p
view-com (Σᶜ M P) (m , p) = send _ m p

module _
  (funExt : ∀ {a}{b}{A : ★_ a}{B : A → ★_ b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g)
  where

  open Equivalences funExt

  _⅋ᴾ_ : Proto → Proto → Proto
  end    ⅋ᴾ Q       = Q
  Πᴾ M P ⅋ᴾ Q       = Πᴾ M λ m → P m ⅋ᴾ Q
  P      ⅋ᴾ end     = P
  P      ⅋ᴾ Πᴾ M  Q = Πᴾ M λ m → P ⅋ᴾ Q m
  Σᴾ M P ⅋ᴾ Σᴾ M' Q = Σᴾ (M ⊎ M') [inl: (λ m → P m ⅋ᴾ Σᴾ M' Q)
                                  ,inr: (λ m' → Σᴾ M P ⅋ᴾ Q m') ]

  data View-⅋ : ∀ P Q → ⟦ P ⅋ᴾ Q ⟧ → ★₁ where
    sendL' : ∀ {M M'}(P : M → Proto)(Q : M' → Proto)(m  : M )(p : ⟦ P m ⅋ᴾ Σᴾ M' Q ⟧) → View-⅋ (Σᴾ M P) (Σᴾ M' Q) (inl m  , p)
    sendR' : ∀ {M M'}(P : M → Proto)(Q : M' → Proto)(m' : M')(p : ⟦ Σᴾ M P ⅋ᴾ Q m' ⟧) → View-⅋ (Σᴾ M P) (Σᴾ M' Q) (inr m' , p)
    recvL' : ∀ {M} (P : M → Proto) Q (p : ((m : M) → ⟦ P m ⅋ᴾ Q ⟧)) → View-⅋ (Πᴾ M P) Q p
    recvR' : ∀ {M M'} (P : M → Proto) (Q : M' → Proto)(p : (m' : M') → ⟦ Σᴾ M P ⅋ᴾ Q m' ⟧) → View-⅋ (Σᴾ M P) (Πᴾ M' Q) p
    endL   : ∀ Q (p : ⟦ Q ⟧) → View-⅋ end Q p
    endR   : ∀ {M} (P : M → Proto) (p : ⟦ Σᴾ M P ⟧) → View-⅋ (Σᴾ M P) end p

  view-⅋ : ∀ P Q (p : ⟦ P ⅋ᴾ Q ⟧) → View-⅋ P Q p
  view-⅋ end Q p = endL Q p
  view-⅋ (Πᴾ M P) Q p = recvL' P Q p
  view-⅋ (Σᴾ M P) end p = endR P p
  view-⅋ (Σᴾ M P) (Πᴾ M' Q) p = recvR' P Q p
  view-⅋ (com (mk Out M P)) (com (mk Out M' Q)) (inl x , p) = sendL' P Q x p
  view-⅋ (com (mk Out M P)) (com (mk Out M' Q)) (inr y , p) = sendR' P Q y p

  ⅋ᴾ-assoc : ∀ P Q R → ⟦ P ⅋ᴾ (Q ⅋ᴾ R) ⟧ → ⟦ (P ⅋ᴾ Q) ⅋ᴾ R ⟧
  ⅋ᴾ-assoc end      Q        R         s                 = s
  ⅋ᴾ-assoc (Πᴾ _ P) Q        R         s m               = ⅋ᴾ-assoc (P m) _ _ (s m)
  ⅋ᴾ-assoc (Σᴾ _ P) end      R         s                 = s
  ⅋ᴾ-assoc (Σᴾ _ P) (Πᴾ _ Q) R         s m               = ⅋ᴾ-assoc (Σᴾ _ P) (Q m) _ (s m)
  ⅋ᴾ-assoc (Σᴾ _ P) (Σᴾ _ Q) end       s                 = s
  ⅋ᴾ-assoc (Σᴾ _ P) (Σᴾ _ Q) (Πᴾ M R)  s m               = ⅋ᴾ-assoc (Σᴾ _ P) (Σᴾ _ Q) (R m) (s m)
  ⅋ᴾ-assoc (Σᴾ _ P) (Σᴾ _ Q) (Σᴾ Mr R) (inl m , s)       = inl (inl m) , ⅋ᴾ-assoc (P m) (Σᴾ _ Q) (Σᴾ _ R) s
  ⅋ᴾ-assoc (Σᴾ _ P) (Σᴾ _ Q) (Σᴾ Mr R) (inr (inl m) , s) = inl (inr m) , ⅋ᴾ-assoc (Σᴾ _ P) (Q m) (Σᴾ _ R) s
  ⅋ᴾ-assoc (Σᴾ _ P) (Σᴾ _ Q) (Σᴾ Mr R) (inr (inr m) , s) = inr m       , ⅋ᴾ-assoc (Σᴾ _ P) (Σᴾ _ Q) (R m) s

  ⅋ᴾ-rend : ∀ P → ⟦ P ⅋ᴾ end ⟧  → ⟦ P ⟧
  ⅋ᴾ-rend end      p = p
  ⅋ᴾ-rend (Πᴾ _ P) p = λ m → ⅋ᴾ-rend (P m) (p m)
  ⅋ᴾ-rend (Σᴾ _ _) p = p

  ⅋ᴾ-rend' : ∀ P  → ⟦ P ⟧ → ⟦ P ⅋ᴾ end ⟧
  ⅋ᴾ-rend' end      p = p
  ⅋ᴾ-rend' (Πᴾ _ P) p = λ m → ⅋ᴾ-rend' (P m) (p m)
  ⅋ᴾ-rend' (Σᴾ _ _) p = p

  {-
  ⅋ᴾ-rend-equiv : ∀ P → Equiv (⅋ᴾ-rend P)
  ⅋ᴾ-rend-equiv end     = idᴱ
  ⅋ᴾ-rend-equiv (com _) = idᴱ
  -}

  ⅋ᴾ-sendR : ∀ {M}P{Q : M → Proto}(m : M) → ⟦ P ⅋ᴾ Q m ⟧ → ⟦ P ⅋ᴾ com' Out M Q ⟧
  ⅋ᴾ-sendR end     m p = m , p
  ⅋ᴾ-sendR (Σᴾ M P) m p = inr m , p
  ⅋ᴾ-sendR (Πᴾ M P) m p = λ x → ⅋ᴾ-sendR (P x) m (p x)

  ⅋ᴾ-sendL : ∀ {M}{P : M → Proto} Q (m : M) → ⟦ P m ⅋ᴾ Q ⟧ → ⟦ Σᴾ M P ⅋ᴾ Q ⟧
  ⅋ᴾ-sendL {P = P} end      m p = m , ⅋ᴾ-rend (P m) p
  ⅋ᴾ-sendL         (Πᴾ M Q) m p = λ m' → ⅋ᴾ-sendL (Q m') m {!p!}
  ⅋ᴾ-sendL         (Σᴾ M Q) m p = {!!} , p

  {-
  ⅋ᴾ-sendR : ∀ {M} P Q → ⟦ P ⅋ᴾ Πᴾ M Q ⟧ → (m : M) → ⟦ P ⅋ᴾ Q m ⟧
  ⅋ᴾ-sendR P Q s m = {!!}
  -}

  ⅋ᴾ-recvR : ∀ {M} P Q → ((m : M) → ⟦ P ⅋ᴾ Q m ⟧) → ⟦ P ⅋ᴾ Πᴾ M Q ⟧
  ⅋ᴾ-recvR end      Q s = s
  ⅋ᴾ-recvR (Πᴾ M P) Q s = λ x → ⅋ᴾ-recvR (P x) Q (λ m → s m x)
  ⅋ᴾ-recvR (Σᴾ M P) Q s = s

  mutual
    ⅋ᴾ-! : ∀ P Q → ⟦ P ⅋ᴾ Q ⟧ → ⟦ Q ⅋ᴾ P ⟧
    ⅋ᴾ-! P Q p = {!!}

    ⅋ᴾ-!-view : ∀ {P Q} {pq : ⟦ P ⅋ᴾ Q ⟧} → View-⅋ P Q pq → ⟦ Q ⅋ᴾ P ⟧
    ⅋ᴾ-!-view (sendL' P Q m p) = ⅋ᴾ-sendR (Σᴾ _ Q) m (⅋ᴾ-! (P m) (com (mk Out _ Q)) p)
    ⅋ᴾ-!-view (sendR' P Q m' p) = {!⅋ᴾ-sendL (Σᴾ _ P) m'!}
    ⅋ᴾ-!-view (recvL' P Q pq) = {!!}
    ⅋ᴾ-!-view (recvR' P Q pq) = {!!}
    ⅋ᴾ-!-view (endL Q pq) = {!!}
    ⅋ᴾ-!-view (endR P pq) = {!!}

  {-
  end Q p = ⅋ᴾ-rend' Q p
  {-
  ⅋ᴾ-! end Q p = ⅋ᴾ-rend' Q p
  ⅋ᴾ-! (Πᴾ M P) end p x = ⅋ᴾ-! (P x) end (p x)
  ⅋ᴾ-! (Πᴾ M P) (Πᴾ M' Q) p = λ m' → {!⅋ᴾ-! (Π !}
  ⅋ᴾ-! (Πᴾ M P) (Σᴾ M' Q) p = λ m → ⅋ᴾ-! (P m) (com (mk Out M' Q)) (p m)
  ⅋ᴾ-! (Σᴾ M P) end       p = p
  ⅋ᴾ-! (Σᴾ M P) (Πᴾ M' Q) p = λ m' → ⅋ᴾ-! (com (mk Out M P)) (Q m') (p m')
  ⅋ᴾ-! (Σᴾ M P) (Σᴾ M' Q) (inl m , p) = inr m , (⅋ᴾ-! (P m) (com (mk Out M' Q)) p)
  ⅋ᴾ-! (Σᴾ M P) (Σᴾ M' Q) (inr m , p) = inl m , (⅋ᴾ-! (com (mk Out M P)) (Q m) p)

  {-
  ⅋ᴾ-apply : ∀ P Q → ⟦ ⅋ᴾ P Q ⟧ → ⟦ dual P ⟧ → ⟦ Q ⟧
  ⅋ᴾ-apply end      Q         s           p       = s
  ⅋ᴾ-apply (Πᴾ M P) Q         s           (m , p) = ⅋ᴾ-apply (P m) Q (s m) p
  ⅋ᴾ-apply (Σᴾ M P) end       s           p       = _
  ⅋ᴾ-apply (Σᴾ M P) (Πᴾ M' Q) s           p m'    = ⅋ᴾ-apply (Σᴾ M P) (Q m') (s m') p
  ⅋ᴾ-apply (Σᴾ M P) (Σᴾ M' Q) (inl m , s) p       = ⅋ᴾ-apply (P m) (Σᴾ M' Q) s (p m)
  ⅋ᴾ-apply (Σᴾ M P) (Σᴾ M' Q) (inr m , s) p       = m , ⅋ᴾ-apply (Σᴾ M P) (Q m) s p
  -}

  {-
module V4
  (funExt : ∀ {a}{b}{A : ★_ a}{B : A → ★_ b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g)
  where
  mutual
    _⅋ᴾ_ : Proto → Proto → Proto
    end   ⅋ᴾ Q     = Q
    P     ⅋ᴾ end   = P
    com P ⅋ᴾ com Q = Σᴾ LR (P ⅋ᶜ Q)

    _⅋ᶜ_ : Com → Com → LR → Proto
    (Pᴸ ⅋ᶜ Pᴿ) `L = Pᴸ ⅋ᶜL Pᴿ
    (Pᴸ ⅋ᶜ Pᴿ) `R = Pᴸ ⅋ᶜR Pᴿ

    _⅋ᶜL_ : Com → Com → Proto
    (mk qᴸ Mᴸ Pᴸ) ⅋ᶜL Q = com' qᴸ Mᴸ (λ m → Pᴸ m ⅋ᴾ com Q)

    _⅋ᶜR_ : Com → Com → Proto
    P ⅋ᶜR (mk qᴿ Mᴿ Pᴿ) = com' qᴿ Mᴿ (λ m → com P ⅋ᴾ Pᴿ m)

  mutual
    _oxᴾ_ : Proto → Proto → Proto
    end    oxᴾ Q      = Q
    P      oxᴾ end    = P
    com Pᴸ oxᴾ com Pᴿ = Πᴾ LR (Pᴸ oxᶜ Pᴿ)

    _oxᶜ_ : Com → Com → LR → Proto
    (Pᴸ oxᶜ Pᴿ) `L = Pᴸ oxᶜL Pᴿ
    (Pᴸ oxᶜ Pᴿ) `R = Pᴸ oxᶜR Pᴿ

    _oxᶜL_ : Com → Com → Proto
    (mk qᴸ Mᴸ Pᴸ) oxᶜL Q = com' qᴸ Mᴸ (λ m → Pᴸ m oxᴾ com Q)

    _oxᶜR_ : Com → Com → Proto
    P oxᶜR (mk qᴿ Mᴿ Pᴿ) = com' qᴿ Mᴿ (λ m → com P oxᴾ Pᴿ m)

  data Viewox : ∀ P Q → ⟦ P oxᴾ Q ⟧ → ★₁ where
    com  : ∀{P Q}(p : ⟦ Πᴾ LR (P oxᶜ Q) ⟧) → Viewox (com P) (com Q) p
    endL : ∀{Q}(p : ⟦ Q ⟧) → Viewox end Q p
    endR : ∀{P}(p : ⟦ com P ⟧) → Viewox (com P) end p

  viewox : ∀ P Q (p : ⟦ P oxᴾ Q ⟧) → Viewox P Q p
  viewox end Q p = endL p
  viewox (com P) end p = endR p
  viewox (com P) (com Q) p = com p

  data View-∘ : ∀ P Q R → ⟦ P ⅋ᴾ Q ⟧ → ⟦ dual Q ⅋ᴾ R ⟧ → ★₁ where
    sendLL : ∀ {M} (P : M → Proto) Q R (m : M)(p : ⟦ P m ⅋ᴾ com Q ⟧)(q : ⟦ dual (com Q) ⅋ᴾ R ⟧)
             → View-∘ (Σᴾ M P) (com Q) R (`L , m , p) q
    recvLL : ∀ {M} (P : M → Proto) Q R
               (p : ((m : M) → ⟦ P m ⅋ᴾ com Q ⟧))(q : ⟦ dual (com Q) ⅋ᴾ R ⟧)
             → View-∘ (Πᴾ M P) (com Q) R (`L , p) q
    sendRR : ∀ {M} P Q (R : M → Proto)(m : M)(p : ⟦ com P ⅋ᴾ com Q ⟧)(q : ⟦ dual (com Q) ⅋ᴾ R m ⟧)
             → View-∘ (com P) (com Q) (Σᴾ M R) p (`R , m , q)
    recvRR : ∀ {M} P Q (R : M → Proto)
               (p : ⟦ com P ⅋ᴾ com Q ⟧)(q : (m : M) → ⟦ dual (com Q) ⅋ᴾ R m ⟧)
             → View-∘ (com P) (com Q) (Πᴾ M R) p (`R , q)

    sendR-recvL : ∀ {M} P (Q : M → Proto) R (m : M)(p : ⟦ com P ⅋ᴾ Q m ⟧)(q : (m : M) → ⟦ dual (Q m) ⅋ᴾ com R ⟧)
             → View-∘ (com P) (Σᴾ M Q) (com R) (`R , m , p) (`L , q)
    recvR-sendL : ∀ {M} P (Q : M → Proto) R (p : (m : M) → ⟦ com P ⅋ᴾ Q m ⟧)(m : M)(q : ⟦ dual (Q m) ⅋ᴾ com R ⟧)
             → View-∘ (com P) (Πᴾ M Q) (com R) (`R , p) (`L , m , q)

    endL : ∀ Q R
            → (q : ⟦ Q ⟧)(qr : ⟦ dual Q ⅋ᴾ R ⟧)
            → View-∘ end Q R q qr

    endM  : ∀ P R
            → (p : ⟦ com P ⟧)(r : ⟦ R ⟧)
            → View-∘ (com P) end R p r
    endR : ∀ P Q
            → (p : ⟦ com P ⅋ᴾ com Q ⟧)(q : ⟦ dual (com Q) ⟧)
            → View-∘ (com P) (com Q) end p q

  view-∘ : ∀ P Q R (pq : ⟦ P ⅋ᴾ Q ⟧)(qr : ⟦ dual Q ⅋ᴾ R ⟧) → View-∘ P Q R pq qr
  view-∘ P Q R pq qr = view-∘-view (view-⅋ P Q pq) (view-⅋ (dual Q) R qr)
   where
    view-∘-view : ∀ {P Q R}{pq : ⟦ P ⅋ᴾ Q ⟧}{qr : ⟦ dual Q ⅋ᴾ R ⟧} → View-⅋ P Q pq → View-⅋ (dual Q) R qr → View-∘ P Q R pq qr
    view-∘-view (sendL' _ _ _ _) _                 = sendLL _ _ _ _ _ _
    view-∘-view (recvL' _ _ _)   _                 = recvLL _ _ _ _ _
    view-∘-view (sendR' _ _ _ _) (sendR' ._ _ _ _) = sendRR _ _ _ _ _ _
    view-∘-view (sendR' _ _ _ _) (recvL' ._ _ _)   = sendR-recvL _ _ _ _ _ _
    view-∘-view (sendR' _ _ _ _) (recvR' ._ _ _)   = recvRR _ _ _ _ _
    view-∘-view (sendR' _ _ _ _) (endR ._ _)       = endR _ _ _ _
    view-∘-view (recvR' _ _ _)   (sendL' ._ _ _ _) = recvR-sendL _ _ _ _ _ _
    view-∘-view (recvR' _ _ _)   (sendR' ._ _ _ _) = sendRR _ _ _ _ _ _
    view-∘-view (recvR' _ _ _)   (recvR' ._ _ _)   = recvRR _ _ _ _ _
    view-∘-view (recvR' _ _ _)   (endR ._ ._)      = endR _ _ _ _
    view-∘-view (endL _ _)       _                 = endL _ _ _ _
    view-∘-view (endR _ _)       _                 = endM _ _ _ _

  ⅋ᴾ-rend : ∀ P → ⟦ P ⅋ᴾ end ⟧  → ⟦ P ⟧
  ⅋ᴾ-rend end     = id
  ⅋ᴾ-rend (com _) = id

  ⅋ᴾ-rend-equiv : ∀ P → Equiv (⅋ᴾ-rend P)
  ⅋ᴾ-rend-equiv end     = idᴱ
  ⅋ᴾ-rend-equiv (com _) = idᴱ

  ⅋ᴾ-sendR : ∀ {M}P{Q : M → Proto}(m : M) → ⟦ P ⅋ᴾ Q m ⟧ → ⟦ P ⅋ᴾ com' Out M Q ⟧
  ⅋ᴾ-sendR end     m p = m , p
  ⅋ᴾ-sendR (com P) m p = `R , (m , p)

  ⅋ᴾ-sendL : ∀ {M}{P : M → Proto} Q (m : M) → ⟦ P m ⅋ᴾ Q ⟧ → ⟦ Σᴾ M P ⅋ᴾ Q ⟧
  ⅋ᴾ-sendL {P = P} end     m p = m , ⅋ᴾ-rend (P m) p
  ⅋ᴾ-sendL         (com _) m p = `L , (m , p)

  ⅋ᴾ-recvR : ∀ {M}P{Q : M → Proto} → ((m : M) → ⟦ P ⅋ᴾ Q m ⟧) → ⟦ P ⅋ᴾ com' In M Q ⟧
  ⅋ᴾ-recvR end     f = f
  ⅋ᴾ-recvR (com _) f = `R , f

  ⅋ᴾ-recvL : ∀ {M}{P : M → Proto}Q → ((m : M) → ⟦ P m ⅋ᴾ Q ⟧) → ⟦ Πᴾ M P ⅋ᴾ Q ⟧
  ⅋ᴾ-recvL {P = P} end     f x = ⅋ᴾ-rend (P x) (f x)
  ⅋ᴾ-recvL         (com _) f = `L , f

  oxᴾ-rend : ∀ P → ⟦ P oxᴾ end ⟧  → ⟦ P ⟧
  oxᴾ-rend end     = id
  oxᴾ-rend (com x) = id

  oxᴾ-sendR : ∀ {M P}{Q : M → Proto}(m : M) → ⟦ P ⅋ᴾ Q m ⟧ → ⟦ P ⅋ᴾ com' Out M Q ⟧
  oxᴾ-sendR {P = end} m p = m , p
  oxᴾ-sendR {P = com x} m p = `R , (m , p)

  ⅋ᴾ-id : ∀ P → ⟦ dual P ⅋ᴾ P ⟧
  ⅋ᴾ-id end = _
  ⅋ᴾ-id (com (mk In M P))  = `R , λ m → ⅋ᴾ-sendL (P m) m (⅋ᴾ-id (P m))
  ⅋ᴾ-id (com (mk Out M P)) = `L , λ m → ⅋ᴾ-sendR (dual (P m)) m (⅋ᴾ-id (P m))

  module _ where
    ⅋ᴾ-comm : ∀ P Q → ⟦ P ⅋ᴾ Q ⟧ ≃ ⟦ Q ⅋ᴾ P ⟧
    ⅋ᴾ-comm = λ P Q → to P Q , equiv P Q
      where
      to : ∀ P Q → ⟦ P ⅋ᴾ Q ⟧ → ⟦ Q ⅋ᴾ P ⟧
      to end end pq = pq
      to end (com x) pq = pq
      to (com x) end pq = pq
      to (com (mk In M P)) (com x₁) (`L , pq) = `R , (λ m → to (P m) (com x₁) (pq m))
      to (com (mk Out M P)) (com x₁) (`L , m , pq) = `R , m , to (P m) (com x₁) pq
      to (com x) (com (mk In M P)) (`R , pq) = `L , (λ m → to (com x) (P m) (pq m))
      to (com x) (com (mk Out M P)) (`R , m , pq) = `L , m , to (com x) (P m) pq

      toto : ∀ P Q (x : ⟦ P ⅋ᴾ Q ⟧) → to Q P (to P Q x) ≡ x
      toto end end x = refl
      toto end (com (mk io M P)) x₁ = refl
      toto (com (mk io M P)) end x₁ = refl
      toto (com (mk In M P)) (com (mk In M₁ P₁)) (`L , pq) = Σ-ext refl (funExt λ x → toto (P x) (com' In M₁ P₁) (pq x))
      toto (com (mk In M P)) (com (mk Out M₁ P₁)) (`L , pq) = Σ-ext refl (funExt λ x → toto (P x) (com' Out M₁ P₁) (pq x))
      toto (com (mk Out M P)) (com (mk In M₁ P₁)) (`L , m , pq) = Σ-ext refl (Σ-ext refl (toto (P m) (com' In M₁ P₁) pq))
      toto (com (mk Out M P)) (com (mk Out M₁ P₁)) (`L , m , pq) = Σ-ext refl (Σ-ext refl (toto (P m) (com' Out M₁ P₁) pq))
      toto (com (mk In M P)) (com (mk In M₁ P₁)) (`R , pq) = Σ-ext refl (funExt (λ x → toto (com' In M P) (P₁ x) (pq x)))
      toto (com (mk In M P)) (com (mk Out M₁ P₁)) (`R , m , pq) = Σ-ext refl (Σ-ext refl (toto (com' In M P) (P₁ m) pq))
      toto (com (mk Out M P)) (com (mk In M₁ P₁)) (`R , pq) = Σ-ext refl (funExt (λ x → toto (com' Out M P) (P₁ x) (pq x)))
      toto (com (mk Out M P)) (com (mk Out M₁ P₁)) (`R , m , pq) = Σ-ext refl (Σ-ext refl (toto (com' Out M P) (P₁ m) pq))

      equiv : ∀ P Q → Equiv (to P Q)
      equiv P Q = record { linv = to Q P ; is-linv = toto P Q ; rinv = to Q P ; is-rinv = toto Q P }

  ⅋ᴾ-assoc : ∀ P Q R → ⟦ (P ⅋ᴾ Q) ⅋ᴾ R ⟧ ≃ ⟦ P ⅋ᴾ (Q ⅋ᴾ R) ⟧
  ⅋ᴾ-assoc P Q R = {!!}

  ⅋ᴾ-oxᴾ : ∀ P Q → ⟦ P ⅋ᴾ Q ⟧ ≃ ⟦ dual P oxᴾ dual Q ⊥⟧
  ⅋ᴾ-oxᴾ P Q = {!!}
  
  oxᴾ-comm : ∀ P Q → ⟦ P oxᴾ Q ⟧ ≃ ⟦ Q oxᴾ P ⟧
  oxᴾ-comm P Q = {!!}

  oxᴾ-assoc : ∀ P Q R → ⟦ (P oxᴾ Q) oxᴾ R ⟧ ≃ ⟦ P oxᴾ (Q oxᴾ R) ⟧
  oxᴾ-assoc P Q R = {!!}

  commaᴾ : ∀ P Q → ⟦ P ⟧ → ⟦ Q ⟧ → ⟦ P oxᴾ Q ⟧
  commaᴾ end      Q        p       q = q
  commaᴾ (com _)  end      p       q = p
  commaᴾ (Σᴾ M P) (com Q)  (m , p) q `L = m , commaᴾ (P m) (com Q) p q
  commaᴾ (Πᴾ M P) (com Q)  p       q `L = λ m → commaᴾ (P m) (com Q) (p m) q
  commaᴾ (com P)  (Σᴾ M Q) p (m , q) `R = m , commaᴾ (com P) (Q m) p q
  commaᴾ (com P)  (Πᴾ M Q) p       q `R = λ m → commaᴾ (com P) (Q m) p (q m)

  ×→oxᴾ : ∀ P Q → ⟦ P ⟧ × ⟦ Q ⟧ → ⟦ P oxᴾ Q ⟧
  ×→oxᴾ P Q (p , q) = commaᴾ P Q p q

  oxᴾ-fst : ∀ P Q → ⟦ P oxᴾ Q ⟧ → ⟦ P ⟧
  oxᴾ-fst end      Q       pq = _
  oxᴾ-fst (com _)  end     pq = pq
  oxᴾ-fst (Πᴾ M P) (com Q) pq = λ m → oxᴾ-fst (P m) (com Q) (pq `L m)
  oxᴾ-fst (Σᴾ M P) (com Q) pq = ×-map id (λ {x} → oxᴾ-fst (P x) (com Q)) (pq `L)

  oxᴾ-snd : ∀ P Q → ⟦ P oxᴾ Q ⟧ → ⟦ Q ⟧
  oxᴾ-snd end     Q         pq = pq
  oxᴾ-snd (com _) end       pq = _
  oxᴾ-snd (com P) (Πᴾ M' Q) pq = λ m' → oxᴾ-snd (com P) (Q m') (pq `R m')
  oxᴾ-snd (com P) (Σᴾ M' Q) pq = ×-map id (λ {m'} → oxᴾ-snd (com P) (Q m')) (pq `R)

  oxᴾ→× : ∀ P Q → ⟦ P oxᴾ Q ⟧ → ⟦ P ⟧ × ⟦ Q ⟧
  oxᴾ→× P Q p = oxᴾ-fst P Q p , oxᴾ-snd P Q p

  oxᴾ-comma-fst : ∀ P Q (p : ⟦ P ⟧)(q : ⟦ Q ⟧) → oxᴾ-fst P Q (commaᴾ P Q p q) ≡ p
  oxᴾ-comma-fst end      Q       p  q = refl
  oxᴾ-comma-fst (com P)  end     p  q = refl
  oxᴾ-comma-fst (com P)  (com Q) p  q with view-com P p
  oxᴾ-comma-fst (com ._) (com Q) ._ q | send P m p = cong (_,_ m) (oxᴾ-comma-fst (P m) (com Q) p q)
  oxᴾ-comma-fst (com ._) (com Q) ._ q | recv P p   = funExt λ m → oxᴾ-comma-fst (P m) (com Q) (p m) q

  oxᴾ-comma-snd : ∀ P Q (p : ⟦ P ⟧)(q : ⟦ Q ⟧) → oxᴾ-snd P Q (commaᴾ P Q p q) ≡ q
  oxᴾ-comma-snd end     Q        p  q = refl
  oxᴾ-comma-snd (com P) end      p  q = refl
  oxᴾ-comma-snd (com P) (com Q)  p  q with view-com Q q
  oxᴾ-comma-snd (Πᴾ _ P) (com ._) p ._ | send Q m q = cong (_,_ m) (oxᴾ-comma-snd (Πᴾ _ P) (Q m) p q)
  oxᴾ-comma-snd (Σᴾ _ P) (com ._) p ._ | send Q m q = cong (_,_ m) (oxᴾ-comma-snd (Σᴾ _ P) (Q m) p q)
  oxᴾ-comma-snd (Πᴾ _ P) (com ._) p ._ | recv Q q   = funExt λ m → oxᴾ-comma-snd (Πᴾ _ P) (Q m) p (q m)
  oxᴾ-comma-snd (Σᴾ _ P) (com ._) p ._ | recv Q q   = funExt λ m → oxᴾ-comma-snd (Σᴾ _ P) (Q m) p (q m)

  {-
  oxᴾ→×-rinv : ∀ {P Q} (p : ⟦ P oxᴾ Q ⟧) → ×→oxᴾ P Q (oxᴾ→× P Q p) ≡ p
  oxᴾ→×-rinv {P} {Q} p with viewox P Q p
  oxᴾ→×-rinv p | com {mk In M P} {mk In M₁ P₁} .p = funExt λ { `L → funExt λ m → {!oxᴾ→×-rinv {P m} {Πᴾ _ P₁} ?!} ; `R → {!!} }
  oxᴾ→×-rinv p | com {mk In M P} {mk Out M₁ P₁} .p = {!!}
  oxᴾ→×-rinv p | com {mk Out M P} {mk In M₁ P₁} .p = {!!}
  oxᴾ→×-rinv p | com {mk Out M P} {mk Out M₁ P₁} .p = {!!}
  oxᴾ→×-rinv p | endL .p = refl
  oxᴾ→×-rinv p | endR {P} .p = refl

  ×→oxᴾ-equiv : ∀ P Q → Equiv (×→oxᴾ P Q)
  ×→oxᴾ-equiv P Q = record { linv = oxᴾ→× P Q
                           ; is-linv = λ { (x , y) → cong₂ _,_ (oxᴾ-comma-fst P Q x y) (oxᴾ-comma-snd P Q x y) }
                           ; rinv = oxᴾ→× P Q
                           ; is-rinv = oxᴾ→×-rinv {P} {Q} }
  -}

  -- left-biased strategy
  par : ∀ P Q → ⟦ P ⟧ → ⟦ Q ⟧ → ⟦ P ⅋ᴾ Q ⟧
  par P Q p q = par-view (view-proc P p)
    where par-view : ∀ {P} {p : ⟦ P ⟧} → ViewProc P p → ⟦ P ⅋ᴾ Q ⟧
          par-view (send M P m p) = ⅋ᴾ-sendL Q m (par (P m) Q p q)
          par-view (recv M P p)   = ⅋ᴾ-recvL Q λ m → par (P m) Q (p m) q
          par-view end            = q

  ⅋ᴾ-apply : ∀ {P Q} → ⟦ P ⅋ᴾ Q ⟧ → ⟦ dual P ⟧ → ⟦ Q ⟧
  ⅋ᴾ-apply {P} {Q} pq p with view-⅋ P Q pq
  ⅋ᴾ-apply ._ p       | sendL' P Q m pq = ⅋ᴾ-apply {P m} pq (p m)
  ⅋ᴾ-apply ._ p       | sendR' P Q m pq = m , ⅋ᴾ-apply {com P} {Q m} pq p
  ⅋ᴾ-apply ._ (m , p) | recvL' P Q pq   = ⅋ᴾ-apply {P m} (pq m) p
  ⅋ᴾ-apply ._ p       | recvR' P Q pq   = λ m → ⅋ᴾ-apply {com P} {Q m} (pq m) p
  ⅋ᴾ-apply pq p       | endL Q .pq        = pq
  ⅋ᴾ-apply pq p       | endR P .pq        = _

  ⅋ᴾ-apply' : ∀ {P Q} → ⟦ dual P ⅋ᴾ Q ⟧ → ⟦ P ⟧ → ⟦ Q ⟧
  ⅋ᴾ-apply' {P} {Q} pq p = ⅋ᴾ-apply {dual P} {Q} pq (subst ⟦_⟧ (≡.sym (≡ᴾ-sound funExt (dual-involutive P))) p)

  ⅋ᴾ-∘ : ∀ P Q R → ⟦ P ⅋ᴾ Q ⟧ → ⟦ dual Q ⅋ᴾ R ⟧ → ⟦ P ⅋ᴾ R ⟧
  ⅋ᴾ-∘ P Q R pq qr = ⅋ᴾ-∘-view (view-∘ P Q R pq qr)
   where
    ⅋ᴾ-∘-view : ∀ {P Q R}{pq : ⟦ P ⅋ᴾ Q ⟧}{qr : ⟦ dual Q ⅋ᴾ R ⟧} → View-∘ P Q R pq qr → ⟦ P ⅋ᴾ R ⟧
    ⅋ᴾ-∘-view (sendLL P Q R m p qr)     = ⅋ᴾ-sendL R m (⅋ᴾ-∘ (P m) (com Q) R p qr)
    ⅋ᴾ-∘-view (recvLL P Q R p qr)       = ⅋ᴾ-recvL R (λ m → ⅋ᴾ-∘ (P m) (com Q) R (p m) qr)
    ⅋ᴾ-∘-view (sendRR P Q R m pq q)     = ⅋ᴾ-sendR (com P) m (⅋ᴾ-∘ (com P) (com Q) (R m) pq q)
    ⅋ᴾ-∘-view (recvRR P Q R pq q)       = ⅋ᴾ-recvR (com P) (λ m₁ → ⅋ᴾ-∘ (com P) (com Q) (R m₁) pq (q m₁))
    ⅋ᴾ-∘-view (sendR-recvL P Q R m p q) = ⅋ᴾ-∘ (com P) (Q m) (com R) p (q m)
    ⅋ᴾ-∘-view (recvR-sendL P Q R p m q) = ⅋ᴾ-∘ (com P) (Q m) (com R) (p m) q
    ⅋ᴾ-∘-view (endL Q R pq qr)          = ⅋ᴾ-apply' {Q} {R} qr pq
    ⅋ᴾ-∘-view (endM P R pq qr)          = par (com P) R pq qr
    ⅋ᴾ-∘-view (endR P Q pq qr)          = ⅋ᴾ-apply {com Q} {com P} (fst (⅋ᴾ-comm (com P) (com Q)) pq) qr

  oxᴾ-map : ∀ P Q R S → (⟦ P ⟧ → ⟦ Q ⟧) → (⟦ R ⟧ → ⟦ S ⟧) → ⟦ P oxᴾ R ⟧ → ⟦ Q oxᴾ S ⟧
  oxᴾ-map P Q R S f g p = commaᴾ Q S (f (oxᴾ-fst P R p)) (g (oxᴾ-snd P R p))

  {-
  switchL : ∀ P Q R → ⟦ (P ⅋ᴾ Q) oxᴾ R ⟧ → ⟦ P ⅋ᴾ (Q oxᴾ R) ⟧
  switchL P Q R pqr = switchL' P Q R (oxᴾ-fst (P ⅋ᴾ Q) R pqr) (oxᴾ-snd (P ⅋ᴾ Q) R pqr)
  -}

  {-
  switchL' : ∀ P Q R (pq : ⟦ P ⅋ᴾ Q ⟧) (r : ⟦ R ⟧) → ⟦ P ⅋ᴾ (Q oxᴾ R) ⟧
  switchL' P Q R pq r = {!switchL-view {!!}!}
   where
    switchL-view : ∀ {P Q R}{pq : ⟦ P ⅋ᴾ Q ⟧}{r : ⟦ R ⟧} → ⟦ P ⅋ᴾ (Q oxᴾ R) ⟧
    switchL-view {P} {Q} {R} {p⅋q} {r} with view-⅋ P Q p⅋q | view-proc R r
    switchL-view | sendL' P₁ Q₁ m p | vr = {!!}
    switchL-view | sendR' P₁ Q₁ m p | send M₁ P₂ m₁ p₁ = {!!}
    switchL-view | sendR' P₁ Q₁ m p | recv M₁ P₂ r₁ = {!!}
    switchL-view | sendR' P₁ Q₁ m p | end = {!!}
    switchL-view | recvL' P₁ Q₁ p | send M₁ P₂ m p₁ = {!!}
    switchL-view | recvL' P₁ Q₁ p | recv M₁ P₂ r₁ = {!!}
    switchL-view | recvL' P₁ Q₁ p | end = {!!}
    switchL-view | recvR' P₁ Q₁ p | send M₁ P₂ m p₁ = {!!}
    switchL-view | recvR' P₁ Q₁ p | recv M₁ P₂ r₁ = {!!}
    switchL-view | recvR' P₁ Q₁ p | end = {!!}
    switchL-view | endL Q₁ pq₁ | send M P₁ m p = {!!}
    switchL-view | endL Q₁ pq₁ | recv M P₁ r₁ = {!!}
    switchL-view | endL Q₁ pq₁ | end = {!!}
    switchL-view | endR P₁ pq₁ | send M P₂ m p = {!!}
    switchL-view | endR P₁ pq₁ | recv M P₂ r₁ = {!!}
    switchL-view | endR P₁ pq₁ | end = {!!}
    {-
    switchL-view {R = R}{r = r} | sendL' P Q m p = ⅋ᴾ-sendL {!!} m (switchL' {!!} {!!} {!!} p r)
    switchL-view {R = R}{r = r} | sendR' P Q m p with view-proc R r
    switchL-view | sendR' {M₁} P₁ Q m₁ p₁ | send M P m p = {!!}
    switchL-view | sendR' {M₁} P₁ Q m p | recv M P r = {!!}
    switchL-view | sendR' {M} P Q m p | end = {!!}
    -- {!⅋ᴾ-map (com P) (com P) (Q m oxᴾ R) (Σᴾ M Q oxᴾ R) id (oxᴾ-map (Q m) (Σᴾ M Q) R R (_,_ m) id) (switchL-view (com P) (Q m) R p r)!}
    switchL-view {R = R}{r = r} | recvL' P Q p = ⅋ᴾ-recvL (com Q oxᴾ R) λ m → switchL' (P m) (com Q) R (p m) r
    switchL-view {R = R}{r = r} | recvR' (Πᶜ M' P) Q p = {!!} -- ⅋ᴾ-map (com P) (com P) {!!} (Πᴾ M Q oxᴾ R) id {!!} {!!}
    switchL-view {R = R}{r = r} | recvR' (Σᶜ M' P) Q p = {!!} -- ⅋ᴾ-map (com P) (com P) {!!} (Πᴾ M Q oxᴾ R) id {!!} {!!}
    switchL-view {R = R}{r = r} | endL Q p⅋q = commaᴾ Q R p⅋q r
    switchL-view {R = R}{r = r} | endR P p⅋q = par (com P) R p⅋q r
  -}
  -}

  ⊕ᴾ-map : ∀ {P Q R S} → (⟦ P ⟧ → ⟦ Q ⟧) → (⟦ R ⟧ → ⟦ S ⟧) → ⟦ P ⊕ᴾ R ⟧ → ⟦ Q ⊕ᴾ S ⟧
  ⊕ᴾ-map f g (`L , pr) = `L , f pr
  ⊕ᴾ-map f g (`R , pr) = `R , g pr

  &ᴾ-map : ∀ {P Q R S} → (⟦ P ⟧ → ⟦ Q ⟧) → (⟦ R ⟧ → ⟦ S ⟧) → ⟦ P &ᴾ R ⟧ → ⟦ Q &ᴾ S ⟧
  &ᴾ-map f g p `L = {!!}
  &ᴾ-map f g p `R = {!!}
  -}

  {-

    {-
_⟹_ : Proto → Proto → ★₁
P ⟹ Q = Sim (dual P) Q

_⟹ᴾ_ : Proto → Proto → ★₁
P ⟹ᴾ Q = Process (dual P) → Process Q

{-
sim& : ∀ {PA PB PAB}  → [ PA & PB ≡ PAB ] → Sim end PA → Sim end PB → Sim end PAB
sim&R : ∀ {PA PB PAB} → [ PA & PB ≡ PAB ]ᶜ → SimR end PA → SimR end PB → SimR end PAB

sim& end PA PB = PB
sim& (com P&) (comR s₀) (comR s₁) = comR (sim&R P& s₀ s₁)
sim& (&-comm P&) PA PB = sim& P& PB PA

sim&R (Π&  In  P&)  (recv s₀) (recv s₁)   = recv λ m → sim& (P& m) (s₀ m) (s₁ m)
sim&R (Π&  Out P&)  (recv s₀) (send m s₁) = send m (sim& (P& m) (s₀ m) s₁)
sim&R (Π☐& In  P&)  (recv s₀) (recv s₁)   = recv λ m → sim& (P& m) (s₀ [ m ]) (s₁ m)
sim&R (Π☐& Out P&)  (recv s₀) (send m s₁) = send m (sim& (P& m) (s₀ [ m ]) s₁)
-}
{-
sim&-assoc : ∀ {PA PB PC PAB PBC PABC}
               (PAB& : [ PA & PB ≡ PAB ])
               (PAB&PC : [ PAB & PC ≡ PABC ])
               (PBC& : [ PB & PC ≡ PBC ])
               (PA&PBC : [ PA & PBC ≡ PABC ])
               (sA : Sim end PA)(sB : Sim end PB)(sC : Sim end PC)
             → sim& PA&PBC sA (sim& PBC& sB sC) ≡ sim& PAB&PC (sim& PAB& sA sB) sC
sim&-assoc PAB& PAB&PC PBC& PA&PBC sA sB sC = {!!}
-}

sim-id : ∀ P → Sim (dual P) P
sim-id end = end
sim-id (Πᴾ M P) = comR (recv λ m → comL  (send m (sim-id (P m))))
sim-id (Σᴾ M P) = comL  (recv λ m → comR (send m (sim-id (P m))))

idˢ : ∀ {P P'} → Dual P P' → Sim P P'
idˢ end = end
idˢ (Π·Σ x) = comL (recv (λ m → comR (send m (idˢ (x m)))))
idˢ (Σ·Π x) = comR (recv (λ m → comL (send m (idˢ (x m)))))

sim-comp : ∀ {P Q Q' R} → Dual Q Q' → Sim P Q → Sim Q' R → Sim P R
sim-compRL : ∀ {P Q Q' R} → Dual (com Q) (com Q') → SimR P Q → SimL Q' R → Sim P R
--sim-compRL : ∀ {P Q R} → SimR P Q → SimL (dualᶜ Q) R → Sim P R
sim-compL : ∀ {P Q Q' R} → Dual Q Q' → SimL P Q → Sim Q' R → SimL P R
sim-compR : ∀ {P Q Q' R} → Dual Q Q' → Sim P Q → SimR Q' R → SimR P R

sim-comp Q-Q' (comL  PQ) QR         = comL (sim-compL Q-Q' PQ QR)
sim-comp Q-Q' (comR PQ) (comL QR)  = sim-compRL Q-Q' PQ QR
sim-comp Q-Q' (comR PQ) (comR QR) = comR (sim-compR Q-Q' (comR PQ) QR)
sim-comp ()   (comR PQ) end
sim-comp end end QR                 = QR

sim-compRL (Π·Σ Q-Q') (recv PQ)   (send m QR) = sim-comp (Q-Q' m) (PQ m) QR
sim-compRL (Σ·Π Q-Q') (send m PQ) (recv QR)   = sim-comp (Q-Q' m) PQ     (QR m)
{-
sim-compRL (Π☐·Σ Q-Q') (recv PQ)   (send m QR) = sim-comp (Q-Q' m) (PQ [ m ]) QR
sim-compRL (Σ·Π☐ Q-Q') (send m PQ) (recv QR)   = sim-comp (Q-Q' m) PQ     (QR [ m ])
-}

sim-compL Q-Q' (recv PQ)   QR = recv λ m → sim-comp Q-Q' (PQ m) QR
sim-compL Q-Q' (send m PQ) QR = send m (sim-comp Q-Q' PQ QR)

sim-compR Q-Q' PQ (recv QR)   = recv λ m → sim-comp Q-Q' PQ (QR m)
sim-compR Q-Q' PQ (send m QR) = send m (sim-comp Q-Q' PQ QR)

_♦_ : ∀ {P Q R} → Sim P Q → Sim (dual Q) R → Sim P R
_♦_ = sim-comp (Dual-spec _)

⟹-comp : ∀ {P Q R} → P ⟹ Q → Q ⟹ R → P ⟹ R
⟹-comp = _♦_

!ˢ : ∀ {P Q} → Sim P Q → Sim Q P
sim-symL : ∀ {P Q} → SimL P Q → SimR Q P
sim-symR : ∀ {P Q} → SimR P Q → SimL Q P

!ˢ (comL x) = comR (sim-symL x)
!ˢ (comR x) = comL (sim-symR x)
!ˢ end = end

sim-symL (recv PQ)   = recv (λ m → !ˢ (PQ m))
sim-symL (send m PQ) = send m (!ˢ PQ)

sim-symR (recv PQ)   = recv (λ m → !ˢ (PQ m))
sim-symR (send m PQ) = send m (!ˢ PQ)

!ˢ-cong : ∀ {P Q} {s₀ s₁ : Sim P Q} → s₀ ≈ˢ s₁ → !ˢ s₀ ≈ˢ !ˢ s₁
!ˢ-cong ≈-end = ≈-end
!ˢ-cong (≈-sendL m p) = ≈-sendR m (!ˢ-cong p)
!ˢ-cong (≈-sendR m p) = ≈-sendL m (!ˢ-cong p)
!ˢ-cong (≈-recvL x) = ≈-recvR (λ m → !ˢ-cong (x m))
!ˢ-cong (≈-recvR x) = ≈-recvL (λ m → !ˢ-cong (x m))

sim-unit : ∀ {P} → Sim end P → Process P
sim-unit (comR (recv P))   = com (recv (λ m → sim-unit (P m)))
sim-unit (comR (send m P)) = com (send m (sim-unit P))
sim-unit end                = end

mutual
    Simᴾ→SimR : ∀ {P Q} → ProcessF (Sim end) (Q >>ᶜ Simᴾ (com P)) → SimR (com P) Q
    Simᴾ→SimR (recv s)   = recv λ m → Simᴾ→Sim (s m)
    Simᴾ→SimR (send m s) = send m (Simᴾ→Sim s)

    Simᴾ→SimL : ∀ {P Q} → ProcessF (Sim end) (P >>ᶜ flip Simᴾ (com Q)) → SimL P (com Q)
    Simᴾ→SimL (recv s)   = recv λ m → Simᴾ→Sim (s m)
    Simᴾ→SimL (send m s) = send m (Simᴾ→Sim s)

    Simᴾ→Sim : ∀ {P Q} → Sim end (Simᴾ P Q) → Sim P Q
    Simᴾ→Sim {end}           s = s
    Simᴾ→Sim {com _} {end}   s = !ˢ s
    Simᴾ→Sim {com _} {com _} (comR (send `L (comR s))) = comL (Simᴾ→SimL s)
    Simᴾ→Sim {com _} {com _} (comR (send `R (comR s))) = comR (Simᴾ→SimR s)

mutual
    Sim→SimᴾR : ∀ {P Q} → SimR (com P) Q → ProcessF (Sim end) (Q >>ᶜ Simᴾ (com P))
    Sim→SimᴾR (recv s)   = recv λ m → Sim→Simᴾ (s m)
    Sim→SimᴾR (send m s) = send m (Sim→Simᴾ s)

    Sim→SimᴾL : ∀ {P Q} → SimL P (com Q) → ProcessF (Sim end) (P >>ᶜ flip Simᴾ (com Q))
    Sim→SimᴾL (recv s)   = recv λ m → Sim→Simᴾ (s m)
    Sim→SimᴾL (send m s) = send m (Sim→Simᴾ s)

    Sim→Simᴾ : ∀ {P Q} → Sim P Q → Sim end (Simᴾ P Q)
    Sim→Simᴾ {end}           s = s
    Sim→Simᴾ {com _} {end}   s = !ˢ s
    Sim→Simᴾ {com _} {com _} (comL s) = comR (send `L (comR (Sim→SimᴾL s)))
    Sim→Simᴾ {com _} {com _} (comR s) = comR (send `R (comR (Sim→SimᴾR s)))

    {-
mutual
    Simᴾ-assocR : ∀ {P Q R} → Sim P (SimᶜR Q R) → Sim (Simᴾ P (com Q)) (com R)
    Simᴾ-assocR {end}{Q}{R} s = {!!}
    Simᴾ-assocR {Πᴾ M P}{Q}{R}(comL (recv s)) = comL (send `L (comL (recv (λ m → Simᴾ-assocR (s m)))))
    Simᴾ-assocR {Σᴾ M P}{Q}{R}(comL (send m s)) = comL (send `L (comL (send m (Simᴾ-assocR s))))
    Simᴾ-assocR {com (mk io M P)} {Q} {mk .In M₂ R} (comR (recv s)) = comR (recv (λ m → Simᴾ-assoc {Q = com Q} {R m} (s m)))
    Simᴾ-assocR {com (mk io M P)} {mk io₁ M₁ Q} {mk .Out M₂ R} (comR (send m s)) = comR (send m (Simᴾ-assoc {com (mk io M P)} {com (mk io₁ M₁ Q)} {R m} s))

    Simᴾ-assocL : ∀ {P Q R} → Sim P (SimᶜL Q R) → Sim (Simᴾ P (com Q)) (com R)
    Simᴾ-assocL s = {!!}

    Simᴾ-assoc : ∀ {P Q R} → Sim P (Simᴾ Q R) → Sim (Simᴾ P Q) R
    Simᴾ-assoc {end}                   s = Simᴾ→Sim s
    Simᴾ-assoc {com _} {end}           s = s
    Simᴾ-assoc {com _} {com _} {end}   s = !ˢ {!s!}
    Simᴾ-assoc {com ._} {com Q} {com R} (comL (recv s))   = comL (send `L (comL (recv (λ m → Simᴾ-assoc (s m)))))
    Simᴾ-assoc {com ._} {com Q} {com R} (comL (send m s)) = comL (send `L (comL (send m (Simᴾ-assoc s))))
    Simᴾ-assoc {Πᴾ M P} {com Q} {com R} (comR (send `L (comL (recv s))))   = comL (send `L (comL (recv (λ m → Simᴾ-assocL (s m)))))
    Simᴾ-assoc {com ._} {com Q} {com R} (comR (send `L (comL (send m s)))) = comL (send `L (comL (send m (Simᴾ-assocL s))))
    Simᴾ-assoc {com P} {Πᴾ M Q} {com R} (comR (send `L (comR (recv s))))
      = comL (send `R (comL (recv (λ m → Simᴾ-assoc {Q = Q m} (s m)))))
    Simᴾ-assoc {com P} {Σᴾ M Q} {com R} (comR (send `L (comR (send m s))))
      = comL (send `R (comL (send m (Simᴾ-assoc {Q = Q m} s))))
    Simᴾ-assoc {Πᴾ M P} {com Q} {com R} (comR (send `R (comL (recv s)))) = comL (send `L (comL (recv (λ m → Simᴾ-assocR (s m)))))
    Simᴾ-assoc {Σᴾ M P} {com Q} {com R} (comR (send `R (comL (send m s)))) = comL (send `L (comL (send m (Simᴾ-assocR s))))
    Simᴾ-assoc {com P} {com Q} {Πᴾ M R} (comR (send `R (comR (recv s))))
      = comR (recv (λ m → Simᴾ-assoc {com P} {com Q} {R m} (s m)))
    Simᴾ-assoc {com P} {com Q} {Σᴾ M R} (comR (send `R (comR (send m s))))
      = comR (send m (Simᴾ-assoc {com P} {com Q} {R m} s))
-}
{-
Simᴾ-assoc : ∀ {P Q R} → ⟦ Simᴾ P (Simᴾ Q R) ⟧ → ⟦ Simᴾ (Simᴾ P Q) R ⟧
Simᴾ-assoc {end}                   s = s
Simᴾ-assoc {com _} {end}           s = s
Simᴾ-assoc {com _} {com _} {end}   s = s
Simᴾ-assoc {com P} {com Q} {com R} (`L , s) = `L , `L , Simᴾ-assoc {com ?} {com Q} {com R} s
Simᴾ-assoc {com P} {com Q} {com R} (`R , `L , s) = `L , `R , Simᴾ-assoc {com P} {{!com ?!}} {com R} s
Simᴾ-assoc {com P} {com Q} {com R} (`R , `R , s) = {!!}
-}

{-
module 3-way-trace where
  trace : ∀ {P P' Q Q'} → Dual P P' → Dual Q Q' →  Sim end P' → Sim P Q → Sim Q' end
        → Tele P × Tele Q
  trace (Π·Σ x₁) Q-Q' (comR (send x x₂)) (comL (recv x₃)) Q· = first (_,_ x) (trace (x₁ x) Q-Q' x₂ (x₃ x) Q·)
  trace (Σ·Π x₁) Q-Q' (comR (recv x)) (comL (send x₂ x₃)) Q· = first (_,_ x₂) (trace (x₁ x₂) Q-Q' (x x₂) x₃ Q·)
  {-
  trace (Π☐·Σ x₁) Q-Q' (comR (send x x₂)) (comL (recv x₃)) Q· = {!first (_,_ x) (trace (x₁ x) Q-Q' x₂ (x₃ x) Q·)!}
  trace (Σ·Π☐ x₁) Q-Q' (comR (recv x)) (comL (send x₂ x₃)) Q· = {!first (_,_ x₂) (trace (x₁ x₂) Q-Q' (x x₂) x₃ Q·)!}
  -}
  trace P-P' (Π·Σ x₁) ·P (comR (recv x)) (comL (send x₂ x₃)) = second (_,_ x₂) (trace P-P' (x₁ x₂) ·P (x x₂) x₃)
  trace P-P' (Σ·Π x₁) ·P (comR (send x x₂)) (comL (recv x₃)) = second (_,_ x) (trace P-P' (x₁ x) ·P x₂ (x₃ x))
  {-
  trace P-P' (Π☐·Σ x₁) ·P (comR (recv x)) (comL (send x₂ x₃)) = {!second (_,_ x₂) (trace P-P' (x₁ x₂) ·P (x x₂) x₃)!}
  trace P-P' (Σ·Π☐ x₁) ·P (comR (send x x₂)) (comL (recv x₃)) = {!second (_,_ x) (trace P-P' (x₁ x) ·P x₂ (x₃ x))!}
  -}
  trace P-P' Q-Q' ·P end Q· = _

  module _ {P Q : Proto} where
    _≈_ : (PQ PQ' : Sim P Q) → ★₁
    PQ ≈ PQ' = ∀ {P' Q'}(P-P' : Dual P P')(Q-Q' : Dual Q Q') → (·P : Sim end P')(Q· : Sim Q' end)
       → trace P-P' Q-Q' ·P PQ Q· ≡ trace P-P' Q-Q' ·P PQ' Q·

module _ where
  trace : ∀ {B E} → Sim (Trace B) (Trace E) → Tele B × Tele E
  trace {end}   {end}   end = _
  trace {com _} {end}   (comL  (send m s)) = first  (_,_ m) (trace s)
  trace {end}   {com _} (comR (send m s)) = second (_,_ m) (trace s)
  trace {com _} {com c} (comL  (send m s)) = first  (_,_ m) (trace {E = com c} s)
  trace {com c} {com _} (comR (send m s)) = second (_,_ m) (trace {com c} s)

  module _ {P Q} where
    _≈_ : (PQ PQ' : Sim P Q) → ★₁
    PQ ≈ PQ' = ∀ {B P' Q' E} → (P'-P : Dual P' P)(Q-Q' : Dual Q Q')(BP : Sim (Trace B) P')(QE : Sim Q' (Trace E))
       → trace (sim-comp P'-P BP (sim-comp Q-Q' PQ QE)) ≡ trace (sim-comp P'-P BP (sim-comp Q-Q' PQ' QE))

module _
  (funExt : ∀ {a}{b}{A : ★_ a}{B : A → ★_ b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g)
  where

  Dual-sym-sym : ∀ {P Q} (P-Q : Dual P Q) → P-Q ≡ Dual-sym (Dual-sym P-Q)
  Dual-sym-sym end = refl
  Dual-sym-sym (Π·Σ x) = cong Π·Σ (funExt (λ y → Dual-sym-sym (x y)))
  Dual-sym-sym (Σ·Π x) = cong Σ·Π (funExt (λ y → Dual-sym-sym (x y)))
  {-
  Dual-sym-sym (Π☐·Σ x) = cong Π☐·Σ (funExt (λ y → Dual-sym-sym (x y)))
  Dual-sym-sym (Σ·Π☐ x) = cong Σ·Π☐ (funExt (λ y → Dual-sym-sym (x y)))
  -}

module _
  (funExt : ∀ {a}{b}{A : ★_ a}{B : A → ★_ b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g)
  where

  open ≡-Reasoning
  sim-comp-assoc : ∀ {W P P' Q Q' R}(P-P' : Dual P P')(Q-Q' : Dual Q Q')
    (WP : Sim W P)(PQ : Sim P' Q)(QR : Sim Q' R)
    → sim-comp Q-Q' (sim-comp P-P' WP PQ) QR
    ≡ sim-comp P-P' WP (sim-comp Q-Q' PQ QR)
  sim-comp-assoc P-P' Q-Q' (comL (recv x)) PQ QR = cong (comL ∘ recv) (funExt (λ m → sim-comp-assoc P-P' Q-Q' (x m) PQ QR))
  sim-comp-assoc P-P' Q-Q' (comL (send m x)) PQ QR = cong (comL ∘ send m) (sim-comp-assoc P-P' Q-Q' x PQ QR)
  sim-comp-assoc (Π·Σ x₁) Q-Q' (comR (recv x)) (comL (send m x₂)) QR = sim-comp-assoc (x₁ m) Q-Q' (x m) x₂ QR
  sim-comp-assoc (Σ·Π x₁) Q-Q' (comR (send m x)) (comL (recv x₂)) QR = sim-comp-assoc (x₁ m) Q-Q' x (x₂ m) QR
  sim-comp-assoc P-P' (Π·Σ x₂) (comR x) (comR (recv x₁)) (comL (send m x₃)) = sim-comp-assoc P-P' (x₂ m) (comR x) (x₁ m) x₃
  sim-comp-assoc P-P' (Σ·Π x₂) (comR x) (comR (send m x₁)) (comL (recv x₃)) = sim-comp-assoc P-P' (x₂ m) (comR x) x₁ (x₃ m)
  sim-comp-assoc P-P' Q-Q' (comR x) (comR x₁) (comR (recv x₂)) = cong (comR ∘ recv) (funExt λ m → sim-comp-assoc P-P' Q-Q' (comR x) (comR x₁) (x₂ m))
  sim-comp-assoc P-P' Q-Q' (comR x) (comR x₁) (comR (send m x₂)) = cong (comR ∘ send m) (sim-comp-assoc P-P' Q-Q' (comR x) (comR x₁) x₂)
  sim-comp-assoc end Q-Q' end PQ QR = refl

  ♦-assoc : ∀ {W P Q R}(WP : Sim W P)(PQ : Sim (dual P) Q)(QR : Sim (dual Q) R)
    → (WP ♦ PQ) ♦ QR ≡ WP ♦ (PQ ♦ QR)
  ♦-assoc = sim-comp-assoc (Dual-spec _) (Dual-spec _)

  {-
  sim-id-comp : ∀ {P P' Q}(P-P' : Dual P P')(s : Sim P' Q) → sim-comp P-P' (idˢ (Dual-sym P-P')) s ≡ s
  sim-id-comp end s = refl
  sim-id-comp (Π·Σ x) s = {!!}
  sim-id-comp (Σ·Π x) s = {!!}

  module _ (A : ★) where
    Test : Proto
    Test = A ×' end

    s : A → Sim Test Test
    s m = comR (send m (comL (send m end)))

    s' : Sim (dual Test) (dual Test)
    s' = comR (recv (λ m → comL (recv (λ m₁ → end))))

    prf : ∀ x → s x ♦ sim-id _ ≡ s x
    prf x = {!!}

    c-prf : ∀ x → sim-id _ ♦ s x ≡ s x
    c-prf x = {!!}

    c-prf' : sim-id _ ♦ s' ≡ s'
    c-prf' = {!!}

    prf' : s' ♦ sim-id _ ≡ s'
    prf' = {!!}

  sim-comp-id : ∀ {P Q}(s : Sim P Q) → s ♦ (sim-id Q) ≡ s
  sim-comp-id (comL (recv x)) = cong (comL ∘ recv) (funExt λ m → sim-comp-id (x m))
  sim-comp-id (comL (send m x)) = cong (comL ∘ send m) (sim-comp-id x)
  sim-comp-id (comR (recv x)) = cong (comR ∘ recv) (funExt λ m → sim-comp-id (x m))
  sim-comp-id (comR (send m x)) = {!cong (comR ∘ send m) (sim-comp-id x)!}
  sim-comp-id end = refl
  -}

module _
  (funExt : ∀ {a}{b}{A : ★_ a}{B : A → ★_ b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g)
  where

  sim-!! : ∀ {P Q}(PQ : Sim P Q) → PQ ≡ !ˢ (!ˢ PQ)
  sim-!! (comL (recv x))    = cong (comL ∘ recv) (funExt λ m → sim-!! (x m))
  sim-!! (comL (send x x₁)) = cong (comL ∘ send x) (sim-!! x₁)
  sim-!! (comR (recv x))    = cong (comR ∘ recv) (funExt λ m → sim-!! (x m))
  sim-!! (comR (send x x₁)) = cong (comR ∘ send x) (sim-!! x₁)
  sim-!! end = refl

  sim-comp-! : ∀ {P Q Q' R}(Q-Q' : Dual Q Q')(PQ : Sim P Q)(Q'R : Sim Q' R)
    → sim-comp (Dual-sym Q-Q') (!ˢ Q'R) (!ˢ PQ) ≈ˢ !ˢ (sim-comp Q-Q' PQ Q'R)
  sim-comp-! Q-Q'       (comL (recv s))   (comR (recv s₁))    = TODO where postulate TODO : _
  sim-comp-! Q-Q'       (comL (recv s))   (comR (send m s₁))  = TODO where postulate TODO : _
  sim-comp-! Q-Q'       (comL (send m s)) (comR (recv s₁))    = TODO where postulate TODO : _
  sim-comp-! Q-Q'       (comL (send m s)) (comR (send m₁ s₁)) = ≈ˢ-trans (≈ˢ-trans (≈-sendL m₁ (≈ˢ-trans (sim-comp-! Q-Q' (sendL m s) s₁) (≈-sendR m (≈ˢ-sym (sim-comp-! Q-Q' s s₁))))) (≈-sendLR m₁ m)) (≈-sendR m (sim-comp-! Q-Q' s (comR (send m₁ s₁))))
  sim-comp-! Q-Q'       (comL (recv s))   (comL (recv s₁))    = ≈-recvR λ m → sim-comp-! Q-Q' (s m) (comL (recv s₁))
  sim-comp-! Q-Q'       (comL (send m s)) (comL (recv s₁))    = ≈-sendR m (sim-comp-! Q-Q' s (comL (recv s₁)))
  sim-comp-! Q-Q'       (comL (send m s)) (comL (send m₁ s₁)) = ≈-sendR m (sim-comp-! Q-Q' s (comL (send m₁ s₁)))
  sim-comp-! (Π·Σ Q-Q') (comR (recv s))   (comL (send m s₁))  = sim-comp-! (Q-Q' m) (s m) s₁
  sim-comp-! (Π·Σ Q-Q') (comL (recv s))   (comL (send m s₁))  = ≈-recvR λ m₁ → sim-comp-! (Π·Σ Q-Q') (s m₁) (comL (send m s₁))
  sim-comp-! (Π·Σ Q-Q') (comR (recv s))   (comR (recv s₁))    = ≈-recvL λ m → sim-comp-! (Π·Σ Q-Q') (comR (recv s)) (s₁ m)
  sim-comp-! (Π·Σ Q-Q') (comR (recv s))   (comR (send m s₁))  = ≈-sendL m (sim-comp-! (Π·Σ Q-Q') (comR (recv s)) s₁)
  sim-comp-! (Σ·Π Q-Q') (comR (send m s)) (comL (recv s₁))    = sim-comp-! (Q-Q' m) s (s₁ m)
  sim-comp-! (Σ·Π Q-Q') (comR (send m s)) (comR (recv s₁))    = ≈-recvL λ m₁ → sim-comp-! (Σ·Π Q-Q') (comR (send m s)) (s₁ m₁)
  sim-comp-! (Σ·Π Q-Q') (comR (send m s)) (comR (send m₁ s₁)) = ≈-sendL m₁ (sim-comp-! (Σ·Π Q-Q') (comR (send m s)) s₁)
  sim-comp-! end        (comL (recv s))   end                 = ≈-recvR λ m → sim-comp-! end (s m) end
  sim-comp-! end        (comL (send m s)) end                 = ≈-sendR m (sim-comp-! end s end)
  sim-comp-! end        end               (comR (recv s))     = ≈-recvL λ m → sim-comp-! end end (s m)
  sim-comp-! end        end               (comR (send m s))   = ≈-sendL m (sim-comp-! end end s)
  sim-comp-! end        end               end                 = ≈-end

    {-
  sim-comp-!-end : ∀ {Q Q' R}(Q-Q' : Dual Q Q')(·Q : Sim end Q)(Q'R : Sim Q' R)
    → sim-comp (Dual-sym Q-Q') (!ˢ Q'R) (!ˢ ·Q) ≡ !ˢ (sim-comp Q-Q' ·Q Q'R)
  sim-comp-!-end (Π·Σ x₁) (comR (recv x)) (comL (send x₂ x₃)) = sim-comp-!-end (x₁ x₂) (x x₂) x₃
  sim-comp-!-end (Σ·Π x) (comR (send x₁ x₂)) (comL (recv x₃)) = sim-comp-!-end (x x₁) x₂ (x₃ x₁)
  sim-comp-!-end Q-Q' (comR x) (comR (recv x₁))
    = cong (comL ∘ recv) (funExt (λ x₂ → sim-comp-!-end Q-Q' (comR x) (x₁ x₂)))
  sim-comp-!-end Q-Q' (comR x) (comR (send x₁ x₂))
    = cong (comL ∘ send x₁) (sim-comp-!-end Q-Q' (comR x) x₂)
  sim-comp-!-end end end (comR (recv x)) = cong (comL ∘ recv) (funExt λ m → sim-comp-!-end end end (x m))
  sim-comp-!-end end end (comR (send m x)) = cong (comL ∘ send m) (sim-comp-!-end end end x)
  sim-comp-!-end end end end = refl

  open ≡-Reasoning

  module _ {P Q : Proto} where
      infix 2 _∼_
      _∼_ : (PQ PQ' : Sim P Q) → ★₁
      PQ ∼ PQ' = ∀ {P'} → (P'-P : Dual P' P) → (øP : Sim end P')
               → sim-comp P'-P øP PQ ≡ sim-comp P'-P øP PQ'

  sim-comp-! : ∀ {P Q Q' R}(Q-Q' : Dual Q Q')(PQ : Sim P Q)(Q'R : Sim Q' R)
    → sim-comp (Dual-sym Q-Q') (!ˢ Q'R) (!ˢ PQ) ∼ !ˢ (sim-comp Q-Q' PQ Q'R)
  sim-comp-! Q-Q' PQ Q'R {R'} R'-R øR'
    = sim-comp R'-R øR' (sim-comp (Dual-sym Q-Q') (!ˢ Q'R) (!ˢ PQ))
    ≡⟨ sim-!! (sim-comp R'-R øR' (sim-comp (Dual-sym Q-Q') (!ˢ Q'R) (!ˢ PQ))) ⟩
      !ˢ( !ˢ ((sim-comp R'-R øR' (sim-comp (Dual-sym Q-Q') (!ˢ Q'R) (!ˢ PQ)))))
    ≡⟨ cong (!ˢ ∘ !ˢ) (sym (sim-comp-assoc funExt R'-R (Dual-sym Q-Q') øR' (!ˢ Q'R) (!ˢ PQ))) ⟩
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
    ≡⟨ cong !ˢ (sym (sim-comp-assoc funExt Q-Q' (Dual-sym R'-R) PQ Q'R (!ˢ øR'))) ⟩
      !ˢ (sim-comp (Dual-sym R'-R) (sim-comp Q-Q' PQ Q'R) (!ˢ øR'))
    ≡⟨ cong (λ X → !ˢ (sim-comp (Dual-sym R'-R) X (!ˢ øR'))) (sim-!! (sim-comp Q-Q' PQ Q'R)) ⟩
      !ˢ (sim-comp (Dual-sym R'-R) (!ˢ (!ˢ (sim-comp Q-Q' PQ Q'R)))
                                   (!ˢ øR'))
    ≡⟨ cong !ˢ (sim-comp-!-end R'-R øR' (!ˢ (sim-comp Q-Q' PQ Q'R))) ⟩
      !ˢ (!ˢ (sim-comp R'-R øR' (!ˢ (sim-comp Q-Q' PQ Q'R))))
    ≡⟨ sym (sim-!! (sim-comp R'-R øR' (!ˢ (sim-comp Q-Q' PQ Q'R)))) ⟩
      sim-comp R'-R øR' (!ˢ (sim-comp Q-Q' PQ Q'R))
    ∎
-}

  {-
  ♦-! : ∀ {P Q R}(PQ : Sim P Q)(QR : Sim (dual Q) R)
    → !ˢ (PQ ♦ QR) ∼ (!ˢ QR) ♦ (!ˢ {!PQ!})
  ♦-! = {!!}
  -}
  -}

module Commitment {Secret Guess : ★} {R : ..(_ : Secret) → Guess → ★} where
    Commit : Proto
    Commit = Σ☐ᴾ Secret  λ s →
             Πᴾ  Guess   λ g →
             Σᴾ  S< s >  λ _ →
             end

    commit : (s : Secret)  → ⟦ Commit ⟧
    commit s = [ s ] , λ g → S[ s ] , _

    decommit : (g : Guess) → ⟦ dual Commit ⟧
    decommit g = λ { [ m ] → g , _ }

open import Relation.Nullary
open import Relation.Nullary.Decidable

--    foo : (⟦ P ⟧ → ⟦ Q ⟧) → Sim (dual P) Q
--       foo can stop interacting with P as soon as Q is done

data End? : ★ where
  end continue : End?

End?ᴾ : Proto → Proto
End?ᴾ P = Σᴾ End? λ { end → end ; continue → P }

module _ {A : ★} (Aᴾ : A → Proto) where
    addΣᴾ : Proto → Proto
    addΣᴾ end      = end
    addΣᴾ (Σᴾ M P) = Σᴾ (M ⊎ A) [ (λ m → addΣᴾ (P m)) , Aᴾ ]′
    addΣᴾ (Πᴾ M P) = Πᴾ M λ m → addΣᴾ (P m)

    addΠᴾ : Proto → Proto
    addΠᴾ end      = end
    addΠᴾ (Σᴾ M P) = Σᴾ (M ⊎ A) [ (λ m → addΠᴾ (P m)) , Aᴾ ]′
    addΠᴾ (Πᴾ M P) = Πᴾ M λ m → addΠᴾ (P m)

data Abort : ★ where abort : Abort

Abortᴾ : Abort → Proto
Abortᴾ _ = end

add-abort : Proto → Proto
add-abort = addΣᴾ Abortᴾ

{-
test-sim : Sim (𝟘 ×' end) end
test-sim = end
-}

-- Prove knowledge of a discrete log
-- Adapted here to have precise types
module Shnorr-protocol
    (G ℤq : ★)
    (g    : G) 
    (_^_  : G  → ℤq → G)
    (_·_  : G  → G  → G)
    (_+_  : ℤq → ℤq → ℤq)
    (_*_  : ℤq → ℤq → ℤq)
    (_≟_  : (x y : G) → Dec (x ≡ y))
    where
    module Real where
        Prover : Proto
        Prover = Σᴾ  G  λ gʳ → -- commitment
                 Πᴾ  ℤq λ c  → -- challenge
                 Σᴾ  ℤq λ s  → -- response
                 end

        Verifier : Proto
        Verifier = dual Prover

        -- he is honest but its type does not say it
        prover : (x r : ℤq) → ⟦ Prover ⟧
        prover x r = (g ^ r) , λ c → (r + (c * x)) , _

        Honest-Prover : ..(x : ℤq) (y : S< g ^ x >) → Proto
        Honest-Prover x y
          = Σ☐ᴾ ℤq                λ r  → -- ideal commitment
            Σᴾ  S< g ^ r >        λ gʳ → -- real  commitment
            Πᴾ  ℤq                λ c  → -- challenge
            Σᴾ  S< r + (c * x) >  λ s  → -- response
            Πᴾ  (Dec ((g ^ unS s) ≡ (unS gʳ · (unS y ^ c)))) λ _ →
            end

        Honest-Prover' : ..(x : ℤq) (y : S< g ^ x >) → Proto
        Honest-Prover' x S[ y ∥ _ ]
          = Σ☐ᴾ ℤq                λ r  → -- ideal commitment
            Σᴾ  S< g ^ r >        λ { S[ gʳ ∥ _ ] → -- real  commitment
            Πᴾ  ℤq                λ c  → -- challenge
            Σᴾ  S< r + (c * x) >  λ { S[ s ∥ _ ]  → -- response
            Πᴾ  (Dec ((g ^ s) ≡ (gʳ · (y ^ c)))) λ _ →
            end } }

        Honest-Verifier : ..(x : ℤq) (y : S< g ^ x >) → Proto
        Honest-Verifier x y = dual (Honest-Prover x y)

        honest-prover : (x r : ℤq) → ⟦ Honest-Prover x S[ g ^ x ] ⟧
        honest-prover x r = [ r ] , S[ g ^ r ] , λ c → S[ r + (c * x) ] , _
        -- agsy can do it

        honest-verifier : ..(x : ℤq) (y : S< g ^ x >) (c : ℤq) → ⟦ Honest-Verifier x y ⟧
        honest-verifier x y c = λ { [ r ] → λ gʳ → c , λ s → (g ^ unS s) ≟ (unS gʳ · (unS y ^ c)) , _ }

        honest-prover→prover : ..(x : ℤq)(y : S< g ^ x >) → ⟦ Honest-Prover x y ⟧ → ⟦ Prover ⟧
        honest-prover→prover x y ([ r ] , gʳ , p) = unS gʳ , λ c → case p c of λ { (s , _) → unS s , _ }

        {-
        sim-honest-prover : ..(x : ℤq)(y : S< g ^ x >) → Sim (dual (Honest-Prover x y)) Prover
        sim-honest-prover x y = recvL (λ { [ r ] →
                                recvL λ gʳ →
                                sendR (unS gʳ) (
                                recvR λ c →
                                sendL c (recvL λ s → sendR (unS s) (sendL {!!} {!!}) )) })
                                -}

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
