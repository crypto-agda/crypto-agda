
-- {-# OPTIONS --without-K #-}
open import Coinduction
open import Function.NP
open import Type
open import Level.NP
open import Data.Product.NP renaming (map to ×-map; proj₁ to fst; proj₂ to snd)
open import Data.Zero
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr; [_,_] to [inl:_,inr:_]) hiding ([_,_]′)
open import Data.One using (𝟙)
open import Data.Two hiding (_≟_)
open import Data.Nat hiding (_⊔_)
open import Data.LR
open Data.Two.Indexed

open import Relation.Binary
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_; !_; _∙_; refl; subst; J; ap; coe; coe!; J-orig; _≢_)

open import Function.Extensionality
open import HoTT
open import Data.ShapePolymorphism
open Equivalences

module Control.Protocol.Choreography where

data InOut : ★ where
  In Out : InOut

dualᴵᴼ : InOut → InOut
dualᴵᴼ In  = Out
dualᴵᴼ Out = In

dualᴵᴼ-involutive : ∀ io → dualᴵᴼ (dualᴵᴼ io) ≡ io
dualᴵᴼ-involutive In = refl
dualᴵᴼ-involutive Out = refl

dualᴵᴼ-equiv : Is-equiv dualᴵᴼ
dualᴵᴼ-equiv = self-inv-is-equiv dualᴵᴼ-involutive

dualᴵᴼ-inj : ∀ {x y} → dualᴵᴼ x ≡ dualᴵᴼ y → x ≡ y
dualᴵᴼ-inj = Is-equiv.injective dualᴵᴼ-equiv

{-
module UniversalProtocols ℓ {U : ★_(ₛ ℓ)}(U⟦_⟧ : U → ★_ ℓ) where
-}
module _ ℓ where
  U = ★_ ℓ
  U⟦_⟧ = id
  data Proto_ : ★_(ₛ ℓ) where
    end : Proto_
    com : (io : InOut){M : U}(P : U⟦ M ⟧ → Proto_) → Proto_
{-
module U★ ℓ = UniversalProtocols ℓ {★_ ℓ} id
open U★
-}

Proto : ★₁
Proto = Proto_ ₀
Proto₀ = Proto
Proto₁ = Proto_ ₁

pattern recv P = com In  P
pattern send P = com Out P

module _ {{_ : FunExt}} where
    com= : ∀ io {M₀ M₁}(M= : M₀ ≡ M₁)
                {P₀ : M₀ → Proto}{P₁ : M₁ → Proto}(P= : ∀ m₀ → P₀ m₀ ≡ P₁ (coe M= m₀))
           → com io P₀ ≡ com io P₁
    com= io refl P= = ap (com io) (λ= P=)

    module _ io {M₀ M₁}(M≃ : M₀ ≃ M₁)
             {P₀ : M₀ → Proto}{P₁ : M₁ → Proto}
             (P= : ∀ m₀ → P₀ m₀ ≡ P₁ (–> M≃ m₀))
             {{_ : UA}} where
        com≃ : com io P₀ ≡ com io P₁
        com≃ = com= io (ua M≃) λ m → P= m ∙ ap P₁ (! coe-β M≃ m)

    module _ io {M N}(P : M × N → Proto)
             where
        com₂ : Proto
        com₂ = com io λ m → com io λ n → P (m , n)

    {- Proving this would be awesome...
    module _ io
             {M₀ M₁ N₀ N₁ : ★}
             (M×N≃ : (M₀ × N₀) ≃ (M₁ × N₁))
             {P₀ : M₀ × N₀ → Proto}{P₁ : M₁ × N₁ → Proto}
             (P= : ∀ m,n₀ → P₀ m,n₀ ≡ P₁ (–> M×N≃ m,n₀))
             {{_ : UA}} where
        com₂≃ : com₂ io P₀ ≡ com₂ io P₁
        com₂≃ = {!com=!}
    -}

    -- send= : ∀ {M₀ M₁}(M= : M₀ ≡ M₁){P₀ : M₀ → Proto}{P₁ : M₁ → Proto}(P= : ∀ m₀ → P₀ m₀ ≡ P₁ (coe M= m₀)) → send P₀ ≡ send P₁
    send= = com= Out
    send≃ = com≃ Out

    -- recv= : ∀ {M₀ M₁}(M= : M₀ ≡ M₁){P₀ : M₀ → Proto}{P₁ : M₁ → Proto}(P= : ∀ m₀ → P₀ m₀ ≡ P₁ (coe M= m₀)) → recv P₀ ≡ recv P₁
    recv= = com= In
    recv≃ = com≃ In

    com=′ : ∀ io {M}{P₀ P₁ : M → Proto}(P= : ∀ m → P₀ m ≡ P₁ m) → com io P₀ ≡ com io P₁
    com=′ io = com= io refl

    send=′ : ∀ {M}{P₀ P₁ : M → Proto}(P= : ∀ m → P₀ m ≡ P₁ m) → send P₀ ≡ send P₁
    send=′ = send= refl

    recv=′ : ∀ {M}{P₀ P₁ : M → Proto}(P= : ∀ m → P₀ m ≡ P₁ m) → recv P₀ ≡ recv P₁
    recv=′ = recv= refl

pattern recvE M P = com In  {M} P
pattern sendE M P = com Out {M} P

module ProtoRel (_≈ᴵᴼ_ : InOut → InOut → ★) where
    infix 0 _≈ᴾ_
    data _≈ᴾ_ : Proto → Proto → ★₁ where
      end : end ≈ᴾ end
      com : ∀ {io₀ io₁} (io : io₀ ≈ᴵᴼ io₁){M P Q} → (∀ (m : M) → P m ≈ᴾ Q m) → com io₀ P ≈ᴾ com io₁ Q

module ProtoRelImplicit {_≈ᴵᴼ_ : InOut → InOut → ★} = ProtoRel _≈ᴵᴼ_
open ProtoRelImplicit hiding (_≈ᴾ_)
open ProtoRel _≡_ public renaming (_≈ᴾ_ to _≡ᴾ_) using ()

data View-≡ᴾ : (P Q : Proto) → P ≡ᴾ Q → ★₁ where
  end : View-≡ᴾ end end end
  ≡-Σ : ∀ {M P Q} (p≡q : (m : M) → P m ≡ᴾ Q m) → View-≡ᴾ (send P) (send Q) (com refl p≡q)
  ≡-Π : ∀ {M P Q} (p≡q : (m : M) → P m ≡ᴾ Q m) → View-≡ᴾ (recv P) (recv Q) (com refl p≡q)

view-≡ᴾ : ∀ {P Q} (p≡q : P ≡ᴾ Q) → View-≡ᴾ P Q p≡q
view-≡ᴾ end = end
view-≡ᴾ (com {In}  refl _) = ≡-Π _
view-≡ᴾ (com {Out} refl _) = ≡-Σ _

recv☐ : {M : ★}(P : ..(_ : M) → Proto) → Proto
recv☐ P = recv (λ { [ m ] → P m })

send☐ : {M : ★}(P : ..(_ : M) → Proto) → Proto
send☐ P = send (λ { [ m ] → P m })

source-of : Proto → Proto
source-of end       = end
source-of (com _ P) = send λ m → source-of (P m)

{-
dual : Proto → Proto
dual end      = end
dual (send P) = recv λ m → dual (P m)
dual (recv P) = send λ m → dual (P m)
-}

dual : Proto → Proto
dual end        = end
dual (com io P) = com (dualᴵᴼ io) λ m → dual (P m)

data IsSource : Proto → ★₁ where
  end : IsSource end
  com : ∀ {M P} (PT : (m : M) → IsSource (P m)) → IsSource (send P)

data IsSink : Proto → ★₁ where
  end : IsSink end
  com : ∀ {M P} (PT : (m : M) → IsSink (P m)) → IsSink (recv P)

data Proto☐ : Proto → ★₁ where
  end : Proto☐ end
  com : ∀ q {M P} (P☐ : ∀ (m : ☐ M) → Proto☐ (P m)) → Proto☐ (com q P)

record End_ ℓ : ★_ ℓ where
  constructor end

End : ∀ {ℓ} → ★_ ℓ
End = End_ _

module _ {{_ : UA}} where
    End-uniq : End ≡ 𝟙
    End-uniq = ua (equiv _ _ (λ _ → refl) (λ _ → refl))

⟦_⟧ᴵᴼ : InOut → ∀{ℓ}(M : ★_ ℓ)(P : M → ★_ ℓ) → ★_ ℓ
⟦_⟧ᴵᴼ In  = Π
⟦_⟧ᴵᴼ Out = Σ

⟦_⟧ : ∀ {ℓ} → Proto_ ℓ → ★_ ℓ
⟦ end     ⟧ = End
⟦ com q P ⟧ = ⟦ q ⟧ᴵᴼ _ λ m → ⟦ P m ⟧

⟦_⊥⟧ : Proto → ★
⟦ P ⊥⟧ = ⟦ dual P ⟧

ℛ⟦_⟧ : ∀{ℓ}(P : Proto_ ℓ) (p q : ⟦ P ⟧) → ★_ ℓ
ℛ⟦ end    ⟧ p q = End
ℛ⟦ recv P ⟧ p q = ∀ m → ℛ⟦ P m ⟧ (p m) (q m)
ℛ⟦ send P ⟧ p q = Σ (fst p ≡ fst q) λ e → ℛ⟦ P (fst q) ⟧ (subst (⟦_⟧ ∘ P) e (snd p)) (snd q)

ℛ⟦_⟧-refl : ∀ {ℓ}(P : Proto_ ℓ) → Reflexive ℛ⟦ P ⟧
ℛ⟦ end    ⟧-refl     = end
ℛ⟦ recv P ⟧-refl     = λ m → ℛ⟦ P m ⟧-refl
ℛ⟦ send P ⟧-refl {x} = refl , ℛ⟦ P (fst x) ⟧-refl

ℛ⟦_⟧-sym : ∀ {ℓ}(P : Proto_ ℓ) → Symmetric ℛ⟦ P ⟧
ℛ⟦ end    ⟧-sym p          = end
ℛ⟦ recv P ⟧-sym p          = λ m → ℛ⟦ P m ⟧-sym (p m)
ℛ⟦ send P ⟧-sym (refl , q) = refl , ℛ⟦ P _ ⟧-sym q    -- TODO HoTT

ℛ⟦_⟧-trans : ∀ {ℓ}(P : Proto_ ℓ) → Transitive ℛ⟦ P ⟧
ℛ⟦ end    ⟧-trans p          q          = end
ℛ⟦ recv P ⟧-trans p          q          = λ m → ℛ⟦ P m ⟧-trans (p m) (q m)
ℛ⟦ send P ⟧-trans (refl , p) (refl , q) = refl , ℛ⟦ P _ ⟧-trans p q    -- TODO HoTT

send′ : ★ → Proto → Proto
send′ M P = send λ (_ : M) → P

recv′ : ★ → Proto → Proto
recv′ M P = recv λ (_ : M) → P

module send/recv-𝟘 (P : 𝟘 → Proto){{_ : FunExt}}{{_ : UA}} where
    P⊤ : Proto
    P⊤ = recvE 𝟘 P

    P0 : Proto
    P0 = sendE 𝟘 P

    P0-empty : ⟦ P0 ⟧ ≡ 𝟘
    P0-empty = ua (equiv fst (λ()) (λ()) (λ { (() , _) }))

    P⊤-uniq : ⟦ P⊤ ⟧ ≡ 𝟙
    P⊤-uniq = Π𝟘-uniq _

open send/recv-𝟘 (λ _ → end) public

≡ᴾ-refl : ∀ P → P ≡ᴾ P
≡ᴾ-refl end       = end
≡ᴾ-refl (com q P) = com refl λ m → ≡ᴾ-refl (P m)

≡ᴾ-reflexive : ∀ {P Q} → P ≡ Q → P ≡ᴾ Q
≡ᴾ-reflexive refl = ≡ᴾ-refl _

≡ᴾ-sym : Symmetric _≡ᴾ_
≡ᴾ-sym end = end
≡ᴾ-sym (com refl r) = com refl λ m → ≡ᴾ-sym (r m)

≡ᴾ-trans : Transitive _≡ᴾ_
≡ᴾ-trans end qr = qr
≡ᴾ-trans (com refl x) (com refl x₁) = com refl (λ m → ≡ᴾ-trans (x m) (x₁ m))

!ᴾ = ≡ᴾ-sym
_∙ᴾ_ = ≡ᴾ-trans

dual-involutive : ∀ P → dual (dual P) ≡ᴾ P
dual-involutive end       = end
dual-involutive (com q P) = com (dualᴵᴼ-involutive q) λ m → dual-involutive (P m)

module _ {{_ : FunExt}} where
    ≡ᴾ-sound : ∀ {P Q} → P ≡ᴾ Q → P ≡ Q
    ≡ᴾ-sound end            = refl
    ≡ᴾ-sound (com refl P≡Q) = ap (com _) (λ= λ m → ≡ᴾ-sound (P≡Q m))

    ≡ᴾ-cong : ∀ {P Q} (f : Proto → Proto) → P ≡ᴾ Q → f P ≡ᴾ f Q
    ≡ᴾ-cong f P≡Q = ≡ᴾ-reflexive (ap f (≡ᴾ-sound P≡Q))

    dual-equiv : Is-equiv dual
    dual-equiv = self-inv-is-equiv (≡ᴾ-sound ∘ dual-involutive)

    dual-inj : ∀ {P Q} → dual P ≡ dual Q → P ≡ Q
    dual-inj = Is-equiv.injective dual-equiv

source-of-idempotent : ∀ P → source-of (source-of P) ≡ᴾ source-of P
source-of-idempotent end       = end
source-of-idempotent (com _ P) = com refl λ m → source-of-idempotent (P m)

source-of-dual-oblivious : ∀ P → source-of (dual P) ≡ᴾ source-of P
source-of-dual-oblivious end       = end
source-of-dual-oblivious (com _ P) = com refl λ m → source-of-dual-oblivious (P m)

sink-of : Proto → Proto
sink-of = dual ∘ source-of

Sink : Proto → ★
Sink P = ⟦ sink-of P ⟧

sink : ∀ P → Sink P
sink end         = _
sink (com _ P) x = sink (P x)

module _ {{_ : FunExt}} where
    sink-contr : ∀ P s → sink P ≡ s
    sink-contr end       s = refl
    sink-contr (com _ P) s = λ= λ m → sink-contr (P m) (s m)

    Sink-is-contr : ∀ P → Is-contr (Sink P)
    Sink-is-contr P = sink P , sink-contr P

    𝟙≃Sink : ∀ P → 𝟙 ≃ Sink P
    𝟙≃Sink P = Is-contr-to-Is-equiv.𝟙≃ (Sink-is-contr P)

Log : Proto → ★
Log P = ⟦ source-of P ⟧

_>>=_ : (P : Proto) → (Log P → Proto) → Proto
end     >>= Q = Q _
com q P >>= Q = com q λ m → P m >>= λ ms → Q (m , ms)

_>>_ : Proto → Proto → Proto
P >> Q = P >>= λ _ → Q

replicateᴾ : ℕ → Proto → Proto
replicateᴾ 0       P = end
replicateᴾ (suc n) P = P >> replicateᴾ n P

++Log : ∀ (P : Proto){Q : Log P → Proto} (xs : Log P) → Log (Q xs) → Log (P >>= Q)
++Log end       _        ys = ys
++Log (com q P) (x , xs) ys = x , ++Log (P x) xs ys

>>=-right-unit : ∀ P → (P >> end) ≡ᴾ P
>>=-right-unit end       = end
>>=-right-unit (com q P) = com refl λ m → >>=-right-unit (P m)

>>=-assoc : ∀ (P : Proto)(Q : Log P → Proto)(R : Log (P >>= Q) → Proto)
            → P >>= (λ x → Q x >>= (λ y → R (++Log P x y))) ≡ᴾ ((P >>= Q) >>= R)
>>=-assoc end       Q R = ≡ᴾ-refl (Q _ >>= R)
>>=-assoc (com q P) Q R = com refl λ m → >>=-assoc (P m) (λ ms → Q (m , ms)) (λ ms → R (m , ms))

data Accept? : ★ where
  accept reject : Accept?
data Is-accept : Accept? → ★ where
  accept : Is-accept accept

module _ {A : ★} (Aᴾ : A → Proto) where
    extend-send : Proto → Proto
    extend-send end      = end
    extend-send (send P) = send [inl: (λ m → extend-send (P m)) ,inr: Aᴾ ]
    extend-send (recv P) = recv λ m → extend-send (P m)

    extend-recv : Proto → Proto
    extend-recv end      = end
    extend-recv (recv P) = recv [inl: (λ m → extend-recv (P m)) ,inr: Aᴾ ]
    extend-recv (send P) = send λ m → extend-recv (P m)

module _ {A : ★} (Aᴾ : A → Proto) where
    dual-extend-send : ∀ P → dual (extend-send Aᴾ P) ≡ᴾ extend-recv (dual ∘ Aᴾ) (dual P)
    dual-extend-send end      = end
    dual-extend-send (recv P) = com refl (λ m → dual-extend-send (P m))
    dual-extend-send (send P) = com refl [inl: (λ m → dual-extend-send (P m))
                                         ,inr: (λ x → ≡ᴾ-refl (dual (Aᴾ x))) ]

data Abort : ★ where abort : Abort

Abortᴾ : Abort → Proto
Abortᴾ _ = end

add-abort : Proto → Proto
add-abort = extend-send Abortᴾ

telecom : ∀ P → ⟦ P ⟧ → ⟦ P ⊥⟧ → Log P
telecom end      _       _       = _
telecom (recv P) p       (m , q) = m , telecom (P m) (p m) q
telecom (send P) (m , p) q       = m , telecom (P m) p (q m)

liftᴾ : ∀ a {ℓ} → Proto_ ℓ → Proto_ (a ⊔ ℓ)
liftᴾ a end        = end
liftᴾ a (com io P) = com io λ m → liftᴾ a (P (lower {ℓ = a} m))

lift-proc : ∀ a {ℓ} (P : Proto_ ℓ) → ⟦ P ⟧ → ⟦ liftᴾ a P ⟧
lift-proc a {ℓ} end      end     = end
lift-proc a {ℓ} (send P) (m , p) = lift m , lift-proc a (P m) p
lift-proc a {ℓ} (recv P) p       = λ { (lift m) → lift-proc _ (P m) (p m) }

module MonomorphicSky (P : Proto₀) where
  Cloud : Proto₀
  Cloud = recv λ (t   : ⟦ P  ⟧) →
          recv λ (u   : ⟦ P ⊥⟧) →
          send λ (log : Log P)  →
          end
  cloud : ⟦ Cloud ⟧
  cloud t u = telecom P t u , _

module PolySky where
  Cloud : Proto_ ₁
  Cloud = recv λ (P : Proto₀) →
          liftᴾ ₁ (MonomorphicSky.Cloud P)
  cloud : ⟦ Cloud ⟧
  cloud P = lift-proc ₁ (MonomorphicSky.Cloud P) (MonomorphicSky.cloud P)

module PolySky' where
  Cloud : Proto_ ₁
  Cloud = recv λ (P   : Proto₀) →
          recv λ (t   : Lift ⟦ P  ⟧)  →
          recv λ (u   : Lift ⟦ P ⊥⟧)  →
          send λ (log : Lift (Log P)) →
          end
  cloud : ⟦ Cloud ⟧
  cloud P (lift t) (lift u) = lift (telecom P t u) , _

data Choreo (I : ★) : ★₁ where
  _-[_]→_⁏_ : (A : I) (M : ★) (B : I) (ℂ : ..(m : M) → Choreo I) → Choreo I
  _-[_]→★⁏_ : (A : I) (M : ★)         (ℂ :   (m : M) → Choreo I) → Choreo I
  end       : Choreo I

module _ {I : ★} where 
    _-[_]→ø⁏_ : ∀ (A : I)(M : ★)(ℂ : ..(m : M) → Choreo I) → Choreo I
    A -[ M ]→ø⁏ ℂ = A -[ ☐ M ]→★⁏ λ { [ m ] → ℂ m }

    _//_ : (ℂ : Choreo I) (p : I → 𝟚) → Proto
    (A -[ M ]→ B ⁏ ℂ) // p = case p A
                               0: case p B
                                    0: recv (λ { [ m ] → ℂ m // p })
                                    1: recv (λ     m   → ℂ m // p)
                               1: send (λ m → ℂ m // p)
    (A -[ M ]→★⁏   ℂ) // p = com (case p A 0: In 1: Out) λ m → ℂ m // p
    end               // p = end

    ℂObserver : Choreo I → Proto
    ℂObserver ℂ = ℂ // λ _ → 0₂

    ℂLog : Choreo I → Proto
    ℂLog ℂ = ℂ // λ _ → 1₂

    ℂLog-IsSource : ∀ ℂ → IsSource (ℂLog ℂ)
    ℂLog-IsSource (A -[ M ]→ B ⁏ ℂ) = com λ m → ℂLog-IsSource (ℂ m)
    ℂLog-IsSource (A -[ M ]→★⁏   ℂ) = com λ m → ℂLog-IsSource (ℂ m)
    ℂLog-IsSource end               = end

    ℂObserver-IsSink : ∀ ℂ → IsSink (ℂObserver ℂ)
    ℂObserver-IsSink (A -[ M ]→ B ⁏ ℂ) = com λ { [ m ] → ℂObserver-IsSink (ℂ m) }
    ℂObserver-IsSink (A -[ M ]→★⁏   ℂ) = com λ m → ℂObserver-IsSink (ℂ m)
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

    choreo-bi : {p : I → 𝟚}(ℂ : Choreo I) → ⟦ ℂ // p ⟧ → ⟦ ℂ // (not ∘ p) ⟧ → ⟦ ℂLog ℂ ⟧
    choreo-bi {p} ℂ ℂp ℂ¬p = choreo-merge ℂ (R-p-¬p-1 p) ℂp ℂ¬p

choreo2 : (ℂ : Choreo 𝟚) → ⟦ ℂ // id ⟧ → ⟦ ℂ // not ⟧ → ⟦ ℂLog ℂ ⟧
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

  choreo3 : (ℂ : Choreo 𝟛) → ⟦ ℂ // 0₃? ⟧ → ⟦ ℂ // 1₃? ⟧ → ⟦ ℂ // 2₃? ⟧ → ⟦ ℂLog ℂ ⟧
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

  choreo3' : (ℂ : Choreo 𝟛) → ⟦ ℂ // 0₃? ⟧ → ⟦ ℂ // 1₃? ⟧ → ⟦ ℂ // 2₃? ⟧ → ⟦ ℂLog ℂ ⟧
  choreo3' ℂ p0 p1 p2 = choreo-merge ℂ (R-p-¬p-1 0₃?) p0 (choreo-merge ℂ R-1-2-¬0 p1 p2)
     where R-1-2-¬0 : ∀ i → R (1₃? i) (2₃? i) (not (0₃? i))
           R-1-2-¬0 0₃ = R000
           R-1-2-¬0 1₃ = R101
           R-1-2-¬0 2₃ = R011

>>=-com : (P : Proto){Q : Log P → Proto}{R : Log P → Proto}
          → ⟦ P >>= Q  ⟧
          → ⟦ P >>= R ⊥⟧
          → Σ (Log P) (λ t → ⟦ Q t ⟧ × ⟦ R t ⊥⟧)
>>=-com end      p0       p1       = _ , p0 , p1
>>=-com (send P) (m , p0) p1       = first (_,_ m) (>>=-com (P m) p0 (p1 m))
>>=-com (recv P) p0       (m , p1) = first (_,_ m) (>>=-com (P m) (p0 m) p1)

>>-com : (P : Proto){Q R : Proto}
       → ⟦ P >> Q  ⟧
       → ⟦ P >> R ⊥⟧
       → Log P × ⟦ Q ⟧ × ⟦ R ⊥⟧
>>-com P p q = >>=-com P p q

module _ {{_ : FunExt}} where
    ap->>= : ∀ P {Q₀ Q₁} → (∀ {log} → ⟦ Q₀ log ⟧ ≡ ⟦ Q₁ log ⟧) → ⟦ P >>= Q₀ ⟧ ≡ ⟦ P >>= Q₁ ⟧
    ap->>= end      Q= = Q=
    ap->>= (send P) Q= = Σ=′ _ λ m → ap->>= (P m) Q=
    ap->>= (recv P) Q= = Π=′ _ λ m → ap->>= (P m) Q=

module _ {{_ : FunExt}}{{_ : UA}} where
    P2 = send′ 𝟚 end

    0₂≢1₂ : 0₂ ≢ 1₂
    0₂≢1₂ ()

    𝟘≢ : ∀ {A} (x : A) → 𝟘 ≢ A
    𝟘≢ x e = coe! e x

    𝟘≢𝟙 : 𝟘 ≢ 𝟙
    𝟘≢𝟙 = 𝟘≢ _

    𝟘≢𝟚 : 𝟘 ≢ 𝟚
    𝟘≢𝟚 = 𝟘≢ 0₂


module ClientServerV1 (Query : ★₀) (Resp : Query → ★₀) (P : Proto) where
    Client : ℕ → Proto
    Client zero    = P
    Client (suc n) = send λ (q : Query) → recv λ (r : Resp q) → Client n

    Server : ℕ → Proto
    Server zero    = P
    Server (suc n) = recv λ (q : Query) → send λ (r : Resp q) → Server n

module ClientServerV2 (Query : ★₀) (Resp : Query → ★₀) where
    ClientRound ServerRound : Proto
    ClientRound = send λ (q : Query) → recv λ (r : Resp q) → end
    ServerRound = dual ClientRound

    Client Server : ℕ → Proto
    Client n = replicateᴾ n ClientRound
    Server = dual ∘ Client

    DynamicServer StaticServer : Proto
    DynamicServer = recv λ n →
                    Server n
    StaticServer  = send λ n →
                    Server n

    module PureServer (serve : Π Query Resp) where
      server : ∀ n → ⟦ Server n ⟧
      server zero      = _
      server (suc n) q = serve q , server n

module _ {{_ : FunExt}} where
  dual-Log : ∀ P → Log (dual P) ≡ Log P
  dual-Log P = ap ⟦_⟧ (≡ᴾ-sound (source-of-dual-oblivious P))

dual->> : ∀ P Q → dual (P >> Q) ≡ᴾ dual P >> dual Q
dual->> end      Q = ≡ᴾ-refl _
dual->> (recv P) Q = com refl λ m → dual->> (P m) Q
dual->> (send P) Q = com refl λ m → dual->> (P m) Q

  {- ohoh!
  dual->>= : ∀ P (Q : Log P → Proto) → dual (P >>= Q) ≡ᴾ dual P >>= (dual ∘ Q ∘ coe (dual-Log P))
  dual->>= end Q = ≡ᴾ-refl _
  dual->>= (recv M P) Q = ProtoRel.com refl M (λ m → {!dual->>= (P m) (Q ∘ _,_ m)!})
  dual->>= (send M P) Q = ProtoRel.com refl M (λ m → {!!})
  -}

module _ {{_ : FunExt}} (P : Proto) where
    dual-replicateᴾ : ∀ n → dual (replicateᴾ n P) ≡ᴾ replicateᴾ n (dual P)
    dual-replicateᴾ zero    = end
    dual-replicateᴾ (suc n) = dual->> P (replicateᴾ n P) ∙ᴾ ≡ᴾ-cong (_>>_ (dual P)) (dual-replicateᴾ n)

_⊕_ : (l r : Proto) → Proto
l ⊕ r = send [L: l R: r ]

_&_ : (l r : Proto) → Proto
l & r = recv [L: l R: r ]

module _ {{_ : FunExt}} where
    dual-⊕ : ∀ {P Q} → dual (P ⊕ Q) ≡ dual P & dual Q
    dual-⊕ = recv=′ [L: refl R: refl ]

    dual-& : ∀ {P Q} → dual (P & Q) ≡ dual P ⊕ dual Q
    dual-& = send=′ [L: refl R: refl ]

module _ {{_ : FunExt}}{{_ : UA}} where
    &-comm : ∀ P Q → P & Q ≡ Q & P
    &-comm P Q = recv≃ LR!-equiv [L: refl R: refl ]

    ⊕-comm : ∀ P Q → P ⊕ Q ≡ Q ⊕ P
    ⊕-comm P Q = send≃ LR!-equiv [L: refl R: refl ]

module _ {P Q R S} where
    ⊕-map : (⟦ P ⟧ → ⟦ Q ⟧) → (⟦ R ⟧ → ⟦ S ⟧) → ⟦ P ⊕ R ⟧ → ⟦ Q ⊕ S ⟧
    ⊕-map f g (`L , pr) = `L , f pr
    ⊕-map f g (`R , pr) = `R , g pr

    &-map : (⟦ P ⟧ → ⟦ Q ⟧) → (⟦ R ⟧ → ⟦ S ⟧) → ⟦ P & R ⟧ → ⟦ Q & S ⟧
    &-map f g p `L = f (p `L)
    &-map f g p `R = g (p `R)

module _ {P Q} where
    ⊕→⊎ : ⟦ P ⊕ Q ⟧ → ⟦ P ⟧ ⊎ ⟦ Q ⟧
    ⊕→⊎ (`L , p) = inl p
    ⊕→⊎ (`R , q) = inr q

    ⊎→⊕ : ⟦ P ⟧ ⊎ ⟦ Q ⟧ → ⟦ P ⊕ Q ⟧
    ⊎→⊕ (inl p) = `L , p
    ⊎→⊕ (inr q) = `R , q

    ⊎→⊕→⊎ : ∀ x → ⊎→⊕ (⊕→⊎ x) ≡ x
    ⊎→⊕→⊎ (`L , _) = refl
    ⊎→⊕→⊎ (`R , _) = refl

    ⊕→⊎→⊕ : ∀ x → ⊕→⊎ (⊎→⊕ x) ≡ x
    ⊕→⊎→⊕ (inl _) = refl
    ⊕→⊎→⊕ (inr _) = refl

    ⊕≃⊎ : ⟦ P ⊕ Q ⟧ ≃ (⟦ P ⟧ ⊎ ⟦ Q ⟧)
    ⊕≃⊎ = ⊕→⊎ , record { linv = ⊎→⊕ ; is-linv = ⊎→⊕→⊎ ; rinv = ⊎→⊕ ; is-rinv = ⊕→⊎→⊕ }

    ⊕≡⊎ : {{_ : UA}} → ⟦ P ⊕ Q ⟧ ≡ (⟦ P ⟧ ⊎ ⟦ Q ⟧)
    ⊕≡⊎ = ua ⊕≃⊎

    &→× : ⟦ P & Q ⟧ → ⟦ P ⟧ × ⟦ Q ⟧
    &→× p = p `L , p `R

    ×→& : ⟦ P ⟧ × ⟦ Q ⟧ → ⟦ P & Q ⟧
    ×→& (p , q) `L = p
    ×→& (p , q) `R = q

    &→×→& : ∀ x → &→× (×→& x) ≡ x
    &→×→& (p , q) = refl

    module _ {{_ : FunExt}} where
        ×→&→× : ∀ x → ×→& (&→× x) ≡ x
        ×→&→× p = λ= λ { `L → refl ; `R → refl }

        &≃× : ⟦ P & Q ⟧ ≃ (⟦ P ⟧ × ⟦ Q ⟧)
        &≃× = &→× , record { linv = ×→& ; is-linv = ×→&→× ; rinv = ×→& ; is-rinv = &→×→& }

        &≡× : {{_ : UA}} → ⟦ P & Q ⟧ ≡ (⟦ P ⟧ × ⟦ Q ⟧)
        &≡× = ua &≃×

module _ {{_ : FunExt}}{{_ : UA}} where
    P⊤-& : ∀ P → ⟦ P⊤ & P ⟧ ≡ ⟦ P ⟧
    P⊤-& P = &≡× ∙ ap (flip _×_ ⟦ P ⟧) P⊤-uniq ∙ Σ𝟙-snd

    P0-⊕ : ∀ P → ⟦ P0 ⊕ P ⟧ ≡ ⟦ P ⟧
    P0-⊕ P = ⊕≡⊎ ∙ ap (flip _⊎_ ⟦ P ⟧) Σ𝟘-fst ∙ ⊎-comm ∙ ! ⊎𝟘-inl

    &-assoc : ∀ P Q R → ⟦ P & (Q & R) ⟧ ≡ ⟦ (P & Q) & R ⟧
    &-assoc P Q R = &≡× ∙ (ap (_×_ ⟦ P ⟧) &≡× ∙ ×-assoc ∙ ap (flip _×_ ⟦ R ⟧) (! &≡×)) ∙ ! &≡×

    ⊕-assoc : ∀ P Q R → ⟦ P ⊕ (Q ⊕ R) ⟧ ≡ ⟦ (P ⊕ Q) ⊕ R ⟧
    ⊕-assoc P Q R = ⊕≡⊎ ∙ (ap (_⊎_ ⟦ P ⟧) ⊕≡⊎ ∙ ⊎-assoc ∙ ap (flip _⊎_ ⟦ R ⟧) (! ⊕≡⊎)) ∙ ! ⊕≡⊎

module _ where

  _⅋_ : Proto → Proto → Proto
  end    ⅋ Q      = Q
  recv P ⅋ Q      = recv λ m → P m ⅋ Q
  P      ⅋ end    = P
  P      ⅋ recv Q = recv λ m → P ⅋ Q m
  send P ⅋ send Q = send [inl: (λ m → P m ⅋ send Q)
                         ,inr: (λ n → send P ⅋ Q n) ]

  module _ {{_ : FunExt}}{{_ : UA}} where
    -- absorption
    ⊤-⅋ : ∀ P → ⟦ P⊤ ⅋ P ⟧
    ⊤-⅋ P = λ()

  _⊗_ : Proto → Proto → Proto
  end    ⊗ Q      = Q
  send P ⊗ Q      = send λ m → P m ⊗ Q
  P      ⊗ end    = P
  P      ⊗ send Q = send λ m → P ⊗ Q m
  recv P ⊗ recv Q = recv [inl: (λ m → P m ⊗ recv Q)
                         ,inr: (λ n → recv P ⊗ Q n) ]

  _-o_ : (P Q : Proto) → Proto
  P -o Q = dual P ⅋ Q

  _o-o_ : (P Q : Proto) → Proto
  P o-o Q = (P -o Q) ⊗ (Q -o P)

  module _ {{_ : FunExt}} where
    ⊗-endR : ∀ P → P ⊗ end ≡ P
    ⊗-endR end      = refl
    ⊗-endR (recv _) = refl
    ⊗-endR (send P) = send=′ λ m → ⊗-endR (P m)

    ⅋-endR : ∀ P → P ⅋ end ≡ P
    ⅋-endR end      = refl
    ⅋-endR (send _) = refl
    ⅋-endR (recv P) = recv=′ λ m → ⅋-endR (P m)

  module _ {{_ : FunExt}}{{_ : UA}} where
    ⊗-sendR : ∀ P{M}(Q : M → Proto) → ⟦ P ⊗ send Q ⟧ ≡ (Σ M λ m → ⟦ P ⊗ Q m ⟧)
    ⊗-sendR end      Q = refl
    ⊗-sendR (recv P) Q = refl
    ⊗-sendR (send P) Q = (Σ=′ _ λ m → ⊗-sendR (P m) Q) ∙ ΣΣ-comm

    ⊗-comm : ∀ P Q → ⟦ P ⊗ Q ⟧ ≡ ⟦ Q ⊗ P ⟧
    ⊗-comm end      Q        = ! ap ⟦_⟧ (⊗-endR Q)
    ⊗-comm (send P) Q        = (Σ=′ _ λ m → ⊗-comm (P m) Q) ∙ ! ⊗-sendR Q P
    ⊗-comm (recv P) end      = refl
    ⊗-comm (recv P) (send Q) = Σ=′ _ λ m → ⊗-comm (recv P) (Q m)
    ⊗-comm (recv P) (recv Q) = Π≃ ⊎-comm-equiv [inl: (λ m → ⊗-comm (P m) (recv Q))
                                               ,inr: (λ m → ⊗-comm (recv P) (Q m)) ]

    ⊗-assoc : ∀ P Q R → P ⊗ (Q ⊗ R) ≡ (P ⊗ Q) ⊗ R
    ⊗-assoc end      Q        R        = refl
    ⊗-assoc (send P) Q        R        = send=′ λ m → ⊗-assoc (P m) Q R
    ⊗-assoc (recv P) end      R        = refl
    ⊗-assoc (recv P) (send Q) R        = send=′ λ m → ⊗-assoc (recv P) (Q m) R
    ⊗-assoc (recv P) (recv Q) end      = refl
    ⊗-assoc (recv P) (recv Q) (send R) = send=′ λ m → ⊗-assoc (recv P) (recv Q) (R m)
    ⊗-assoc (recv P) (recv Q) (recv R) = recv≃ ⊎-assoc-equiv
                                             λ { (inl m)       → ⊗-assoc (P m) (recv Q) (recv R)
                                               ; (inr (inl m)) → ⊗-assoc (recv P) (Q m) (recv R)
                                               ; (inr (inr m)) → ⊗-assoc (recv P) (recv Q) (R m) }


    ⅋-recvR : ∀ P{M}(Q : M → Proto) → ⟦ P ⅋ recv Q ⟧ ≡ (Π M λ m → ⟦ P ⅋ Q m ⟧)
    ⅋-recvR end      Q = refl
    ⅋-recvR (send P) Q = refl
    ⅋-recvR (recv P) Q = (Π=′ _ λ m → ⅋-recvR (P m) Q) ∙ ΠΠ-comm

    ⅋-comm : ∀ P Q → ⟦ P ⅋ Q ⟧ ≡ ⟦ Q ⅋ P ⟧
    ⅋-comm end      Q        = ! ap ⟦_⟧ (⅋-endR Q)
    ⅋-comm (recv P) Q        = (Π=′ _ λ m → ⅋-comm (P m) Q) ∙ ! ⅋-recvR Q P
    ⅋-comm (send P) end      = refl
    ⅋-comm (send P) (recv Q) = Π=′ _ λ m → ⅋-comm (send P) (Q m)
    ⅋-comm (send P) (send Q) = Σ≃ ⊎-comm-equiv [inl: (λ m → ⅋-comm (P m) (send Q))
                                               ,inr: (λ m → ⅋-comm (send P) (Q m)) ]

    ⅋-assoc : ∀ P Q R → P ⅋ (Q ⅋ R) ≡ (P ⅋ Q) ⅋ R
    ⅋-assoc end      Q        R        = refl
    ⅋-assoc (recv P) Q        R        = recv=′ λ m → ⅋-assoc (P m) Q R
    ⅋-assoc (send P) end      R        = refl
    ⅋-assoc (send P) (recv Q) R        = recv=′ λ m → ⅋-assoc (send P) (Q m) R
    ⅋-assoc (send P) (send Q) end      = refl
    ⅋-assoc (send P) (send Q) (recv R) = recv=′ λ m → ⅋-assoc (send P) (send Q) (R m)
    ⅋-assoc (send P) (send Q) (send R) = send≃ ⊎-assoc-equiv
                                             λ { (inl m)       → ⅋-assoc (P m) (send Q) (send R)
                                               ; (inr (inl m)) → ⅋-assoc (send P) (Q m) (send R)
                                               ; (inr (inr m)) → ⅋-assoc (send P) (send Q) (R m) }

  module _ {P Q R}{{_ : FunExt}} where
    dist-⊗-⊕′ : (Q ⊕ R) ⊗ P ≡ (Q ⊗ P) ⊕ (R ⊗ P)
    dist-⊗-⊕′ = send=′ [L: refl R: refl ]

    dist-⅋-&′ : (Q & R) ⅋ P ≡ (Q ⅋ P) & (R ⅋ P)
    dist-⅋-&′ = recv=′ [L: refl R: refl ]

    module _ {{_ : UA}} where
        dist-⊗-⊕ : ⟦ P ⊗ (Q ⊕ R) ⟧ ≡ ⟦ (P ⊗ Q) ⊕ (P ⊗ R) ⟧
        dist-⊗-⊕ = ⊗-comm P (Q ⊕ R)
                 ∙ ap ⟦_⟧ dist-⊗-⊕′
                 ∙ ⊕≡⊎
                 ∙ ⊎= (⊗-comm Q P) (⊗-comm R P)
                 ∙ ! ⊕≡⊎

        dist-⅋-& : ⟦ P ⅋ (Q & R) ⟧ ≡ ⟦ (P ⅋ Q) & (P ⅋ R) ⟧
        dist-⅋-& = ⅋-comm P (Q & R)
                 ∙ ap ⟦_⟧ dist-⅋-&′
                 ∙ &≡×
                 ∙ ×= (⅋-comm Q P) (⅋-comm R P)
                 ∙ ! &≡×

  -- P ⟦⊗⟧ Q ≃ ⟦ P ⊗ Q ⟧
  -- but potentially more convenient
  _⟦⊗⟧_ : Proto → Proto → ★
  end    ⟦⊗⟧ Q      = ⟦ Q ⟧
  send P ⟦⊗⟧ Q      = ∃ λ m → P m ⟦⊗⟧ Q
  P      ⟦⊗⟧ end    = ⟦ P ⟧
  P      ⟦⊗⟧ send Q = ∃ λ m → P ⟦⊗⟧ Q m
  recv P ⟦⊗⟧ recv Q = (Π _ λ m → P m    ⟦⊗⟧ recv Q)
                    × (Π _ λ n → recv P ⟦⊗⟧ Q n)

  module _ {{_ : FunExt}}{{_ : UA}} where
    ⟦⊗⟧-correct : ∀ P Q → P ⟦⊗⟧ Q ≡ ⟦ P ⊗ Q ⟧
    ⟦⊗⟧-correct end      Q        = refl
    ⟦⊗⟧-correct (send P) Q        = Σ=′ _ λ m → ⟦⊗⟧-correct (P m) Q
    ⟦⊗⟧-correct (recv P) end      = refl
    ⟦⊗⟧-correct (recv P) (send Q) = Σ=′ _ λ n → ⟦⊗⟧-correct (recv P) (Q n)
    ⟦⊗⟧-correct (recv P) (recv Q) = ! dist-×-Π
                                  ∙ Π=′ (_ ⊎ _) λ { (inl m)  → ⟦⊗⟧-correct (P m) (recv Q)
                                                  ; (inr n) → ⟦⊗⟧-correct (recv P) (Q n) }

  -- an alternative, potentially more convenient
  _⟦⅋⟧_ : Proto → Proto → ★
  end    ⟦⅋⟧ Q      = ⟦ Q ⟧
  recv P ⟦⅋⟧ Q      = ∀ m → P m ⟦⅋⟧ Q
  P      ⟦⅋⟧ end    = ⟦ P ⟧
  P      ⟦⅋⟧ recv Q = ∀ n → P ⟦⅋⟧ Q n
  send P ⟦⅋⟧ send Q = (∃ λ m → P m    ⟦⅋⟧ send Q)
                    ⊎ (∃ λ n → send P ⟦⅋⟧ Q n)

  module _ {{_ : FunExt}}{{_ : UA}} where
    ⟦⅋⟧-correct : ∀ P Q → P ⟦⅋⟧ Q ≡ ⟦ P ⅋ Q ⟧
    ⟦⅋⟧-correct end      Q        = refl
    ⟦⅋⟧-correct (recv P) Q        = Π=′ _ λ m → ⟦⅋⟧-correct (P m) Q
    ⟦⅋⟧-correct (send P) end      = refl
    ⟦⅋⟧-correct (send P) (recv Q) = Π=′ _ λ n → ⟦⅋⟧-correct (send P) (Q n)
    ⟦⅋⟧-correct (send P) (send Q) = ! dist-⊎-Σ
                                  ∙ Σ=′ (_ ⊎ _) λ { (inl m) → ⟦⅋⟧-correct (P m) (send Q)
                                                  ; (inr n) → ⟦⅋⟧-correct (send P) (Q n) }

                                                  {-
    -- sends can be pulled out of tensor
    source->>=-⊗ : ∀ P Q R → (source-of P >>= Q) ⊗ R ≡ source-of P >>= λ log → (Q log ⊗ R)
    source->>=-⊗ end       Q R = refl
    source->>=-⊗ (com _ P) Q R = send=′ λ m → source->>=-⊗ (P m) (Q ∘ _,_ m) R

    -- consequence[Q = const end]: ∀ P R → source-of P ⊗ R ≡ source-of P >> R

    -- recvs can be pulled out of par
    sink->>=-⅋ : ∀ P Q R → (sink-of P >>= Q) ⅋ R ≡ sink-of P >>= λ log → (Q log ⅋ R)
    sink->>=-⅋ end       Q R = refl
    sink->>=-⅋ (com _ P) Q R = recv=′ λ m → sink->>=-⅋ (P m) (Q ∘ _,_ m) R

    -- consequence[Q = const end]: ∀ P R → sink-of P ⅋ R ≡ sink-of P >> R

  Log-⅋-× : ∀ {P Q} → Log (P ⅋ Q) → Log P × Log Q
  Log-⅋-× {end}   {Q}      q           = end , q
  Log-⅋-× {recv P}{Q}      (m , p)     = first  (_,_ m) $ Log-⅋-× {P m} {Q} p
  Log-⅋-× {send P}{end}    (m , p)     = (m , p) , end
  Log-⅋-× {send P}{recv Q} (m , p)     = second (_,_ m) $ Log-⅋-× {send P} {Q m} p
  Log-⅋-× {send P}{send Q} (inl m , p) = first  (_,_ m) $ Log-⅋-× {P m} {send Q} p
  Log-⅋-× {send P}{send Q} (inr m , p) = second (_,_ m) $ Log-⅋-× {send P} {Q m} p

  module _ {{_ : FunExt}} where
    ⊗⅋-dual : ∀ P Q → dual (P ⅋ Q) ≡ dual P ⊗ dual Q
    ⊗⅋-dual end Q = refl
    ⊗⅋-dual (recv P) Q = com=′ _ λ m → ⊗⅋-dual (P m) _
    ⊗⅋-dual (send P) end = refl
    ⊗⅋-dual (send P) (recv Q) = com=′ _ λ n → ⊗⅋-dual (send P) (Q n)
    ⊗⅋-dual (send P) (send Q) = com=′ _
      [inl: (λ m → ⊗⅋-dual (P m) (send Q))
      ,inr: (λ n → ⊗⅋-dual (send P) (Q n))
      ]

  data View-⅋-proto : Proto → Proto → ★₁ where
    end-X     : ∀ Q → View-⅋-proto end Q
    recv-X    : ∀ {M}(P : M → Proto)Q → View-⅋-proto (recv P) Q
    send-send : ∀ {M N}(P : M → Proto)(Q : N → Proto) → View-⅋-proto (send P) (send Q)
    send-recv : ∀ {M N}(P : M → Proto)(Q : N → Proto) → View-⅋-proto (send P) (recv Q)
    send-end  : ∀ {M}(P : M → Proto) → View-⅋-proto (send P) end

  view-⅋-proto : ∀ P Q → View-⅋-proto P Q
  view-⅋-proto end      Q        = end-X Q
  view-⅋-proto (recv P) Q        = recv-X P Q
  view-⅋-proto (send P) end      = send-end P
  view-⅋-proto (send P) (recv Q) = send-recv P Q
  view-⅋-proto (send P) (send Q) = send-send P Q

  data View-⊗-proto : Proto → Proto → ★₁ where
    end-X     : ∀ Q → View-⊗-proto end Q
    send-X    : ∀ {M}(P : M → Proto)Q → View-⊗-proto (send P) Q
    recv-recv : ∀ {M N}(P : M → Proto)(Q : N → Proto) → View-⊗-proto (recv P) (recv Q)
    recv-send : ∀ {M N}(P : M → Proto)(Q : N → Proto) → View-⊗-proto (recv P) (send Q)
    recv-end  : ∀ {M}(P : M → Proto) → View-⊗-proto (recv P) end

  view-⊗-proto : ∀ P Q → View-⊗-proto P Q
  view-⊗-proto end      Q        = end-X Q
  view-⊗-proto (send P) Q        = send-X P Q
  view-⊗-proto (recv P) end      = recv-end P
  view-⊗-proto (recv P) (recv Q) = recv-recv P Q
  view-⊗-proto (recv P) (send Q) = recv-send P Q

  -- the terminology used for the constructor follows the behavior of the combined process
  data View-⅋ : ∀ P Q → ⟦ P ⅋ Q ⟧ → ★₁ where
    sendL' : ∀ {M N}(P : M → Proto)(Q : N → Proto)(m  : M )(p : ⟦ P m ⅋ send Q ⟧) → View-⅋ (send P) (send Q) (inl m  , p)
    sendR' : ∀ {M N}(P : M → Proto)(Q : N → Proto)(n : N)(p : ⟦ send P ⅋ Q n ⟧) → View-⅋ (send P) (send Q) (inr n , p)
    recvL' : ∀ {M} (P : M → Proto) Q (p : ((m : M) → ⟦ P m ⅋ Q ⟧)) → View-⅋ (recv P) Q p
    recvR' : ∀ {M N} (P : M → Proto) (Q : N → Proto)(p : (n : N) → ⟦ send P ⅋ Q n ⟧) → View-⅋ (send P) (recv Q) p
    endL   : ∀ Q (p : ⟦ Q ⟧) → View-⅋ end Q p
    send'  : ∀ {M}(P : M → Proto)(m : M)(p : ⟦ P m ⟧) → View-⅋ (send P) end (m , p)

  view-⅋ : ∀ P Q (p : ⟦ P ⅋ Q ⟧) → View-⅋ P Q p
  view-⅋ end Q p = endL Q p
  view-⅋ (recv P) Q p = recvL' P Q p
  view-⅋ (send P) end (m , p) = send' P m p
  view-⅋ (send P) (recv Q) p = recvR' P Q p
  view-⅋ (send P) (send Q) (inl x , p) = sendL' P Q x p
  view-⅋ (send P) (send Q) (inr y , p) = sendR' P Q y p

  {-
  -- use coe (... ⅋-assoc P Q R)
  ⅋-assoc : ∀ P Q R → ⟦ P ⅋ (Q ⅋ R) ⟧ → ⟦ (P ⅋ Q) ⅋ R ⟧
  ⅋-assoc end      Q        R         s                 = s
  ⅋-assoc (recv P) Q        R         s m               = ⅋-assoc (P m) _ _ (s m)
  ⅋-assoc (send P) end      R         s                 = s
  ⅋-assoc (send P) (recv Q) R         s m               = ⅋-assoc (send P) (Q m) _ (s m)
  ⅋-assoc (send P) (send Q) end       s                 = s
  ⅋-assoc (send P) (send Q) (recv R)  s m               = ⅋-assoc (send P) (send Q) (R m) (s m)
  ⅋-assoc (send P) (send Q) (send R) (inl m , s)       = inl (inl m) , ⅋-assoc (P m) (send Q) (send R) s
  ⅋-assoc (send P) (send Q) (send R) (inr (inl m) , s) = inl (inr m) , ⅋-assoc (send P) (Q m) (send R) s
  ⅋-assoc (send P) (send Q) (send R) (inr (inr m) , s) = inr m       , ⅋-assoc (send P) (send Q) (R m) s

  -- use coe (⅋-endR P) instead
  ⅋-rend : ∀ P → ⟦ P ⅋ end ⟧  → ⟦ P ⟧
  ⅋-rend end      p = p
  ⅋-rend (send _) p = p
  ⅋-rend (recv P) p = λ m → ⅋-rend (P m) (p m)

  -- use coe! (⅋-endR P) instead
  ⅋-rend! : ∀ P  → ⟦ P ⟧ → ⟦ P ⅋ end ⟧
  ⅋-rend! end      p = p
  ⅋-rend! (send _) p = p
  ⅋-rend! (recv P) p = λ m → ⅋-rend! (P m) (p m)

  -- use coe! (⅋-recvR P Q) instead
  ⅋-isendR : ∀ {N} P Q → ⟦ P ⅋ recv Q ⟧ → (n : N) → ⟦ P ⅋ Q n ⟧
  ⅋-isendR end Q s n = s n
  ⅋-isendR (recv P) Q s n = λ m → ⅋-isendR (P m) Q (s m) n
  ⅋-isendR (send P) Q s n = s n


  -- see ⅋-recvR
  ⅋-recvR : ∀ {M} P Q → ((m : M) → ⟦ P ⅋ Q m ⟧) → ⟦ P ⅋ recv Q ⟧
  ⅋-recvR end      Q s = s
  ⅋-recvR (recv P) Q s = λ x → ⅋-recvR (P x) Q (λ m → s m x)
  ⅋-recvR (send P) Q s = s
  -}

  module _ {{_ : FunExt}}{{_ : UA}} where

    ⅋-sendR : ∀ {M}P{Q : M → Proto}(m : M) → ⟦ P ⅋ Q m ⟧ → ⟦ P ⅋ send Q ⟧
    ⅋-sendR end      m p = m , p
    ⅋-sendR (send P) m p = inr m , p
    ⅋-sendR (recv P) m p = λ x → ⅋-sendR (P x) m (p x)

    ⅋-sendL : ∀ {M}{P : M → Proto} Q (m : M) → ⟦ P m ⅋ Q ⟧ → ⟦ send P ⅋ Q ⟧
    ⅋-sendL {M} {P} Q m pq = coe (⅋-comm Q (send P)) (⅋-sendR Q m (coe (⅋-comm (P m) Q) pq))

    ⅋-id : ∀ P → ⟦ dual P ⅋ P ⟧
    ⅋-id end      = end
    ⅋-id (recv P) = λ x → ⅋-sendL (P x) x (⅋-id (P x))
    ⅋-id (send P) = λ x → ⅋-sendR (dual (P x)) x (⅋-id (P x))

  data View-∘ : ∀ P Q R → ⟦ P ⅋ Q ⟧ → ⟦ dual Q ⅋ R ⟧ → ★₁ where
    sendLL : ∀ {M N}(P : M → Proto)(Q : N → Proto) R (m : M)(p : ⟦ P m ⅋ send Q ⟧)(q : ⟦ dual (send Q) ⅋ R ⟧)
             → View-∘ (send P) (send Q) R (inl m , p) q
    recvLL : ∀ {M} (P : M → Proto) Q R
               (p : ((m : M) → ⟦ P m ⅋ Q ⟧))(q : ⟦ dual Q ⅋ R ⟧)
             → View-∘ (recv P) Q R p q
    recvR-sendR : ∀ {MP MQ MR}ioP(P : MP → Proto)(Q : MQ → Proto)(R : MR → Proto)
                    (mR : MR)(p : ⟦ com ioP P ⅋ recv Q ⟧)(q : ⟦ dual (recv Q) ⅋ R mR ⟧)
                    → View-∘ (com ioP P) (recv Q) (send R) p (inr mR , q)

    recvRR : ∀ {MP MQ MR}(P : MP → Proto)(Q : MQ → Proto)(R : MR → Proto)
               (p : ⟦ send P ⅋ recv Q ⟧)(q : (m : MR) → ⟦ dual (recv Q) ⅋ R m ⟧)
             → View-∘ (send P) (recv Q) (recv R) p q
    sendR-recvL : ∀ {MP MQ}(P : MP → Proto)(Q : MQ → Proto)R(m : MQ)
                    (p : ⟦ send P ⅋ Q m ⟧)(q : (m : MQ) → ⟦ dual (Q m) ⅋ R ⟧)
                  → View-∘ (send P) (send Q) R (inr m , p) q
    recvR-sendL : ∀ {MP MQ MR}(P : MP → Proto)(Q : MQ → Proto)(R : MR → Proto)
                    (p : (m : MQ) → ⟦ send P ⅋ Q m ⟧)(m : MQ)(q : ⟦ dual (Q m) ⅋ send R ⟧)
                  → View-∘ (send P) (recv Q) (send R) p (inl m , q)
    endL : ∀ Q R
           → (q : ⟦ Q ⟧)(qr : ⟦ dual Q ⅋ R ⟧)
           → View-∘ end Q R q qr
    sendLM : ∀ {MP}(P : MP → Proto)R
               (m : MP)(p : ⟦ P m ⟧)(r : ⟦ R ⟧)
             → View-∘ (send P) end R (m , p) r
    recvL-sendR : ∀ {MP MQ}(P : MP → Proto)(Q : MQ → Proto)
                    (m : MQ)(p : ∀ m → ⟦ send P ⅋ Q m ⟧)(q : ⟦ dual (Q m) ⟧)
                  → View-∘ (send P) (recv Q) end p (m , q)

  view-∘ : ∀ P Q R (pq : ⟦ P ⅋ Q ⟧)(qr : ⟦ dual Q ⅋ R ⟧) → View-∘ P Q R pq qr
  view-∘ P Q R pq qr = view-∘-view (view-⅋ P Q pq) (view-⅋ (dual Q) R qr)
   where
    view-∘-view : ∀ {P Q R}{pq : ⟦ P ⅋ Q ⟧}{qr : ⟦ dual Q ⅋ R ⟧} → View-⅋ P Q pq → View-⅋ (dual Q) R qr → View-∘ P Q R pq qr
    view-∘-view (sendL' _ _ _ _) _                 = sendLL _ _ _ _ _ _
    view-∘-view (recvL' _ _ _)   _                 = recvLL _ _ _ _ _
    view-∘-view (sendR' _ _ _ _) _                 = sendR-recvL _ _ _ _ _ _
    view-∘-view (recvR' _ _ _)   (sendL' ._ _ _ _) = recvR-sendL _ _ _ _ _ _
    view-∘-view (recvR' _ _ _)   (sendR' ._ _ _ _) = recvR-sendR _ _ _ _ _ _ _
    view-∘-view (recvR' _ _ _)   (recvR' ._ _ _)   = recvRR _ _ _ _ _
    view-∘-view (recvR' _ _ _)   (send' ._ _ _)    = recvL-sendR _ _ _ _ _
    view-∘-view (endL _ _)       _                 = endL _ _ _ _
    view-∘-view (send' _ _ _)    _                 = sendLM _ _ _ _ _

  ⅋-apply : ∀ P Q → ⟦ P ⅋ Q ⟧ → ⟦ dual P ⟧ → ⟦ Q ⟧
  ⅋-apply end      Q        s           p       = s
  ⅋-apply (recv P) Q        s           (m , p) = ⅋-apply (P m) Q (s m) p
  ⅋-apply (send P) end      s           p       = _
  ⅋-apply (send P) (recv Q) s           p n     = ⅋-apply (send P) (Q n) (s n) p
  ⅋-apply (send P) (send Q) (inl m , s) p       = ⅋-apply (P m) (send Q) s (p m)
  ⅋-apply (send P) (send Q) (inr m , s) p       = m , ⅋-apply (send P) (Q m) s p

  {-
  -- see dist-⅋-&
  dist-⅋-fst : ∀ P Q R → ⟦ P ⅋ (Q & R) ⟧ → ⟦ P ⅋ Q ⟧
  dist-⅋-fst (recv P) Q R p = λ m → dist-⅋-fst (P m) Q R (p m)
  dist-⅋-fst (send P) Q R p = p `L
  dist-⅋-fst end      Q R p = p `L

  -- see dist-⅋-&
  dist-⅋-snd : ∀ P Q R → ⟦ P ⅋ (Q & R) ⟧ → ⟦ P ⅋ R ⟧
  dist-⅋-snd (recv P) Q R p = λ m → dist-⅋-snd (P m) Q R (p m)
  dist-⅋-snd (send P) Q R p = p `R
  dist-⅋-snd end      Q R p = p `R

  -- see dist-⅋-&
  dist-⅋-× : ∀ P Q R → ⟦ P ⅋ (Q & R) ⟧ → ⟦ P ⅋ Q ⟧ × ⟦ P ⅋ R ⟧
  dist-⅋-× P Q R p = dist-⅋-fst P Q R p , dist-⅋-snd P Q R p

  -- see dist-⅋-&
  dist-⅋-& : ∀ P Q R → ⟦ P ⅋ (Q & R) ⟧ → ⟦ (P ⅋ Q) & (P ⅋ R) ⟧
  dist-⅋-& P Q R p = ×→& (dist-⅋-× P Q R p)

  -- see dist-⅋-&
  factor-,-⅋ : ∀ P Q R → ⟦ P ⅋ Q ⟧ → ⟦ P ⅋ R ⟧ → ⟦ P ⅋ (Q & R) ⟧
  factor-,-⅋ end      Q R pq pr = ×→& (pq , pr)
  factor-,-⅋ (recv P) Q R pq pr = λ m → factor-,-⅋ (P m) Q R (pq m) (pr m)
  factor-,-⅋ (send P) Q R pq pr = [L: pq R: pr ]

  -- see dist-⅋-&
  factor-×-⅋ : ∀ P Q R → ⟦ P ⅋ Q ⟧ × ⟦ P ⅋ R ⟧ → ⟦ P ⅋ (Q & R) ⟧
  factor-×-⅋ P Q R (p , q) = factor-,-⅋ P Q R p q

  -- see dist-⅋-&
  factor-&-⅋ : ∀ P Q R → ⟦ (P ⅋ Q) & (P ⅋ R) ⟧ → ⟦ P ⅋ (Q & R) ⟧
  factor-&-⅋ P Q R p = factor-×-⅋ P Q R (&→× p)

  -- see dist-⅋-&
  module _ {{_ : FunExt}} where
    dist-⅋-fst-factor-&-, : ∀ P Q R (pq : ⟦ P ⅋ Q ⟧)(pr : ⟦ P ⅋ R ⟧)
                            → dist-⅋-fst P Q R (factor-,-⅋ P Q R pq pr) ≡ pq
    dist-⅋-fst-factor-&-, (recv P) Q R pq pr = λ= λ m → dist-⅋-fst-factor-&-, (P m) Q R (pq m) (pr m)
    dist-⅋-fst-factor-&-, (send P) Q R pq pr = refl
    dist-⅋-fst-factor-&-, end      Q R pq pr = refl

    dist-⅋-snd-factor-&-, : ∀ P Q R (pq : ⟦ P ⅋ Q ⟧)(pr : ⟦ P ⅋ R ⟧)
                            → dist-⅋-snd P Q R (factor-,-⅋ P Q R pq pr) ≡ pr
    dist-⅋-snd-factor-&-, (recv P) Q R pq pr = λ= λ m → dist-⅋-snd-factor-&-, (P m) Q R (pq m) (pr m)
    dist-⅋-snd-factor-&-, (send P) Q R pq pr = refl
    dist-⅋-snd-factor-&-, end      Q R pq pr = refl

    factor-×-⅋-linv-dist-⅋-× : ∀ P Q R → (factor-×-⅋ P Q R) LeftInverseOf (dist-⅋-× P Q R)
    factor-×-⅋-linv-dist-⅋-× (recv P) Q R p = λ= λ m → factor-×-⅋-linv-dist-⅋-× (P m) Q R (p m)
    factor-×-⅋-linv-dist-⅋-× (send P) Q R p = λ= λ { `L → refl ; `R → refl }
    factor-×-⅋-linv-dist-⅋-× end      Q R p = λ= λ { `L → refl ; `R → refl }

    module _ P Q R where
        factor-×-⅋-rinv-dist-⅋-× : (factor-×-⅋ P Q R) RightInverseOf (dist-⅋-× P Q R)
        factor-×-⅋-rinv-dist-⅋-× (x , y) = pair×= (dist-⅋-fst-factor-&-, P Q R x y) (dist-⅋-snd-factor-&-, P Q R x y)

        dist-⅋-×-≃ : ⟦ P ⅋ (Q & R) ⟧ ≃ (⟦ P ⅋ Q ⟧ × ⟦ P ⅋ R ⟧)
        dist-⅋-×-≃ = dist-⅋-× P Q R
                   , record { linv = factor-×-⅋ P Q R; is-linv = factor-×-⅋-linv-dist-⅋-× P Q R
                            ; rinv = factor-×-⅋ P Q R; is-rinv = factor-×-⅋-rinv-dist-⅋-× }

        dist-⅋-&-≃ : ⟦ P ⅋ (Q & R) ⟧ ≃ ⟦ (P ⅋ Q) & (P ⅋ R) ⟧
        dist-⅋-&-≃ = dist-⅋-×-≃ ≃-∙ ≃-! &≃×
  -}

module _ {{_ : FunExt}}{{_ : UA}} where
  ⊗-pair : ∀ {P Q} → ⟦ P ⟧ → ⟦ Q ⟧ → ⟦ P ⊗ Q ⟧
  ⊗-pair {end}    {Q}      p q       = q
  ⊗-pair {send P} {Q}      (m , p) q = m , ⊗-pair {P m} p q
  ⊗-pair {recv P} {end}    p end     = p
  ⊗-pair {recv P} {send Q} p (m , q) = m , ⊗-pair {recv P} {Q m} p q
  ⊗-pair {recv P} {recv Q} p q       = [inl: (λ m → ⊗-pair {P m}    {recv Q} (p m) q)
                                       ,inr: (λ n → ⊗-pair {recv P} {Q n}    p     (q n)) ]

  ⊗-fst : ∀ P Q → ⟦ P ⊗ Q ⟧ → ⟦ P ⟧
  ⊗-fst end      Q        pq       = _
  ⊗-fst (send P) Q        (m , pq) = m , ⊗-fst (P m) Q pq
  ⊗-fst (recv P) end      pq       = pq
  ⊗-fst (recv P) (send Q) (_ , pq) = ⊗-fst (recv P) (Q _) pq
  ⊗-fst (recv P) (recv Q) pq       = λ m → ⊗-fst (P m) (recv Q) (pq (inl m))

  ⊗-snd : ∀ P Q → ⟦ P ⊗ Q ⟧ → ⟦ Q ⟧
  ⊗-snd end      Q        pq       = pq
  ⊗-snd (send P) Q        (_ , pq) = ⊗-snd (P _) Q pq
  ⊗-snd (recv P) end      pq       = end
  ⊗-snd (recv P) (send Q) (m , pq) = m , ⊗-snd (recv P) (Q m) pq
  ⊗-snd (recv P) (recv Q) pq       = λ m → ⊗-snd (recv P) (Q m) (pq (inr m))

  ⊗-pair-fst : ∀ P Q (p : ⟦ P ⟧)(q : ⟦ Q ⟧) → ⊗-fst P Q (⊗-pair {P} {Q} p q) ≡ p
  ⊗-pair-fst end      Q        p q       = refl
  ⊗-pair-fst (send P) Q        (m , p) q = pair= refl (⊗-pair-fst (P m) Q p q)
  ⊗-pair-fst (recv P) end      p q       = refl
  ⊗-pair-fst (recv P) (send Q) p (m , q) = ⊗-pair-fst (recv P) (Q m) p q
  ⊗-pair-fst (recv P) (recv Q) p q       = λ= λ m → ⊗-pair-fst (P m) (recv Q) (p m) q

  ⊗-pair-snd : ∀ P Q (p : ⟦ P ⟧)(q : ⟦ Q ⟧) → ⊗-snd P Q (⊗-pair {P} {Q} p q) ≡ q
  ⊗-pair-snd end      Q        p q       = refl
  ⊗-pair-snd (send P) Q        (m , p) q = ⊗-pair-snd (P m) Q p q
  ⊗-pair-snd (recv P) end      p q       = refl
  ⊗-pair-snd (recv P) (send Q) p (m , q) = pair= refl (⊗-pair-snd (recv P) (Q m) p q)
  ⊗-pair-snd (recv P) (recv Q) p q       = λ= λ m → ⊗-pair-snd (recv P) (Q m) p (q m)

  module _ P Q where
    ⊗→× : ⟦ P ⊗ Q ⟧ → ⟦ P ⟧ × ⟦ Q ⟧
    ⊗→× pq = ⊗-fst P Q pq , ⊗-snd P Q pq

    ×→⊗ : ⟦ P ⟧ × ⟦ Q ⟧ → ⟦ P ⊗ Q ⟧
    ×→⊗ (p , q) = ⊗-pair {P} {Q} p q

    ×→⊗→× : ×→⊗ RightInverseOf ⊗→×
    ×→⊗→× = λ { (x , y) → pair×= (⊗-pair-fst P Q x y) (⊗-pair-snd P Q x y) }

    ⊗→×-has-rinv : Rinv ⊗→×
    ⊗→×-has-rinv = record { rinv = ×→⊗ ; is-rinv = ×→⊗→× }

  {- WRONG
  ⊗→×→⊗ : (×→⊗ P Q) LeftInverseOf (⊗→× P Q)
  ⊗≃×   : ⟦ P ⊗ Q ⟧ ≃ ⟦ P ⟧ × ⟦ Q ⟧
  ⟦⊗⟧≡× : P ⟦⊗⟧ Q ≡ (⟦ P ⟧ × ⟦ Q ⟧)
  -}

  -o-apply : ∀ {P Q} → ⟦ dual P ⅋ Q ⟧ → ⟦ P ⟧ → ⟦ Q ⟧
  -o-apply {P} {Q} pq p = ⅋-apply (dual P) Q pq (subst ⟦_⟧ (≡.sym (≡ᴾ-sound (dual-involutive P))) p)

  o-o-apply : ∀ P Q → ⟦ P o-o Q ⟧ → ⟦ P ⟧ → ⟦ Q ⟧
  o-o-apply P Q Po-oQ p = -o-apply {P} {Q} (⊗-fst (P -o Q) (Q -o P) Po-oQ) p

  o-o-comm : ∀ P Q → ⟦ P o-o Q ⟧ ≡ ⟦ Q o-o P ⟧
  o-o-comm P Q = ⊗-comm (dual P ⅋ Q) (dual Q ⅋ P)

  -- left-biased “strategy”
  par : ∀ P Q → ⟦ P ⟧ → ⟦ Q ⟧ → ⟦ P ⅋ Q ⟧
  par (recv P) Q p       q = λ m → par (P m) Q (p m) q
  par (send P) Q (m , p) q = ⅋-sendL Q m (par (P m) Q p q)
  par end      Q end     q = q

  ⅋-∘ : ∀ P Q R → ⟦ P ⅋ Q ⟧ → ⟦ dual Q ⅋ R ⟧ → ⟦ P ⅋ R ⟧
  ⅋-∘ P Q R pq qr = ⅋-∘-view (view-∘ P Q R pq qr)
   where
    ⅋-∘-view : ∀ {P Q R}{pq : ⟦ P ⅋ Q ⟧}{qr : ⟦ dual Q ⅋ R ⟧} → View-∘ P Q R pq qr → ⟦ P ⅋ R ⟧
    ⅋-∘-view (sendLL P Q R m p qr)          = ⅋-sendL R m (⅋-∘ (P m) (send Q) R p qr)
    ⅋-∘-view (recvLL P Q R p qr)            = λ m → ⅋-∘ (P m) Q R (p m) qr
    ⅋-∘-view (recvR-sendR ioP P Q R m pq q) = ⅋-sendR (com ioP P) m (⅋-∘ (com ioP P) (recv Q) (R m) pq q)
    ⅋-∘-view (recvRR P Q R pq q)            = λ m → ⅋-∘ (send P) (recv Q) (R m) pq (q m)
    ⅋-∘-view (sendR-recvL P Q R m p q)      = ⅋-∘ (send P) (Q m) R p (q m)
    ⅋-∘-view (recvR-sendL P Q R p m q)      = ⅋-∘ (send P) (Q m) (send R) (p m) q
    ⅋-∘-view (endL Q R pq qr)               = -o-apply {Q} {R} qr pq
    ⅋-∘-view (sendLM P R m pq qr)           = ⅋-sendL R m (par (P m) R pq qr)
    ⅋-∘-view (recvL-sendR P Q m pq qr)      = ⅋-∘ (send P) (Q m) end (pq m) (coe! (ap ⟦_⟧ (⅋-endR (dual (Q m)))) qr)

    {-
  mutual
    ⅋-comm : ∀ P Q → ⟦ P ⅋ Q ⟧ → ⟦ Q ⅋ P ⟧
    ⅋-comm P Q p = ⅋-comm-view (view-⅋ P Q p)

    ⅋-comm-view : ∀ {P Q} {pq : ⟦ P ⅋ Q ⟧} → View-⅋ P Q pq → ⟦ Q ⅋ P ⟧
    ⅋-comm-view (sendL' P Q m p) = ⅋-sendR (send Q) m (⅋-comm (P m) (send Q) p)
    ⅋-comm-view (sendR' P Q n p) = inl n , ⅋-comm (send P) (Q n) p
    ⅋-comm-view (recvL' P Q pq)  = ⅋-recvR Q P λ m → ⅋-comm (P m) Q (pq m)
    ⅋-comm-view (recvR' P Q pq)  = λ n → ⅋-comm (send P) (Q n) (pq n)
    ⅋-comm-view (endL Q pq)      = ⅋-rend! Q pq
    ⅋-comm-view (send P m pq)    = m , pq
  -}

  switchL' : ∀ P Q R (pq : ⟦ P ⅋ Q ⟧) (r : ⟦ R ⟧) → ⟦ P ⅋ (Q ⊗ R) ⟧
  switchL' end      Q        R        q  r = ⊗-pair {Q} {R} q r
  switchL' (send P) end      R        p  r = par (send P) R p r
  switchL' (send P) (send Q) R        (inl m , pq) r = inl m , switchL' (P m) (send Q) R pq r
  switchL' (send P) (send Q) R        (inr m , pq) r = inr m , switchL' (send P) (Q m) R pq r
  switchL' (send P) (recv Q) end      pq r = pq
  switchL' (send P) (recv Q) (send R) pq (m , r) = inr m , switchL' (send P) (recv Q) (R m) pq r
  switchL' (send P) (recv Q) (recv R) pq r (inl m) = switchL' (send P) (Q m) (recv R) (pq m) r
  switchL' (send P) (recv Q) (recv R) pq r (inr m) = switchL' (send P) (recv Q) (R m) pq (r m)
  switchL' (recv P) Q R pq r = λ m → switchL' (P m) Q R (pq m) r

  switchL : ∀ P Q R → ⟦ (P ⅋ Q) ⊗ R ⟧ → ⟦ P ⅋ (Q ⊗ R) ⟧
  switchL P Q R pqr = switchL' P Q R (⊗-fst (P ⅋ Q) R pqr) (⊗-snd (P ⅋ Q) R pqr)

  -- multiplicative mix (left-biased)
  mmix : ∀ P Q → ⟦ P ⊗ Q ⟧ → ⟦ P ⅋ Q ⟧
  mmix P Q pq = par P Q (⊗-fst P Q pq) (⊗-snd P Q pq)

  -- additive mix (left-biased)
  amix : ∀ P Q → ⟦ P & Q ⟧ → ⟦ P ⊕ Q ⟧
  amix P Q pq = (`L , pq `L)

{-
A `⊗ B 'times', context chooses how A and B are used
A `⅋ B 'par', "we" chooses how A and B are used
A `⊕ B 'plus', select from A or B
A `& B 'with', offer choice of A or B
`! A   'of course!', server accept
`? A   'why not?', client request
`1     unit for `⊗
`⊥     unit for `⅋
`0     unit for `⊕
`⊤     unit for `&
-}
data CLL : ★ where
  `1 `⊤ `0 `⊥ : CLL
  _`⊗_ _`⅋_ _`⊕_ _`&_ : (A B : CLL) → CLL
  -- `!_ `?_ : (A : CLL) → CLL

_⊥ : CLL → CLL
`1 ⊥ = `⊥
`⊥ ⊥ = `1
`0 ⊥ = `⊤
`⊤ ⊥ = `0
(A `⊗ B)⊥ = A ⊥ `⅋ B ⊥
(A `⅋ B)⊥ = A ⊥ `⊗ B ⊥
(A `⊕ B)⊥ = A ⊥ `& B ⊥
(A `& B)⊥ = A ⊥ `⊕ B ⊥
{-
(`! A)⊥ = `?(A ⊥)
(`? A)⊥ = `!(A ⊥)
-}

CLL-proto : CLL → Proto
CLL-proto `1       = end  -- TODO
CLL-proto `⊥       = end  -- TODO
CLL-proto `0       = send′ 𝟘 end -- Alt: send λ()
CLL-proto `⊤       = recv′ 𝟘 end -- Alt: recv λ()
CLL-proto (A `⊗ B) = CLL-proto A ⊗ CLL-proto B
CLL-proto (A `⅋ B) = CLL-proto A ⅋ CLL-proto B
CLL-proto (A `⊕ B) = CLL-proto A ⊕ CLL-proto B
CLL-proto (A `& B) = CLL-proto A & CLL-proto B

{- The point of this could be to devise a particular equivalence
   relation for processes. It could properly deal with ⅋. -}

module Commitment {Secret Guess : ★} {R : ..(_ : Secret) → Guess → ★} where
    Commit : Proto
    Commit = send☐ λ (s : Secret) →
             recv  λ (g : Guess)  →
             send  λ (_ : S⟨ s ⟩) →
             end

    commit : (s : Secret)  → ⟦ Commit ⟧
    commit s = [ s ] , λ g → S[ s ] , _

    decommit : (g : Guess) → ⟦ dual Commit ⟧
    decommit g = λ { [ m ] → g , _ }

open import Relation.Nullary
open import Relation.Nullary.Decidable
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
        Prover = send λ (gʳ : G)  → -- commitment
                 recv λ (c  : ℤq) → -- challenge
                 send λ (s  : ℤq) → -- response
                 end

        Verifier : Proto
        Verifier = dual Prover

        -- he is honest but its type does not say it
        prover : (x r : ℤq) → ⟦ Prover ⟧
        prover x r = (g ^ r) , λ c → (r + (c * x)) , _

        Honest-Prover : ..(x : ℤq) (y : S⟨ g ^ x ⟩) → Proto
        Honest-Prover x y
          = send☐ λ (r  : ℤq)                → -- ideal commitment
            send  λ (gʳ : S⟨ g ^ r ⟩)        → -- real  commitment
            recv  λ (c  : ℤq)                → -- challenge
            send  λ (s  : S⟨ r + (c * x) ⟩)  → -- response
            recv  λ (_  : Dec ((g ^ unS s) ≡ (unS gʳ · (unS y ^ c)))) →
            end

        Honest-Verifier : ..(x : ℤq) (y : S⟨ g ^ x ⟩) → Proto
        Honest-Verifier x y = dual (Honest-Prover x y)

        honest-prover : (x r : ℤq) → ⟦ Honest-Prover x S[ g ^ x ] ⟧
        honest-prover x r = [ r ] , S[ g ^ r ] , λ c → S[ r + (c * x) ] , _
        -- agsy can do it

        honest-verifier : ..(x : ℤq) (y : S⟨ g ^ x ⟩) (c : ℤq) → ⟦ Honest-Verifier x y ⟧
        honest-verifier x y c = λ { [ r ] → λ gʳ → c , λ s → (g ^ unS s) ≟ (unS gʳ · (unS y ^ c)) , _ }

        honest-prover→prover : ..(x : ℤq)(y : S⟨ g ^ x ⟩) → ⟦ Honest-Prover x y ⟧ → ⟦ Prover ⟧
        honest-prover→prover x y ([ r ] , gʳ , p) = unS gʳ , λ c → case p c of λ { (s , _) → unS s , _ }

        {-
        sim-honest-prover : ..(x : ℤq)(y : S⟨ g ^ x ⟩) → Sim (dual (Honest-Prover x y)) Prover
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
