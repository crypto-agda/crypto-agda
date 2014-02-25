
-- {-# OPTIONS --without-K #-}
open import Coinduction
open import Function.NP
open import Type
open import Level.NP
open import Data.Product.NP renaming (map to ×-map; proj₁ to fst; proj₂ to snd)
open import Data.Zero
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr; [_,_] to [inl:_,inr:_]) hiding ([_,_]′)
open import Data.One hiding (_≟_)
open import Data.Two hiding (_≟_)
open import Data.Nat hiding (_⊔_)
open Data.Two.Indexed

open import Relation.Binary
import Function.Inverse.NP as Inv
open Inv using (_↔_; {-_∘_; sym; id;-} inverses; module Inverse) renaming (_$₁_ to to; _$₂_ to from)
open import Function.Related.TypeIsomorphisms.NP hiding (Σ-assoc)
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_; cong; !_; _∙_; refl; subst; cong₂; J; ap; coe; coe!; J-orig)

module Control.Protocol.Choreography where

postulate
    FunExt : ★
    λ= : ∀ {a}{b}{A : ★_ a}{B : A → ★_ b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → {{fe : FunExt}} → f ≡ g

-- Contractible
module _ {a}(A : ★_ a) where
    Is-contr : ★_ a
    Is-contr = Σ A λ x → ∀ y → x ≡ y

module _ {a}{b}{A : ★_ a}{B : A → ★_ b} where
    pair= : ∀ {x y : Σ A B} → (p : fst x ≡ fst y) → subst B p (snd x) ≡ snd y → x ≡ y
    pair= refl = cong (_,_ _)
    snd= : ∀ {x : A} {y y' : B x} → y ≡ y' → _≡_ {A = Σ A B} (x , y) (x , y')
    snd= = pair= refl
module _ {a}{b}{A : ★_ a}{B : ★_ b} where
    pair×= : ∀ {x x' : A}(p : x ≡ x')
               {y y' : B}(q : y ≡ y')
             → (x , y) ≡ (x' , y')
    pair×= refl q = snd= q

module _ {a}(A : ★_ a){b}{B₀ B₁ : A → ★_ b}(B : (x : A) → B₀ x ≡ B₁ x){{_ : FunExt}} where
    Σ=′ : Σ A B₀ ≡ Σ A B₁
    Σ=′ = cong (Σ A) (λ= B)

    Π=′ : Π A B₀ ≡ Π A B₁
    Π=′ = cong (Π A) (λ= B)

module _ {{_ : FunExt}} where
    Σ= : ∀ {a}{A₀ A₁ : ★_ a}{b}{B₀ : A₀ → ★_ b}{B₁ : A₁ → ★_ b}
           (A : A₀ ≡ A₁)(B : (x : A₀) → B₀ x ≡ B₁ (coe A x))
         → Σ A₀ B₀ ≡ Σ A₁ B₁
    Σ= refl B = Σ=′ _ B

    Π= : ∀ {a}{A₀ A₁ : ★_ a}{b}{B₀ : A₀ → ★_ b}{B₁ : A₁ → ★_ b}
           (A : A₀ ≡ A₁)(B : (x : A₀) → B₀ x ≡ B₁ (coe A x))
         → Π A₀ B₀ ≡ Π A₁ B₁
    Π= refl B = Π=′ _ B

module _ {a}{A₀ A₁ : ★_ a}{b}{B₀ B₁ : ★_ b}(A : A₀ ≡ A₁)(B : B₀ ≡ B₁) where
    ×= : (A₀ × B₀) ≡ (A₁ × B₁)
    ×= = cong₂ _×_ A B

    ⊎= : (A₀ ⊎ B₀) ≡ (A₁ ⊎ B₁)
    ⊎= = cong₂ _⊎_ A B

module Equivalences where

  module _ {a b}{A : ★_ a}{B : ★_ b} where
    _LeftInverseOf_ : (B → A) → (A → B) → ★_ a
    linv LeftInverseOf f = ∀ x → linv (f x) ≡ x

    _RightInverseOf_ : (B → A) → (A → B) → ★_ b
    rinv RightInverseOf f = ∀ x → f (rinv x) ≡ x

    record Linv (f : A → B) : ★_(a ⊔ b) where
      field
        linv : B → A
        is-linv : ∀ x → linv (f x) ≡ x

    record Rinv (f : A → B) : ★_(a ⊔ b) where
      field
        rinv : B → A
        is-rinv : ∀ x → f (rinv x) ≡ x

    record Is-equiv (f : A → B) : ★_(a ⊔ b) where
      field
        linv : B → A
        is-linv : ∀ x → linv (f x) ≡ x
        rinv : B → A
        is-rinv : ∀ x → f (rinv x) ≡ x

      injective : ∀ {x y} → f x ≡ f y → x ≡ y
      injective {x} {y} p = !(is-linv x) ∙ ap linv p ∙ is-linv y

      surjective : ∀ y → ∃ λ x → f x ≡ y
      surjective y = rinv y , is-rinv y

  module _ {a b}{A : ★_ a}{B : ★_ b}{f : A → B}(fᴱ : Is-equiv f) where
      open Is-equiv fᴱ
      inv : B → A
      inv = linv ∘ f ∘ rinv

      inv-is-equiv : Is-equiv inv
      inv-is-equiv = record { linv = f
                         ; is-linv = λ x → ap f (is-linv (rinv x)) ∙ is-rinv x
                         ; rinv = f
                         ; is-rinv = λ x → ap linv (is-rinv (f x)) ∙ is-linv x }

  module _ {a}{A : ★_ a}{f : A → A}(f-inv : f LeftInverseOf f) where
      self-inv-is-equiv : Is-equiv f
      self-inv-is-equiv = record { linv = f ; is-linv = f-inv ; rinv = f ; is-rinv = f-inv }

  module _ {a}{A : ★_ a} where
    idᴱ : Is-equiv {A = A} id
    idᴱ = self-inv-is-equiv λ _ → refl

  module _ {a b c}{A : ★_ a}{B : ★_ b}{C : ★_ c}{g : B → C}{f : A → B} where
    _∘ᴱ_ : Is-equiv g → Is-equiv f → Is-equiv (g ∘ f)
    gᴱ ∘ᴱ fᴱ = record { linv = F.linv ∘ G.linv ; is-linv = λ x → ap F.linv (G.is-linv (f x)) ∙ F.is-linv x
                      ; rinv = F.rinv ∘ G.rinv ; is-rinv = λ x → ap g (F.is-rinv _) ∙ G.is-rinv x }
      where
        module G = Is-equiv gᴱ
        module F = Is-equiv fᴱ

  module _ {a b} where
    infix 4 _≃_
    _≃_ : ★_ a → ★_ b → ★_(a ⊔ b)
    A ≃ B = Σ (A → B) Is-equiv

  module _ {a b}{A : ★_ a}{B : ★_ b} where
    –> : (e : A ≃ B) → (A → B)
    –> e = fst e

    <– : (e : A ≃ B) → (B → A)
    <– e = Is-equiv.linv (snd e)

    <–-inv-l : (e : A ≃ B) (a : A)
              → (<– e (–> e a) ≡ a)
    <–-inv-l e a = Is-equiv.is-linv (snd e) a

    {-
    <–-inv-r : (e : A ≃ B) (b : B)
                → (–> e (<– e b) ≡ b)
    <–-inv-r e b = Is-equiv.is-rinv (snd e) b
    -}

    -- Equivalences are "injective"
    equiv-inj : (e : A ≃ B) {x y : A}
                → (–> e x ≡ –> e y → x ≡ y)
    equiv-inj e {x} {y} p = ! (<–-inv-l e x) ∙ ap (<– e) p ∙ <–-inv-l e y

  module _ {a b}{A : ★_ a}{B : ★_ b}
           (f : A → B) (g : B → A)
           (f-g : (y : B) → f (g y) ≡ y)
           (g-f : (x : A) → g (f x) ≡ x) where
    is-equiv : Is-equiv f
    is-equiv = record { linv = g ; is-linv = g-f ; rinv = g ; is-rinv = f-g }

    equiv : A ≃ B
    equiv = f , is-equiv

  module _ {ℓ} where
    ≃-refl : Reflexive (_≃_ {ℓ})
    ≃-refl = _ , idᴱ

    ≃-sym : Symmetric (_≃_ {ℓ})
    ≃-sym (_ , fᴱ) = _ , inv-is-equiv fᴱ

    ≃-trans : Transitive (_≃_ {ℓ})
    ≃-trans (_ , p) (_ , q) = _ , q ∘ᴱ p

    ≃-! = ≃-sym
    _≃-∙_ = ≃-trans

  module _ {a}{A : ★_ a} where
    Paths : ★_ a
    Paths = Σ A λ x → Σ A λ y → x ≡ y

    id-path : A → Paths
    id-path x = x , x , refl

    fst-rinv-id-path : ∀ p → id-path (fst p) ≡ p
    fst-rinv-id-path (x , y , p) = snd= (pair= p (J (λ {y} p → subst (_≡_ x) p refl ≡ p) refl p))

    id-path-is-equiv : Is-equiv id-path
    id-path-is-equiv = record { linv = fst
                              ; is-linv = λ x → refl
                              ; rinv = fst
                              ; is-rinv = fst-rinv-id-path }

    ≃-Paths : A ≃ Paths
    ≃-Paths = id-path , id-path-is-equiv

  module _ {a b}{A : ★_ a}{B : ★_ b}(f : A → B) where
    hfiber : (y : B) → ★_(a ⊔ b)
    hfiber y = Σ A λ x → f x ≡ y

    Is-equiv-alt : ★_(a ⊔ b)
    Is-equiv-alt = (y : B) → Is-contr (hfiber y)

  module Is-contr-to-Is-equiv {a}{A : ★_ a}(A-contr : Is-contr A) where
    const-is-equiv : Is-equiv (λ (_ : 𝟙) → fst A-contr)
    const-is-equiv = record { linv = _ ; is-linv = λ _ → refl ; rinv = _ ; is-rinv = snd A-contr }
    𝟙≃ : 𝟙 ≃ A
    𝟙≃ = _ , const-is-equiv
  module Is-equiv-to-Is-contr {a}{A : ★_ a}(f : 𝟙 → A)(f-is-equiv : Is-equiv f) where
    open Is-equiv f-is-equiv
    A-contr : Is-contr A
    A-contr = f _ , is-rinv

  module _ {a}{A : ★_ a}{b}{B : ★_ b} where
    iso-to-equiv : (A ↔ B) → (A ≃ B)
    iso-to-equiv iso = to iso , record { linv = from iso ; is-linv = Inverse.left-inverse-of iso
                                       ; rinv = from iso ; is-rinv = Inverse.right-inverse-of iso }

    equiv-to-iso : (A ≃ B) → (A ↔ B)
    equiv-to-iso (f , f-is-equiv) = inverses f (fᴱ.linv ∘ f ∘ fᴱ.rinv)
                                             (λ x → ap fᴱ.linv (fᴱ.is-rinv (f x)) ∙ fᴱ.is-linv x)
                                             (λ x → ap f (fᴱ.is-linv (fᴱ.rinv x)) ∙ fᴱ.is-rinv x)
      where module fᴱ = Is-equiv f-is-equiv

    {-
    iso-to-equiv-to-iso : (iso : A ↔ B) → equiv-to-iso (iso-to-equiv iso) ≡ iso
    iso-to-equiv-to-iso iso = {!!}
      where module Iso = Inverse iso

    iso-to-equiv-is-equiv : Is-equiv iso-to-equiv
    iso-to-equiv-is-equiv = record { linv = equiv-to-iso ; is-linv = {!!} ; rinv = {!!} ; is-rinv = {!!} }
    -}
open Equivalences

module _ {ℓ}{A : ★_ ℓ} where
    coe!-inv-r : ∀ {B}(p : A ≡ B) y → coe p (coe! p y) ≡ y
    coe!-inv-r refl y = refl

    coe!-inv-l : ∀ {B}(p : A ≡ B) x → coe! p (coe p x) ≡ x
    coe!-inv-l refl x = refl

    coe-equiv : ∀ {B} → A ≡ B → A ≃ B
    coe-equiv p = equiv (coe p) (coe! p) (coe!-inv-r p) (coe!-inv-l p)

postulate
  UA : ★
module _ {ℓ}{A B : ★_ ℓ}{{_ : UA}} where
  postulate
    ua : (A ≃ B) → (A ≡ B)
    coe-equiv-β : (e : A ≃ B) → coe-equiv (ua e) ≡ e
    ua-η : (p : A ≡ B) → ua (coe-equiv p) ≡ p

  ua-equiv : (A ≃ B) ≃ (A ≡ B)
  ua-equiv = equiv ua coe-equiv ua-η coe-equiv-β

  coe-β : (e : A ≃ B) (a : A) → coe (ua e) a ≡ –> e a
  coe-β e a = ap (λ e → –> e a) (coe-equiv-β e)

module _ {{_ : UA}}{{_ : FunExt}}{a}{A₀ A₁ : ★_ a}{b}{B₀ : A₀ → ★_ b}{B₁ : A₁ → ★_ b} where
    Σ≃ : (A : A₀ ≃ A₁)(B : (x : A₀) → B₀ x ≡ B₁ (–> A x))
         → Σ A₀ B₀ ≡ Σ A₁ B₁
    Σ≃ A B = Σ= (ua A) λ x → B x ∙ ap B₁ (! coe-β A x)

    Π≃ : (A : A₀ ≃ A₁)(B : (x : A₀) → B₀ x ≡ B₁ (–> A x))
         → Π A₀ B₀ ≡ Π A₁ B₁
    Π≃ A B = Π= (ua A) λ x → B x ∙ ap B₁ (! coe-β A x)

module _ {{_ : UA}}{{_ : FunExt}}{A : ★}{B C : A → ★} where
    Σ⊎-split : (Σ A (λ x → B x ⊎ C x)) ≡ (Σ A B ⊎ Σ A C)
    Σ⊎-split = ua (equiv (λ { (x , inl y) → inl (x , y)
                            ; (x , inr y) → inr (x , y) })
                         (λ { (inl (x , y)) → x , inl y
                            ; (inr (x , y)) → x , inr y })
                         (λ { (inl (x , y)) → refl
                            ; (inr (x , y)) → refl })
                         (λ { (x , inl y) → refl
                            ; (x , inr y) → refl }))

module _ {{_ : UA}}{{_ : FunExt}}{A B : ★}{C : A → ★}{D : B → ★} where
    dist-⊎-Σ : (Σ (A ⊎ B) [inl: C ,inr: D ]) ≡ (Σ A C ⊎ Σ B D)
    dist-⊎-Σ = ua (iso-to-equiv Σ⊎-distrib)
    dist-×-Π : (Π (A ⊎ B) [inl: C ,inr: D ]) ≡ (Π A C × Π B D)
    dist-×-Π = ua (iso-to-equiv (Π×-distrib (λ fg → λ= fg)))

module _ {A : ★}{B : A → ★}{C : (x : A) → B x → ★} where
    Σ-assoc-equiv : (Σ A (λ x → Σ (B x) (C x))) ≃ (Σ (Σ A B) (uncurry C))
    Σ-assoc-equiv = equiv (λ x → (fst x , fst (snd x)) , snd (snd x))
                          (λ x → fst (fst x) , snd (fst x) , snd x)
                          (λ y → refl)
                          (λ y → refl)

    Σ-assoc : {{_ : UA}} → (Σ A (λ x → Σ (B x) (C x))) ≡ (Σ (Σ A B) (uncurry C))
    Σ-assoc = ua Σ-assoc-equiv

module _ {A B : ★} where
    ×-comm-equiv : (A × B) ≃ (B × A)
    ×-comm-equiv = equiv swap swap (λ y → refl) (λ x → refl)

    ×-comm : {{_ : UA}} → (A × B) ≡ (B × A)
    ×-comm = ua ×-comm-equiv

    ⊎-comm-equiv : (A ⊎ B) ≃ (B ⊎ A)
    ⊎-comm-equiv = equiv [inl: inr ,inr: inl ]
                         [inl: inr ,inr: inl ]
                         [inl: (λ x → refl) ,inr: (λ x → refl) ]
                         [inl: (λ x → refl) ,inr: (λ x → refl) ]

    ⊎-comm : {{_ : UA}} → (A ⊎ B) ≡ (B ⊎ A)
    ⊎-comm = ua ⊎-comm-equiv

module _ {A B : ★}{C : A → B → ★} where
    ΠΠ-comm-equiv : ((x : A)(y : B) → C x y) ≃ ((y : B)(x : A) → C x y)
    ΠΠ-comm-equiv = equiv flip flip (λ _ → refl) (λ _ → refl)

    ΠΠ-comm : {{_ : UA}} → ((x : A)(y : B) → C x y) ≡ ((y : B)(x : A) → C x y)
    ΠΠ-comm = ua ΠΠ-comm-equiv

    ΣΣ-comm-equiv : (Σ A λ x → Σ B λ y → C x y) ≃ (Σ B λ y → Σ A λ x → C x y)
    ΣΣ-comm-equiv = equiv (λ { (x , y , z) → y , x , z })
                          (λ { (x , y , z) → y , x , z })
                          (λ _ → refl)
                          (λ _ → refl)

    ΣΣ-comm : {{_ : UA}} → (Σ A λ x → Σ B λ y → C x y) ≡ (Σ B λ y → Σ A λ x → C x y)
    ΣΣ-comm = ua ΣΣ-comm-equiv

module _ {A B C : ★} where
    ×-assoc : {{_ : UA}} → (A × (B × C)) ≡ ((A × B) × C)
    ×-assoc = Σ-assoc

    ⊎-assoc-equiv : (A ⊎ (B ⊎ C)) ≃ ((A ⊎ B) ⊎ C)
    ⊎-assoc-equiv = equiv [inl: inl ∘ inl ,inr: [inl: inl ∘ inr ,inr: inr ] ]
                          [inl: [inl: inl ,inr: inr ∘ inl ] ,inr: inr ∘ inr ]
                          [inl: [inl: (λ x → refl) ,inr: (λ x → refl) ] ,inr: (λ x → refl) ]
                          [inl: (λ x → refl) ,inr: [inl: (λ x → refl) ,inr: (λ x → refl) ] ]

    ⊎-assoc : {{_ : UA}} → (A ⊎ (B ⊎ C)) ≡ ((A ⊎ B) ⊎ C)
    ⊎-assoc = ua ⊎-assoc-equiv

module _ {{_ : FunExt}}(F G : 𝟘 → ★) where
    Π𝟘-uniq : Π 𝟘 F ≡ Π 𝟘 G
    Π𝟘-uniq = Π=′ 𝟘 (λ())

Π· : ∀ {a b}(A : ★_ a) → (B : ..(_ : A) → ★_ b) → ★_ (a ⊔ b)
Π· A B = ..(x : A) → B x

data ☐ {a}(A : ★_ a) : ★_ a where
  [_] : ..(x : A) → ☐ A

un☐ : ∀ {a b}{A : ★_ a}{B : ☐ A → ★_ b} → (..(x : A) → B [ x ]) → Π (☐ A) B
un☐ f [ x ] = f x

data _≡☐_ {a} {A : ★_ a} (x : A) : ..(y : A) → ★_ a where
  refl : x ≡☐ x

{-
data S<_> {a} {A : ★_ a} : ..(x : A) → ★_ a where
  S[_] : ∀ x → S< x >

unS : ∀ {a} {A : ★_ a} ..{x : A} → S< x > → A
unS S[ y ] = y
-}

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

dualᴵᴼ-involutive : ∀ io → dualᴵᴼ (dualᴵᴼ io) ≡ io
dualᴵᴼ-involutive In = refl
dualᴵᴼ-involutive Out = refl

dualᴵᴼ-equiv : Is-equiv dualᴵᴼ
dualᴵᴼ-equiv = self-inv-is-equiv dualᴵᴼ-involutive

dualᴵᴼ-inj : ∀ {x y} → dualᴵᴼ x ≡ dualᴵᴼ y → x ≡ y
dualᴵᴼ-inj = Is-equiv.injective dualᴵᴼ-equiv

module UniversalProtocols ℓ {U : ★_(ₛ ℓ)}(U⟦_⟧ : U → ★_ ℓ) where
  data Proto_ : ★_(ₛ ℓ) where
    end : Proto_
    com : (io : InOut){M : U}(P : U⟦ M ⟧ → Proto_) → Proto_

module U★ ℓ = UniversalProtocols ℓ {★_ ℓ} id
open U★

Proto : ★₁
Proto = Proto_ ₀
Proto₀ = Proto
Proto₁ = Proto_ ₁

pattern Πᴾ M P = com In  {M} P
pattern Σᴾ M P = com Out {M} P

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
  ≡-Σ : ∀ {M P Q} (p≡q : (m : M) → P m ≡ᴾ Q m) → View-≡ᴾ (Σᴾ _ P) (Σᴾ _ Q) (com refl p≡q)
  ≡-Π : ∀ {M P Q} (p≡q : (m : M) → P m ≡ᴾ Q m) → View-≡ᴾ (Πᴾ _ P) (Πᴾ _ Q) (com refl p≡q)

view-≡ᴾ : ∀ {P Q} (p≡q : P ≡ᴾ Q) → View-≡ᴾ P Q p≡q
view-≡ᴾ end = end
view-≡ᴾ (com {In}  refl _) = ≡-Π _
view-≡ᴾ (com {Out} refl _) = ≡-Σ _

Π☐ᴾ : (M : ★)(P : ..(_ : M) → Proto) → Proto
Π☐ᴾ M P = Πᴾ (☐ M) (λ { [ m ] → P m })

Σ☐ᴾ : (M : ★)(P : ..(_ : M) → Proto) → Proto
Σ☐ᴾ M P = Σᴾ (☐ M) (λ { [ m ] → P m })

source-of : Proto → Proto
source-of end       = end
source-of (com _ P) = Σᴾ _ λ m → source-of (P m)

{-
dual : Proto → Proto
dual end      = end
dual (Σᴾ M P) = Πᴾ M λ m → dual (P m)
dual (Πᴾ M P) = Σᴾ M λ m → dual (P m)
-}

dual : Proto → Proto
dual end        = end
dual (com io P) = com (dualᴵᴼ io) λ m → dual (P m)

data IsSource : Proto → ★₁ where
  end : IsSource end
  com : ∀ M {P} (PT : ∀ m → IsSource (P m)) → IsSource (Σᴾ M P)

data IsSink : Proto → ★₁ where
  end : IsSink end
  com : ∀ M {P} (PT : ∀ m → IsSink (P m)) → IsSink (Πᴾ M P)

data Proto☐ : Proto → ★₁ where
  end : Proto☐ end
  com : ∀ q M {P} (P☐ : ∀ (m : ☐ M) → Proto☐ (P m)) → Proto☐ (com q P)

record End_ ℓ : ★_ ℓ where
  constructor end

End : ∀ {ℓ} → ★_ ℓ
End = End_ _

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
ℛ⟦ Πᴾ M P ⟧ p q = (m : M) → ℛ⟦ P m ⟧ (p m) (q m)
ℛ⟦ Σᴾ M P ⟧ p q = Σ (fst p ≡ fst q) λ e → ℛ⟦ P (fst q) ⟧ (subst (⟦_⟧ ∘ P) e (snd p)) (snd q)

ℛ⟦_⟧-refl : ∀ {ℓ}(P : Proto_ ℓ) → Reflexive ℛ⟦ P ⟧
ℛ⟦ end    ⟧-refl     = end
ℛ⟦ Πᴾ M P ⟧-refl     = λ m → ℛ⟦ P m ⟧-refl
ℛ⟦ Σᴾ M P ⟧-refl {x} = refl , ℛ⟦ P (fst x) ⟧-refl

ℛ⟦_⟧-sym : ∀ {ℓ}(P : Proto_ ℓ) → Symmetric ℛ⟦ P ⟧
ℛ⟦ end    ⟧-sym p          = end
ℛ⟦ Πᴾ M P ⟧-sym p          = λ m → ℛ⟦ P m ⟧-sym (p m)
ℛ⟦ Σᴾ M P ⟧-sym (refl , q) = refl , ℛ⟦ P _ ⟧-sym q    -- TODO HoTT

ℛ⟦_⟧-trans : ∀ {ℓ}(P : Proto_ ℓ) → Transitive ℛ⟦ P ⟧
ℛ⟦ end    ⟧-trans p          q          = end
ℛ⟦ Πᴾ M P ⟧-trans p          q          = λ m → ℛ⟦ P m ⟧-trans (p m) (q m)
ℛ⟦ Σᴾ M P ⟧-trans (refl , p) (refl , q) = refl , ℛ⟦ P _ ⟧-trans p q    -- TODO HoTT

data ViewProc {ℓ} : ∀ (P : Proto_ ℓ) → ⟦ P ⟧ → ★_(ₛ ℓ) where
  send : ∀ M(P : M → Proto_ ℓ)(m : M)(p : ⟦ P m ⟧) → ViewProc (Σᴾ M P) (m , p)
  recv : ∀ M(P : M → Proto_ ℓ)(p : ((m : M) → ⟦ P m ⟧)) → ViewProc (Πᴾ M P) p
  end  : ViewProc end _

view-proc : ∀ {ℓ} (P : Proto_ ℓ) (p : ⟦ P ⟧) → ViewProc P p
view-proc end      _       = end
view-proc (Πᴾ M P) p       = recv _ _ p
view-proc (Σᴾ M P) (m , p) = send _ _ m p

_×'_ : ★ → Proto → Proto
M ×' P = Σᴾ M λ _ → P

_→'_ : ★ → Proto → Proto
M →' P = Πᴾ M λ _ → P

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

data End? : ★ where
  end continue : End?

End?ᴾ : Proto → Proto
End?ᴾ P = Σᴾ End? λ { end → end ; continue → P }

module _ {A : ★} (Aᴾ : A → Proto) where
    addΣᴾ : Proto → Proto
    addΣᴾ end      = end
    addΣᴾ (Σᴾ M P) = Σᴾ (M ⊎ A) [inl: (λ m → addΣᴾ (P m)) ,inr: Aᴾ ]
    addΣᴾ (Πᴾ M P) = Πᴾ M λ m → addΣᴾ (P m)

    addΠᴾ : Proto → Proto
    addΠᴾ end      = end
    addΠᴾ (Πᴾ M P) = Πᴾ (M ⊎ A) [inl: (λ m → addΠᴾ (P m)) ,inr: Aᴾ ]
    addΠᴾ (Σᴾ M P) = Σᴾ M λ m → addΠᴾ (P m)

module _ {A : ★} (Aᴾ : A → Proto) where
    dual-addΣᴾ : ∀ P → dual (addΣᴾ Aᴾ P) ≡ᴾ addΠᴾ (dual ∘ Aᴾ) (dual P)
    dual-addΣᴾ end      = end
    dual-addΣᴾ (Πᴾ M P) = com refl (λ m → dual-addΣᴾ (P m))
    dual-addΣᴾ (Σᴾ M P) = com refl [inl: (λ m → dual-addΣᴾ (P m))
                                   ,inr: (λ x → ≡ᴾ-refl (dual (Aᴾ x))) ]

data Abort : ★ where abort : Abort

Abortᴾ : Abort → Proto
Abortᴾ _ = end

add-abort : Proto → Proto
add-abort = addΣᴾ Abortᴾ

telecom : ∀ P → ⟦ P ⟧ → ⟦ P ⊥⟧ → Log P
telecom end      _       _       = _
telecom (Πᴾ M P) p       (m , q) = m , telecom (P m) (p m) q
telecom (Σᴾ M P) (m , p) q       = m , telecom (P m) p (q m)

liftᴾ : ∀ a {ℓ} → Proto_ ℓ → Proto_ (a ⊔ ℓ)
liftᴾ a end        = end
liftᴾ a (com io P) = com io λ m → liftᴾ a (P (lower {ℓ = a} m))

lift-proc : ∀ a {ℓ} (P : Proto_ ℓ) → ⟦ P ⟧ → ⟦ liftᴾ a P ⟧
lift-proc a {ℓ} P0 p0 = lift-view (view-proc P0 p0)
  where
    lift-view : ∀ {P : Proto_ ℓ}{p : ⟦ P ⟧} → ViewProc P p → ⟦ liftᴾ a P ⟧
    lift-view (send M P m p) = lift m , lift-proc _ (P m) p
    lift-view (recv M P x)   = λ { (lift m) → lift-proc _ (P m) (x m) }
    lift-view end            = end

module MonomorphicSky (P : Proto₀) where
  Cloud : Proto₀
  Cloud = Πᴾ ⟦ P  ⟧  λ p →
          Πᴾ ⟦ P ⊥⟧  λ p⊥ →
          Σᴾ (Log P) λ log →
          end
  cloud : ⟦ Cloud ⟧
  cloud p p⊥ = telecom P p p⊥ , _

module PolySky where
  Cloud : Proto_ ₁
  Cloud = Πᴾ Proto₀         λ P →
          liftᴾ ₁ (MonomorphicSky.Cloud P)
  cloud : ⟦ Cloud ⟧
  cloud P = lift-proc ₁ (MonomorphicSky.Cloud P) (MonomorphicSky.cloud P)

module PolySky' where
  Cloud : Proto_ ₁
  Cloud = Πᴾ Proto₀         λ P →
         Πᴾ (Lift ⟦ P  ⟧)  λ p →
         Πᴾ (Lift ⟦ P ⊥⟧)  λ p⊥ →
         Σᴾ (Lift (Log P)) λ log →
         end
  cloud : ⟦ Cloud ⟧
  cloud P (lift p) (lift p⊥) = lift (telecom P p p⊥) , _

data Choreo (I : ★) : ★₁ where
  _-[_]→_⁏_ : (A : I) (M : ★) (B : I) (ℂ : ..(m : M) → Choreo I) → Choreo I
  _-[_]→★⁏_ : (A : I) (M : ★)         (ℂ :   (m : M) → Choreo I) → Choreo I
  end       : Choreo I

module _ {I : ★} where 
    _-[_]→ø⁏_ : ∀ (A : I) (M : ★)         (ℂ : ..(m : M) → Choreo I) → Choreo I
    A -[ M ]→ø⁏ ℂ = A -[ ☐ M ]→★⁏ λ { [ m ] → ℂ m }

    _//_ : (ℂ : Choreo I) (p : I → 𝟚) → Proto
    (A -[ M ]→ B ⁏ ℂ) // p = case p A
                               0: case p B
                                    0: Πᴾ (☐ M) (λ { [ m ] → ℂ m // p })
                                    1: Πᴾ M     (λ     m   → ℂ m // p)
                               1: Σᴾ M (λ m → ℂ m // p)
    (A -[ M ]→★⁏   ℂ) // p = com (case p A 0: In 1: Out) λ m → ℂ m // p
    end               // p = end

    ℂObserver : Choreo I → Proto
    ℂObserver ℂ = ℂ // λ _ → 0₂

    ℂLog : Choreo I → Proto
    ℂLog ℂ = ℂ // λ _ → 1₂

    ℂLog-IsSource : ∀ ℂ → IsSource (ℂLog ℂ)
    ℂLog-IsSource (A -[ M ]→ B ⁏ ℂ) = com M λ m → ℂLog-IsSource (ℂ m)
    ℂLog-IsSource (A -[ M ]→★⁏   ℂ) = com M λ m → ℂLog-IsSource (ℂ m)
    ℂLog-IsSource end               = end

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
>>=-com (Σᴾ M P) (m , p0) p1       = first (_,_ m) (>>=-com (P m) p0 (p1 m))
>>=-com (Πᴾ M P) p0       (m , p1) = first (_,_ m) (>>=-com (P m) (p0 m) p1)

>>-com : (P : Proto){Q R : Proto}
       → ⟦ P >> Q  ⟧
       → ⟦ P >> R ⊥⟧
       → Log P × ⟦ Q ⟧ × ⟦ R ⊥⟧
>>-com P p q = >>=-com P p q

module ClientServerV1 (Query : ★₀) (Resp : Query → ★₀) (P : Proto) where
    Client : ℕ → Proto
    Client zero    = P
    Client (suc n) = Σᴾ Query λ q → Πᴾ (Resp q) λ r → Client n

    Server : ℕ → Proto
    Server zero    = P
    Server (suc n) = Πᴾ Query λ q → Σᴾ (Resp q) λ r → Server n

module ClientServerV2 (Query : ★₀) (Resp : Query → ★₀) where
    ClientRound ServerRound : Proto
    ClientRound = Σᴾ Query λ q → Πᴾ (Resp q) λ r → end
    ServerRound = dual ClientRound

    Client Server : ℕ → Proto
    Client n = replicateᴾ n ClientRound
    Server = dual ∘ Client

    DynamicServer StaticServer : Proto
    DynamicServer = Πᴾ ℕ λ n →
                    Server n
    StaticServer  = Σᴾ ℕ λ n →
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
dual->> (Πᴾ _ P) Q = com refl λ m → dual->> (P m) Q
dual->> (Σᴾ _ P) Q = com refl λ m → dual->> (P m) Q

  {- ohoh!
  dual->>= : ∀ P (Q : Log P → Proto) → dual (P >>= Q) ≡ᴾ dual P >>= (dual ∘ Q ∘ subst id (dual-Log P))
  dual->>= end Q = ≡ᴾ-refl _
  dual->>= (Πᴾ M P) Q = ProtoRel.com refl M (λ m → {!dual->>= (P m) (Q ∘ _,_ m)!})
  dual->>= (Σᴾ M P) Q = ProtoRel.com refl M (λ m → {!!})
  -}

module _ {{_ : FunExt}} (P : Proto) where
    dual-replicateᴾ : ∀ n → dual (replicateᴾ n P) ≡ᴾ replicateᴾ n (dual P)
    dual-replicateᴾ zero    = end
    dual-replicateᴾ (suc n) = dual->> P (replicateᴾ n P) ∙ᴾ ≡ᴾ-cong (_>>_ (dual P)) (dual-replicateᴾ n)

data LR : ★ where
  `L `R : LR

[L:_R:_] : ∀ {ℓ}{C : LR → ★_ ℓ}(l : C `L)(r : C `R)(lr : LR) → C lr
[L: l R: r ] `L = l
[L: l R: r ] `R = r

_⊕ᴾ_ : (l r : Proto) → Proto
l ⊕ᴾ r = Σᴾ LR [L: l R: r ]

_&ᴾ_ : (l r : Proto) → Proto
l &ᴾ r = Πᴾ LR [L: l R: r ]

module _ {P Q R S} where
    ⊕ᴾ-map : (⟦ P ⟧ → ⟦ Q ⟧) → (⟦ R ⟧ → ⟦ S ⟧) → ⟦ P ⊕ᴾ R ⟧ → ⟦ Q ⊕ᴾ S ⟧
    ⊕ᴾ-map f g (`L , pr) = `L , f pr
    ⊕ᴾ-map f g (`R , pr) = `R , g pr

    &ᴾ-map : (⟦ P ⟧ → ⟦ Q ⟧) → (⟦ R ⟧ → ⟦ S ⟧) → ⟦ P &ᴾ R ⟧ → ⟦ Q &ᴾ S ⟧
    &ᴾ-map f g p `L = f (p `L)
    &ᴾ-map f g p `R = g (p `R)

module _ {P Q} where
    ⊕ᴾ→⊎ : ⟦ P ⊕ᴾ Q ⟧ → ⟦ P ⟧ ⊎ ⟦ Q ⟧
    ⊕ᴾ→⊎ (`L , p) = inl p
    ⊕ᴾ→⊎ (`R , q) = inr q

    ⊎→⊕ᴾ : ⟦ P ⟧ ⊎ ⟦ Q ⟧ → ⟦ P ⊕ᴾ Q ⟧
    ⊎→⊕ᴾ (inl p) = `L , p
    ⊎→⊕ᴾ (inr q) = `R , q

    ⊎→⊕ᴾ→⊎ : ∀ x → ⊎→⊕ᴾ (⊕ᴾ→⊎ x) ≡ x
    ⊎→⊕ᴾ→⊎ (`L , _) = refl
    ⊎→⊕ᴾ→⊎ (`R , _) = refl

    ⊕ᴾ→⊎→⊕ᴾ : ∀ x → ⊕ᴾ→⊎ (⊎→⊕ᴾ x) ≡ x
    ⊕ᴾ→⊎→⊕ᴾ (inl _) = refl
    ⊕ᴾ→⊎→⊕ᴾ (inr _) = refl

    ⊕ᴾ≃⊎ : ⟦ P ⊕ᴾ Q ⟧ ≃ (⟦ P ⟧ ⊎ ⟦ Q ⟧)
    ⊕ᴾ≃⊎ = ⊕ᴾ→⊎ , record { linv = ⊎→⊕ᴾ ; is-linv = ⊎→⊕ᴾ→⊎ ; rinv = ⊎→⊕ᴾ ; is-rinv = ⊕ᴾ→⊎→⊕ᴾ }

    ⊕ᴾ≡⊎ : {{_ : UA}} → ⟦ P ⊕ᴾ Q ⟧ ≡ (⟦ P ⟧ ⊎ ⟦ Q ⟧)
    ⊕ᴾ≡⊎ = ua ⊕ᴾ≃⊎

    &ᴾ→× : ⟦ P &ᴾ Q ⟧ → ⟦ P ⟧ × ⟦ Q ⟧
    &ᴾ→× p = p `L , p `R

    ×→&ᴾ : ⟦ P ⟧ × ⟦ Q ⟧ → ⟦ P &ᴾ Q ⟧
    ×→&ᴾ (p , q) `L = p
    ×→&ᴾ (p , q) `R = q

    &ᴾ→×→&ᴾ : ∀ x → &ᴾ→× (×→&ᴾ x) ≡ x
    &ᴾ→×→&ᴾ (p , q) = refl

    module _ {{_ : FunExt}} where
        ×→&ᴾ→× : ∀ x → ×→&ᴾ (&ᴾ→× x) ≡ x
        ×→&ᴾ→× p = λ= λ { `L → refl ; `R → refl }

        &ᴾ≃× : ⟦ P &ᴾ Q ⟧ ≃ (⟦ P ⟧ × ⟦ Q ⟧)
        &ᴾ≃× = &ᴾ→× , record { linv = ×→&ᴾ ; is-linv = ×→&ᴾ→× ; rinv = ×→&ᴾ ; is-rinv = &ᴾ→×→&ᴾ }

        &ᴾ≡× : {{_ : UA}} → ⟦ P &ᴾ Q ⟧ ≡ (⟦ P ⟧ × ⟦ Q ⟧)
        &ᴾ≡× = ua &ᴾ≃×


module _ where

  _⅋ᴾ_ : Proto → Proto → Proto
  end    ⅋ᴾ Q      = Q
  Πᴾ M P ⅋ᴾ Q      = Πᴾ M λ m → P m ⅋ᴾ Q
  P      ⅋ᴾ end    = P
  P      ⅋ᴾ Πᴾ M Q = Πᴾ M λ m → P ⅋ᴾ Q m
  Σᴾ M P ⅋ᴾ Σᴾ N Q = Σᴾ (M ⊎ N) [inl: (λ m → P m ⅋ᴾ Σᴾ N Q)
                                ,inr: (λ n → Σᴾ M P ⅋ᴾ Q n) ]

  _⊗ᴾ_ : Proto → Proto → Proto
  end    ⊗ᴾ Q      = Q
  Σᴾ M P ⊗ᴾ Q      = Σᴾ M λ m → P m ⊗ᴾ Q
  P      ⊗ᴾ end    = P
  P      ⊗ᴾ Σᴾ M Q = Σᴾ M λ m → P ⊗ᴾ Q m
  Πᴾ M P ⊗ᴾ Πᴾ N Q = Πᴾ (M ⊎ N) [inl: (λ m → P m ⊗ᴾ Πᴾ N Q)
                                ,inr: (λ n → Πᴾ M P ⊗ᴾ Q n) ]

  module _ {{_ : FunExt}}{{_ : UA}} where
    ⊗-sendR : ∀ P{M}(Q : M → Proto) → ⟦ P ⊗ᴾ Σᴾ _ Q ⟧ ≡ (Σ M λ m → ⟦ P ⊗ᴾ Q m ⟧)
    ⊗-sendR end      Q = refl
    ⊗-sendR (Πᴾ _ P) Q = refl
    ⊗-sendR (Σᴾ _ P) Q = (Σ=′ _ λ m → ⊗-sendR (P m) Q) ∙ ΣΣ-comm

    ⊗-endR : ∀ P → ⟦ P ⊗ᴾ end ⟧ ≡ ⟦ P ⟧
    ⊗-endR end      = refl
    ⊗-endR (Πᴾ _ _) = refl
    ⊗-endR (Σᴾ _ P) = Σ=′ _ λ m → ⊗-endR (P m)

    ⊗ᴾ-comm : ∀ P Q → ⟦ P ⊗ᴾ Q ⟧ ≡ ⟦ Q ⊗ᴾ P ⟧
    ⊗ᴾ-comm end      Q        = ! ⊗-endR Q
    ⊗ᴾ-comm (Σᴾ _ P) Q        = (Σ=′ _ λ m → ⊗ᴾ-comm (P m) Q) ∙ ! ⊗-sendR Q P
    ⊗ᴾ-comm (Πᴾ _ P) end      = refl
    ⊗ᴾ-comm (Πᴾ _ P) (Σᴾ _ Q) = Σ=′ _ λ m → ⊗ᴾ-comm (Πᴾ _ P) (Q m)
    ⊗ᴾ-comm (Πᴾ _ P) (Πᴾ _ Q) = Π≃ ⊎-comm-equiv [inl: (λ m → ⊗ᴾ-comm (P m) (Πᴾ _ Q))
                                                ,inr: (λ m → ⊗ᴾ-comm (Πᴾ _ P) (Q m)) ]

  module _ {{_ : FunExt}}{{_ : UA}} where
    ⅋-recvR : ∀ P{M}(Q : M → Proto) → ⟦ P ⅋ᴾ Πᴾ _ Q ⟧ ≡ (Π M λ m → ⟦ P ⅋ᴾ Q m ⟧)
    ⅋-recvR end      Q = refl
    ⅋-recvR (Σᴾ _ P) Q = refl
    ⅋-recvR (Πᴾ _ P) Q = (Π=′ _ λ m → ⅋-recvR (P m) Q) ∙ ΠΠ-comm

    ⅋-endR : ∀ P → ⟦ P ⅋ᴾ end ⟧ ≡ ⟦ P ⟧
    ⅋-endR end      = refl
    ⅋-endR (Σᴾ _ _) = refl
    ⅋-endR (Πᴾ _ P) = Π=′ _ λ m → ⅋-endR (P m)

  module _ {{_ : FunExt}}{{_ : UA}} where
    ⅋ᴾ-comm : ∀ P Q → ⟦ P ⅋ᴾ Q ⟧ ≡ ⟦ Q ⅋ᴾ P ⟧
    ⅋ᴾ-comm end      Q        = ! ⅋-endR Q
    ⅋ᴾ-comm (Πᴾ _ P) Q        = (Π=′ _ λ m → ⅋ᴾ-comm (P m) Q) ∙ ! ⅋-recvR Q P
    ⅋ᴾ-comm (Σᴾ _ P) end      = refl
    ⅋ᴾ-comm (Σᴾ _ P) (Πᴾ _ Q) = Π=′ _ λ m → ⅋ᴾ-comm (Σᴾ _ P) (Q m)
    ⅋ᴾ-comm (Σᴾ _ P) (Σᴾ _ Q) = Σ≃ ⊎-comm-equiv [inl: (λ m → ⅋ᴾ-comm (P m) (Σᴾ _ Q))
                                                ,inr: (λ m → ⅋ᴾ-comm (Σᴾ _ P) (Q m)) ]

  module _ {{_ : FunExt}}{{_ : UA}} where
    ⅋-assoc : ∀ P Q R → ⟦ P ⅋ᴾ (Q ⅋ᴾ R) ⟧ ≡ ⟦ (P ⅋ᴾ Q) ⅋ᴾ R ⟧
    ⅋-assoc end      Q        R        = refl
    ⅋-assoc (Πᴾ _ P) Q        R        = Π=′ _ λ m → ⅋-assoc (P m) Q R
    ⅋-assoc (Σᴾ _ P) end      R        = refl
    ⅋-assoc (Σᴾ _ P) (Πᴾ _ Q) R        = Π=′ _ λ m → ⅋-assoc (Σᴾ _ P) (Q m) R
    ⅋-assoc (Σᴾ _ P) (Σᴾ _ Q) end      = refl
    ⅋-assoc (Σᴾ _ P) (Σᴾ _ Q) (Πᴾ _ R) = Π=′ _ λ m → ⅋-assoc (Σᴾ _ P) (Σᴾ _ Q) (R m)
    ⅋-assoc (Σᴾ _ P) (Σᴾ _ Q) (Σᴾ _ R) = Σ≃ ⊎-assoc-equiv
                                             λ { (inl m)       → ⅋-assoc (P m) (Σᴾ _ Q) (Σᴾ _ R)
                                               ; (inr (inl m)) → ⅋-assoc (Σᴾ _ P) (Q m) (Σᴾ _ R)
                                               ; (inr (inr m)) → ⅋-assoc (Σᴾ _ P) (Σᴾ _ Q) (R m) }

  module _ {P Q R}{{_ : FunExt}} where
    dist-⊗-⊕′ : ⟦ (Q ⊕ᴾ R) ⊗ᴾ P ⟧ ≡ ⟦ (Q ⊗ᴾ P) ⊕ᴾ (R ⊗ᴾ P) ⟧
    dist-⊗-⊕′ = Σ=′ LR [L: refl R: refl ]

    dist-⅋-&′ : ⟦ (Q &ᴾ R) ⅋ᴾ P ⟧ ≡ ⟦ (Q ⅋ᴾ P) &ᴾ (R ⅋ᴾ P) ⟧
    dist-⅋-&′ = Π=′ LR [L: refl R: refl ]

    module _ {{_ : UA}} where
        dist-⊗-⊕ : ⟦ P ⊗ᴾ (Q ⊕ᴾ R) ⟧ ≡ ⟦ (P ⊗ᴾ Q) ⊕ᴾ (P ⊗ᴾ R) ⟧
        dist-⊗-⊕ = ⊗ᴾ-comm P (Q ⊕ᴾ R)
                 ∙ dist-⊗-⊕′
                 ∙ ⊕ᴾ≡⊎
                 ∙ ⊎= (⊗ᴾ-comm Q P) (⊗ᴾ-comm R P)
                 ∙ ! ⊕ᴾ≡⊎

        dist-⅋-& : ⟦ P ⅋ᴾ (Q &ᴾ R) ⟧ ≡ ⟦ (P ⅋ᴾ Q) &ᴾ (P ⅋ᴾ R) ⟧
        dist-⅋-& = ⅋ᴾ-comm P (Q &ᴾ R)
                 ∙ dist-⅋-&′
                 ∙ &ᴾ≡×
                 ∙ ×= (⅋ᴾ-comm Q P) (⅋ᴾ-comm R P)
                 ∙ ! &ᴾ≡×

  -- P ⟦⊗⟧ Q ≃ ⟦ P ⊗ᴾ Q ⟧
  -- but potentially more convenient
  _⟦⊗⟧_ : Proto → Proto → ★
  end    ⟦⊗⟧ Q      = ⟦ Q ⟧
  Σᴾ M P ⟦⊗⟧ Q      = Σ M λ m → P m ⟦⊗⟧ Q
  P      ⟦⊗⟧ end    = ⟦ P ⟧
  P      ⟦⊗⟧ Σᴾ M Q = Σ M λ m → P ⟦⊗⟧ Q m
  Πᴾ M P ⟦⊗⟧ Πᴾ N Q = (Π M λ m → P m    ⟦⊗⟧ Πᴾ N Q)
                    × (Π N λ n → Πᴾ M P ⟦⊗⟧ Q n)

  module _ {{_ : FunExt}}{{_ : UA}} where
    ⟦⊗⟧-correct : ∀ P Q → P ⟦⊗⟧ Q ≡ ⟦ P ⊗ᴾ Q ⟧
    ⟦⊗⟧-correct end      Q        = refl
    ⟦⊗⟧-correct (Σᴾ M P) Q        = Σ=′ M λ m → ⟦⊗⟧-correct (P m) Q
    ⟦⊗⟧-correct (Πᴾ M P) end      = refl
    ⟦⊗⟧-correct (Πᴾ M P) (Σᴾ N Q) = Σ=′ N λ n → ⟦⊗⟧-correct (Πᴾ M P) (Q n)
    ⟦⊗⟧-correct (Πᴾ M P) (Πᴾ N Q) = ! dist-×-Π
                                  ∙ Π=′ (M ⊎ N) λ { (inl m)  → ⟦⊗⟧-correct (P m) (Πᴾ N Q)
                                                  ; (inr n) → ⟦⊗⟧-correct (Πᴾ M P) (Q n) }

  -- an alternative, potentially more convenient
  _⟦⅋⟧_ : Proto → Proto → ★
  end    ⟦⅋⟧ Q       = ⟦ Q ⟧
  Πᴾ M P ⟦⅋⟧ Q       = Π M λ m → P m ⟦⅋⟧ Q
  P      ⟦⅋⟧ end     = ⟦ P ⟧
  P      ⟦⅋⟧ Πᴾ M  Q = Π M λ m → P ⟦⅋⟧ Q m
  Σᴾ M P ⟦⅋⟧ Σᴾ N Q = (Σ M  λ m  → P m    ⟦⅋⟧ Σᴾ N Q)
                     ⊎ (Σ N λ n → Σᴾ M P ⟦⅋⟧ Q n)

  module _ {{_ : FunExt}}{{_ : UA}} where
    ⟦⅋⟧-correct : ∀ P Q → P ⟦⅋⟧ Q ≡ ⟦ P ⅋ᴾ Q ⟧
    ⟦⅋⟧-correct end      Q        = refl
    ⟦⅋⟧-correct (Πᴾ M P) Q        = Π=′ M λ m → ⟦⅋⟧-correct (P m) Q
    ⟦⅋⟧-correct (Σᴾ M P) end      = refl
    ⟦⅋⟧-correct (Σᴾ M P) (Πᴾ N Q) = Π=′ N λ n → ⟦⅋⟧-correct (Σᴾ M P) (Q n)
    ⟦⅋⟧-correct (Σᴾ M P) (Σᴾ N Q) = ! dist-⊎-Σ
                                  ∙ Σ=′ (M ⊎ N) λ { (inl m) → ⟦⅋⟧-correct (P m) (Σᴾ N Q)
                                                  ; (inr n) → ⟦⅋⟧-correct (Σᴾ M P) (Q n) }

  ⊗⅋-dual : ∀ P Q → dual (P ⅋ᴾ Q) ≡ᴾ dual P ⊗ᴾ dual Q
  ⊗⅋-dual end Q = ≡ᴾ-refl _
  ⊗⅋-dual (Πᴾ _ P) Q = com refl λ m → ⊗⅋-dual (P m) _
  ⊗⅋-dual (Σᴾ _ P) end = ≡ᴾ-refl _
  ⊗⅋-dual (Σᴾ _ P) (Πᴾ _ Q) = com refl λ n → ⊗⅋-dual (Σᴾ _ P) (Q n)
  ⊗⅋-dual (Σᴾ _ P) (Σᴾ _ Q) = com refl
    [inl: (λ m → ⊗⅋-dual (P m) (Σᴾ _ Q))
    ,inr: (λ n → ⊗⅋-dual (Σᴾ _ P) (Q n))
    ]

  data View-⅋-proto : Proto → Proto → ★₁ where
    end-X     : ∀ Q → View-⅋-proto end Q
    recv-X    : ∀ {M}(P : M → Proto)Q → View-⅋-proto (Πᴾ M P) Q
    send-send : ∀ {M N}(P : M → Proto)(Q : N → Proto) → View-⅋-proto (Σᴾ M P) (Σᴾ N Q)
    send-recv : ∀ {M N}(P : M → Proto)(Q : N → Proto) → View-⅋-proto (Σᴾ M P) (Πᴾ N Q)
    send-end  : ∀ {M}(P : M → Proto) → View-⅋-proto (Σᴾ M P) end

  view-⅋-proto : ∀ P Q → View-⅋-proto P Q
  view-⅋-proto end      Q        = end-X Q
  view-⅋-proto (Πᴾ _ P) Q        = recv-X P Q
  view-⅋-proto (Σᴾ _ P) end      = send-end P
  view-⅋-proto (Σᴾ _ P) (Πᴾ _ Q) = send-recv P Q
  view-⅋-proto (Σᴾ _ P) (Σᴾ _ Q) = send-send P Q

  data View-⊗-proto : Proto → Proto → ★₁ where
    end-X     : ∀ Q → View-⊗-proto end Q
    send-X    : ∀ {M}(P : M → Proto)Q → View-⊗-proto (Σᴾ M P) Q
    recv-recv : ∀ {M N}(P : M → Proto)(Q : N → Proto) → View-⊗-proto (Πᴾ M P) (Πᴾ N Q)
    recv-send : ∀ {M N}(P : M → Proto)(Q : N → Proto) → View-⊗-proto (Πᴾ M P) (Σᴾ N Q)
    recv-end  : ∀ {M}(P : M → Proto) → View-⊗-proto (Πᴾ M P) end

  view-⊗-proto : ∀ P Q → View-⊗-proto P Q
  view-⊗-proto end      Q        = end-X Q
  view-⊗-proto (Σᴾ _ P) Q        = send-X P Q
  view-⊗-proto (Πᴾ _ P) end      = recv-end P
  view-⊗-proto (Πᴾ _ P) (Πᴾ _ Q) = recv-recv P Q
  view-⊗-proto (Πᴾ _ P) (Σᴾ _ Q) = recv-send P Q

  -- the terminology used for the constructor follows the behavior of the combined process
  data View-⅋ : ∀ P Q → ⟦ P ⅋ᴾ Q ⟧ → ★₁ where
    sendL' : ∀ {M N}(P : M → Proto)(Q : N → Proto)(m  : M )(p : ⟦ P m ⅋ᴾ Σᴾ N Q ⟧) → View-⅋ (Σᴾ M P) (Σᴾ N Q) (inl m  , p)
    sendR' : ∀ {M N}(P : M → Proto)(Q : N → Proto)(n : N)(p : ⟦ Σᴾ M P ⅋ᴾ Q n ⟧) → View-⅋ (Σᴾ M P) (Σᴾ N Q) (inr n , p)
    recvL' : ∀ {M} (P : M → Proto) Q (p : ((m : M) → ⟦ P m ⅋ᴾ Q ⟧)) → View-⅋ (Πᴾ M P) Q p
    recvR' : ∀ {M N} (P : M → Proto) (Q : N → Proto)(p : (n : N) → ⟦ Σᴾ M P ⅋ᴾ Q n ⟧) → View-⅋ (Σᴾ M P) (Πᴾ N Q) p
    endL   : ∀ Q (p : ⟦ Q ⟧) → View-⅋ end Q p
    send   : ∀ {M}(P : M → Proto)(m : M)(p : ⟦ P m ⟧) → View-⅋ (Σᴾ M P) end (m , p)

  view-⅋ : ∀ P Q (p : ⟦ P ⅋ᴾ Q ⟧) → View-⅋ P Q p
  view-⅋ end Q p = endL Q p
  view-⅋ (Πᴾ M P) Q p = recvL' P Q p
  view-⅋ (Σᴾ M P) end (m , p) = send P m p
  view-⅋ (Σᴾ M P) (Πᴾ N Q) p = recvR' P Q p
  view-⅋ (Σᴾ M P) (Σᴾ N Q) (inl x , p) = sendL' P Q x p
  view-⅋ (Σᴾ M P) (Σᴾ N Q) (inr y , p) = sendR' P Q y p

  {-
  -- use coe (⅋-assoc P Q R)
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

  -- use coe (⅋-endR P) instead
  ⅋ᴾ-rend : ∀ P → ⟦ P ⅋ᴾ end ⟧  → ⟦ P ⟧
  ⅋ᴾ-rend end      p = p
  ⅋ᴾ-rend (Σᴾ _ _) p = p
  ⅋ᴾ-rend (Πᴾ _ P) p = λ m → ⅋ᴾ-rend (P m) (p m)

  -- use coe! (⅋-endR P) instead
  ⅋ᴾ-rend! : ∀ P  → ⟦ P ⟧ → ⟦ P ⅋ᴾ end ⟧
  ⅋ᴾ-rend! end      p = p
  ⅋ᴾ-rend! (Σᴾ _ _) p = p
  ⅋ᴾ-rend! (Πᴾ _ P) p = λ m → ⅋ᴾ-rend! (P m) (p m)

  -- use coe! (⅋-recvR P Q) instead
  ⅋ᴾ-isendR : ∀ {N} P Q → ⟦ P ⅋ᴾ Πᴾ N Q ⟧ → (n : N) → ⟦ P ⅋ᴾ Q n ⟧
  ⅋ᴾ-isendR end Q s n = s n
  ⅋ᴾ-isendR (Πᴾ M P) Q s n = λ m → ⅋ᴾ-isendR (P m) Q (s m) n
  ⅋ᴾ-isendR (Σᴾ M P) Q s n = s n


  -- see ⅋-recvR
  ⅋ᴾ-recvR : ∀ {M} P Q → ((m : M) → ⟦ P ⅋ᴾ Q m ⟧) → ⟦ P ⅋ᴾ Πᴾ M Q ⟧
  ⅋ᴾ-recvR end      Q s = s
  ⅋ᴾ-recvR (Πᴾ M P) Q s = λ x → ⅋ᴾ-recvR (P x) Q (λ m → s m x)
  ⅋ᴾ-recvR (Σᴾ M P) Q s = s
  -}

  module _ {{_ : FunExt}}{{_ : UA}} where

    ⅋ᴾ-sendL : ∀ {M}{P : M → Proto} Q (m : M) → ⟦ P m ⅋ᴾ Q ⟧ → ⟦ Σᴾ M P ⅋ᴾ Q ⟧
    ⅋ᴾ-sendL {P = P} end      m p = m , coe (⅋-endR (P m)) p
    ⅋ᴾ-sendL {P = P} (Πᴾ M Q) m p = λ n → ⅋ᴾ-sendL (Q n) m (coe (⅋-recvR (P m) _) p n)
    ⅋ᴾ-sendL         (Σᴾ M Q) m p = inl m , p

    ⅋ᴾ-sendR : ∀ {M}P{Q : M → Proto}(m : M) → ⟦ P ⅋ᴾ Q m ⟧ → ⟦ P ⅋ᴾ Σᴾ M Q ⟧
    ⅋ᴾ-sendR end      m p = m , p
    ⅋ᴾ-sendR (Σᴾ M P) m p = inr m , p
    ⅋ᴾ-sendR (Πᴾ M P) m p = λ x → ⅋ᴾ-sendR (P x) m (p x)

    ⅋ᴾ-id : ∀ P → ⟦ dual P ⅋ᴾ P ⟧
    ⅋ᴾ-id end      = end
    ⅋ᴾ-id (Πᴾ M P) = λ x → ⅋ᴾ-sendL (P x) x (⅋ᴾ-id (P x))
    ⅋ᴾ-id (Σᴾ M P) = λ x → ⅋ᴾ-sendR (dual (P x)) x (⅋ᴾ-id (P x))

  data View-∘ : ∀ P Q R → ⟦ P ⅋ᴾ Q ⟧ → ⟦ dual Q ⅋ᴾ R ⟧ → ★₁ where
    sendLL : ∀ {M N}(P : M → Proto)(Q : N → Proto) R (m : M)(p : ⟦ P m ⅋ᴾ Σᴾ _ Q ⟧)(q : ⟦ dual (Σᴾ _ Q) ⅋ᴾ R ⟧)
             → View-∘ (Σᴾ M P) (Σᴾ _ Q) R (inl m , p) q
    recvLL : ∀ {M} (P : M → Proto) Q R
               (p : ((m : M) → ⟦ P m ⅋ᴾ Q ⟧))(q : ⟦ dual Q ⅋ᴾ R ⟧)
             → View-∘ (Πᴾ M P) Q R p q
    recvR-sendR : ∀ {MP MQ MR}ioP(P : MP → Proto)(Q : MQ → Proto)(R : MR → Proto)
                    (mR : MR)(p : ⟦ com ioP P ⅋ᴾ Πᴾ _ Q ⟧)(q : ⟦ dual (Πᴾ _ Q) ⅋ᴾ R mR ⟧)
                    → View-∘ (com ioP P) (Πᴾ _ Q) (Σᴾ _ R) p (inr mR , q)

    recvRR : ∀ {MP MQ MR}(P : MP → Proto)(Q : MQ → Proto)(R : MR → Proto)
               (p : ⟦ Σᴾ _ P ⅋ᴾ Πᴾ _ Q ⟧)(q : (m : MR) → ⟦ dual (Πᴾ _ Q) ⅋ᴾ R m ⟧)
             → View-∘ (Σᴾ _ P) (Πᴾ _ Q) (Πᴾ _ R) p q
    sendR-recvL : ∀ {MP MQ}(P : MP → Proto)(Q : MQ → Proto)R(m : MQ)
                    (p : ⟦ Σᴾ _ P ⅋ᴾ Q m ⟧)(q : (m : MQ) → ⟦ dual (Q m) ⅋ᴾ R ⟧)
                  → View-∘ (Σᴾ _ P) (Σᴾ _ Q) R (inr m , p) q
    recvR-sendL : ∀ {MP MQ MR}(P : MP → Proto)(Q : MQ → Proto)(R : MR → Proto)
                    (p : (m : MQ) → ⟦ Σᴾ _ P ⅋ᴾ Q m ⟧)(m : MQ)(q : ⟦ dual (Q m) ⅋ᴾ Σᴾ _ R ⟧)
                  → View-∘ (Σᴾ _ P) (Πᴾ _ Q) (Σᴾ _ R) p (inl m , q)
    endL : ∀ Q R
           → (q : ⟦ Q ⟧)(qr : ⟦ dual Q ⅋ᴾ R ⟧)
           → View-∘ end Q R q qr
    sendLM : ∀ {MP}(P : MP → Proto)R
               (m : MP)(p : ⟦ P m ⟧)(r : ⟦ R ⟧)
             → View-∘ (Σᴾ _ P) end R (m , p) r
    recvL-sendR : ∀ {MP MQ}(P : MP → Proto)(Q : MQ → Proto)
                    (m : MQ)(p : ∀ m → ⟦ Σᴾ _ P ⅋ᴾ Q m ⟧)(q : ⟦ dual (Q m) ⟧)
                  → View-∘ (Σᴾ _ P) (Πᴾ _ Q) end p (m , q)

  view-∘ : ∀ P Q R (pq : ⟦ P ⅋ᴾ Q ⟧)(qr : ⟦ dual Q ⅋ᴾ R ⟧) → View-∘ P Q R pq qr
  view-∘ P Q R pq qr = view-∘-view (view-⅋ P Q pq) (view-⅋ (dual Q) R qr)
   where
    view-∘-view : ∀ {P Q R}{pq : ⟦ P ⅋ᴾ Q ⟧}{qr : ⟦ dual Q ⅋ᴾ R ⟧} → View-⅋ P Q pq → View-⅋ (dual Q) R qr → View-∘ P Q R pq qr
    view-∘-view (sendL' _ _ _ _) _                 = sendLL _ _ _ _ _ _
    view-∘-view (recvL' _ _ _)   _                 = recvLL _ _ _ _ _
    view-∘-view (sendR' _ _ _ _) _                 = sendR-recvL _ _ _ _ _ _
    view-∘-view (recvR' _ _ _)   (sendL' ._ _ _ _) = recvR-sendL _ _ _ _ _ _
    view-∘-view (recvR' _ _ _)   (sendR' ._ _ _ _) = recvR-sendR _ _ _ _ _ _ _
    view-∘-view (recvR' _ _ _)   (recvR' ._ _ _)   = recvRR _ _ _ _ _
    view-∘-view (recvR' _ _ _)   (send ._ _ _)     = recvL-sendR _ _ _ _ _
    view-∘-view (endL _ _)       _                 = endL _ _ _ _
    view-∘-view (send _ _ _)     _                 = sendLM _ _ _ _ _

  ⅋ᴾ-apply : ∀ P Q → ⟦ P ⅋ᴾ Q ⟧ → ⟦ dual P ⟧ → ⟦ Q ⟧
  ⅋ᴾ-apply end      Q        s           p       = s
  ⅋ᴾ-apply (Πᴾ M P) Q        s           (m , p) = ⅋ᴾ-apply (P m) Q (s m) p
  ⅋ᴾ-apply (Σᴾ M P) end      s           p       = _
  ⅋ᴾ-apply (Σᴾ M P) (Πᴾ N Q) s           p n     = ⅋ᴾ-apply (Σᴾ M P) (Q n) (s n) p
  ⅋ᴾ-apply (Σᴾ M P) (Σᴾ N Q) (inl m , s) p       = ⅋ᴾ-apply (P m) (Σᴾ N Q) s (p m)
  ⅋ᴾ-apply (Σᴾ M P) (Σᴾ N Q) (inr m , s) p       = m , ⅋ᴾ-apply (Σᴾ M P) (Q m) s p

  {-
  -- see dist-⅋-&
  dist-⅋-fst : ∀ P Q R → ⟦ P ⅋ᴾ (Q &ᴾ R) ⟧ → ⟦ P ⅋ᴾ Q ⟧
  dist-⅋-fst (Πᴾ _ P) Q R p = λ m → dist-⅋-fst (P m) Q R (p m)
  dist-⅋-fst (Σᴾ _ P) Q R p = p `L
  dist-⅋-fst end      Q R p = p `L

  -- see dist-⅋-&
  dist-⅋-snd : ∀ P Q R → ⟦ P ⅋ᴾ (Q &ᴾ R) ⟧ → ⟦ P ⅋ᴾ R ⟧
  dist-⅋-snd (Πᴾ _ P) Q R p = λ m → dist-⅋-snd (P m) Q R (p m)
  dist-⅋-snd (Σᴾ _ P) Q R p = p `R
  dist-⅋-snd end      Q R p = p `R

  -- see dist-⅋-&
  dist-⅋-× : ∀ P Q R → ⟦ P ⅋ᴾ (Q &ᴾ R) ⟧ → ⟦ P ⅋ᴾ Q ⟧ × ⟦ P ⅋ᴾ R ⟧
  dist-⅋-× P Q R p = dist-⅋-fst P Q R p , dist-⅋-snd P Q R p

  -- see dist-⅋-&
  dist-⅋-& : ∀ P Q R → ⟦ P ⅋ᴾ (Q &ᴾ R) ⟧ → ⟦ (P ⅋ᴾ Q) &ᴾ (P ⅋ᴾ R) ⟧
  dist-⅋-& P Q R p = ×→&ᴾ (dist-⅋-× P Q R p)

  -- see dist-⅋-&
  factor-,-⅋ : ∀ P Q R → ⟦ P ⅋ᴾ Q ⟧ → ⟦ P ⅋ᴾ R ⟧ → ⟦ P ⅋ᴾ (Q &ᴾ R) ⟧
  factor-,-⅋ end      Q R pq pr = ×→&ᴾ (pq , pr)
  factor-,-⅋ (Πᴾ _ P) Q R pq pr = λ m → factor-,-⅋ (P m) Q R (pq m) (pr m)
  factor-,-⅋ (Σᴾ _ P) Q R pq pr = [L: pq R: pr ]

  -- see dist-⅋-&
  factor-×-⅋ : ∀ P Q R → ⟦ P ⅋ᴾ Q ⟧ × ⟦ P ⅋ᴾ R ⟧ → ⟦ P ⅋ᴾ (Q &ᴾ R) ⟧
  factor-×-⅋ P Q R (p , q) = factor-,-⅋ P Q R p q

  -- see dist-⅋-&
  factor-&-⅋ : ∀ P Q R → ⟦ (P ⅋ᴾ Q) &ᴾ (P ⅋ᴾ R) ⟧ → ⟦ P ⅋ᴾ (Q &ᴾ R) ⟧
  factor-&-⅋ P Q R p = factor-×-⅋ P Q R (&ᴾ→× p)

  -- see dist-⅋-&
  module _ {{_ : FunExt}} where
    dist-⅋-fst-factor-&-, : ∀ P Q R (pq : ⟦ P ⅋ᴾ Q ⟧)(pr : ⟦ P ⅋ᴾ R ⟧)
                            → dist-⅋-fst P Q R (factor-,-⅋ P Q R pq pr) ≡ pq
    dist-⅋-fst-factor-&-, (Πᴾ _ P) Q R pq pr = λ= λ m → dist-⅋-fst-factor-&-, (P m) Q R (pq m) (pr m)
    dist-⅋-fst-factor-&-, (Σᴾ _ P) Q R pq pr = refl
    dist-⅋-fst-factor-&-, end      Q R pq pr = refl

    dist-⅋-snd-factor-&-, : ∀ P Q R (pq : ⟦ P ⅋ᴾ Q ⟧)(pr : ⟦ P ⅋ᴾ R ⟧)
                            → dist-⅋-snd P Q R (factor-,-⅋ P Q R pq pr) ≡ pr
    dist-⅋-snd-factor-&-, (Πᴾ _ P) Q R pq pr = λ= λ m → dist-⅋-snd-factor-&-, (P m) Q R (pq m) (pr m)
    dist-⅋-snd-factor-&-, (Σᴾ _ P) Q R pq pr = refl
    dist-⅋-snd-factor-&-, end      Q R pq pr = refl

    factor-×-⅋-linv-dist-⅋-× : ∀ P Q R → (factor-×-⅋ P Q R) LeftInverseOf (dist-⅋-× P Q R)
    factor-×-⅋-linv-dist-⅋-× (Πᴾ _ P) Q R p = λ= λ m → factor-×-⅋-linv-dist-⅋-× (P m) Q R (p m)
    factor-×-⅋-linv-dist-⅋-× (Σᴾ _ P) Q R p = λ= λ { `L → refl ; `R → refl }
    factor-×-⅋-linv-dist-⅋-× end      Q R p = λ= λ { `L → refl ; `R → refl }

    module _ P Q R where
        factor-×-⅋-rinv-dist-⅋-× : (factor-×-⅋ P Q R) RightInverseOf (dist-⅋-× P Q R)
        factor-×-⅋-rinv-dist-⅋-× (x , y) = pair×= (dist-⅋-fst-factor-&-, P Q R x y) (dist-⅋-snd-factor-&-, P Q R x y)

        dist-⅋-×-≃ : ⟦ P ⅋ᴾ (Q &ᴾ R) ⟧ ≃ (⟦ P ⅋ᴾ Q ⟧ × ⟦ P ⅋ᴾ R ⟧)
        dist-⅋-×-≃ = dist-⅋-× P Q R
                   , record { linv = factor-×-⅋ P Q R; is-linv = factor-×-⅋-linv-dist-⅋-× P Q R
                            ; rinv = factor-×-⅋ P Q R; is-rinv = factor-×-⅋-rinv-dist-⅋-× }

        dist-⅋-&-≃ : ⟦ P ⅋ᴾ (Q &ᴾ R) ⟧ ≃ ⟦ (P ⅋ᴾ Q) &ᴾ (P ⅋ᴾ R) ⟧
        dist-⅋-&-≃ = dist-⅋-×-≃ ≃-∙ ≃-! &ᴾ≃×
  -}

module _ {{_ : FunExt}}{{_ : UA}} where
  ⅋ᴾ-apply' : ∀ {P Q} → ⟦ dual P ⅋ᴾ Q ⟧ → ⟦ P ⟧ → ⟦ Q ⟧
  ⅋ᴾ-apply' {P} {Q} pq p = ⅋ᴾ-apply (dual P) Q pq (subst ⟦_⟧ (≡.sym (≡ᴾ-sound (dual-involutive P))) p)

  -- left-biased “strategy”
  par : ∀ P Q → ⟦ P ⟧ → ⟦ Q ⟧ → ⟦ P ⅋ᴾ Q ⟧
  par P Q p q = par-view (view-proc P p)
    where par-view : ∀ {P} {p : ⟦ P ⟧} → ViewProc P p → ⟦ P ⅋ᴾ Q ⟧
          par-view (send M P m p) = ⅋ᴾ-sendL Q m (par (P m) Q p q)
          par-view (recv M P p)   = λ m → par (P m) Q (p m) q
          par-view end            = q

  ⅋ᴾ-∘ : ∀ P Q R → ⟦ P ⅋ᴾ Q ⟧ → ⟦ dual Q ⅋ᴾ R ⟧ → ⟦ P ⅋ᴾ R ⟧
  ⅋ᴾ-∘ P Q R pq qr = ⅋ᴾ-∘-view (view-∘ P Q R pq qr)
   where
    ⅋ᴾ-∘-view : ∀ {P Q R}{pq : ⟦ P ⅋ᴾ Q ⟧}{qr : ⟦ dual Q ⅋ᴾ R ⟧} → View-∘ P Q R pq qr → ⟦ P ⅋ᴾ R ⟧
    ⅋ᴾ-∘-view (sendLL P Q R m p qr)          = ⅋ᴾ-sendL R m (⅋ᴾ-∘ (P m) (Σᴾ _ Q) R p qr)
    ⅋ᴾ-∘-view (recvLL P Q R p qr)            = λ m → ⅋ᴾ-∘ (P m) Q R (p m) qr
    ⅋ᴾ-∘-view (recvR-sendR ioP P Q R m pq q) = ⅋ᴾ-sendR (com ioP P) m (⅋ᴾ-∘ (com ioP P) (Πᴾ _ Q) (R m) pq q)
    ⅋ᴾ-∘-view (recvRR P Q R pq q)            = λ m → ⅋ᴾ-∘ (Σᴾ _ P) (Πᴾ _ Q) (R m) pq (q m)
    ⅋ᴾ-∘-view (sendR-recvL P Q R m p q)      = ⅋ᴾ-∘ (Σᴾ _ P) (Q m) R p (q m)
    ⅋ᴾ-∘-view (recvR-sendL P Q R p m q)      = ⅋ᴾ-∘ (Σᴾ _ P) (Q m) (Σᴾ _ R) (p m) q
    ⅋ᴾ-∘-view (endL Q R pq qr)               = ⅋ᴾ-apply' {Q} {R} qr pq
    ⅋ᴾ-∘-view (sendLM P R m pq qr)           = ⅋ᴾ-sendL R m (par (P m) R pq qr)
    ⅋ᴾ-∘-view (recvL-sendR P Q m pq qr)      = ⅋ᴾ-∘ (Σᴾ _ P) (Q m) end (pq m) (coe! (⅋-endR (dual (Q m))) qr)

    {-
  mutual
    ⅋ᴾ-comm : ∀ P Q → ⟦ P ⅋ᴾ Q ⟧ → ⟦ Q ⅋ᴾ P ⟧
    ⅋ᴾ-comm P Q p = ⅋ᴾ-comm-view (view-⅋ P Q p)

    ⅋ᴾ-comm-view : ∀ {P Q} {pq : ⟦ P ⅋ᴾ Q ⟧} → View-⅋ P Q pq → ⟦ Q ⅋ᴾ P ⟧
    ⅋ᴾ-comm-view (sendL' P Q m p) = ⅋ᴾ-sendR (Σᴾ _ Q) m (⅋ᴾ-comm (P m) (Σᴾ _ Q) p)
    ⅋ᴾ-comm-view (sendR' P Q n p) = inl n , ⅋ᴾ-comm (Σᴾ _ P) (Q n) p
    ⅋ᴾ-comm-view (recvL' P Q pq)  = ⅋ᴾ-recvR Q P λ m → ⅋ᴾ-comm (P m) Q (pq m)
    ⅋ᴾ-comm-view (recvR' P Q pq)  = λ n → ⅋ᴾ-comm (Σᴾ _ P) (Q n) (pq n)
    ⅋ᴾ-comm-view (endL Q pq)      = ⅋ᴾ-rend! Q pq
    ⅋ᴾ-comm-view (send P m pq)    = m , pq
  -}

  commaᴾ : ∀ {P Q} → ⟦ P ⟧ → ⟦ Q ⟧ → ⟦ P ⊗ᴾ Q ⟧
  commaᴾ {end}    {Q}      p q       = q
  commaᴾ {Σᴾ M P} {Q}      (m , p) q = m , commaᴾ {P m} p q
  commaᴾ {Πᴾ M P} {end}    p end     = p
  commaᴾ {Πᴾ M P} {Σᴾ _ Q} p (m , q) = m , commaᴾ {Πᴾ M P} {Q m} p q
  commaᴾ {Πᴾ M P} {Πᴾ N Q} p q       = [inl: (λ m → commaᴾ {P m}    {Πᴾ _ Q} (p m) q)
                                       ,inr: (λ n → commaᴾ {Πᴾ _ P} {Q n}    p     (q n)) ]

  ⊗ᴾ-fst : ∀ P Q → ⟦ P ⊗ᴾ Q ⟧ → ⟦ P ⟧
  ⊗ᴾ-fst end      Q        pq       = _
  ⊗ᴾ-fst (Σᴾ M P) Q        (m , pq) = m , ⊗ᴾ-fst (P m) Q pq
  ⊗ᴾ-fst (Πᴾ M P) end      pq       = pq
  ⊗ᴾ-fst (Πᴾ M P) (Σᴾ _ Q) (_ , pq) = ⊗ᴾ-fst (Πᴾ M P) (Q _) pq
  ⊗ᴾ-fst (Πᴾ M P) (Πᴾ N Q) pq       = λ m → ⊗ᴾ-fst (P m) (Πᴾ N Q) (pq (inl m))

  ⊗ᴾ-snd : ∀ P Q → ⟦ P ⊗ᴾ Q ⟧ → ⟦ Q ⟧
  ⊗ᴾ-snd end      Q        pq       = pq
  ⊗ᴾ-snd (Σᴾ M P) Q        (_ , pq) = ⊗ᴾ-snd (P _) Q pq
  ⊗ᴾ-snd (Πᴾ M P) end      pq       = end
  ⊗ᴾ-snd (Πᴾ M P) (Σᴾ _ Q) (m , pq) = m , ⊗ᴾ-snd (Πᴾ M P) (Q m) pq
  ⊗ᴾ-snd (Πᴾ M P) (Πᴾ N Q) pq       = λ m → ⊗ᴾ-snd (Πᴾ M P) (Q m) (pq (inr m))

  ⊗ᴾ-comma-fst : ∀ P Q (p : ⟦ P ⟧)(q : ⟦ Q ⟧) → ⊗ᴾ-fst P Q (commaᴾ {P} {Q} p q) ≡ p
  ⊗ᴾ-comma-fst end      Q        p q       = refl
  ⊗ᴾ-comma-fst (Σᴾ M P) Q        (m , p) q = pair= refl (⊗ᴾ-comma-fst (P m) Q p q)
  ⊗ᴾ-comma-fst (Πᴾ M P) end      p q       = refl
  ⊗ᴾ-comma-fst (Πᴾ M P) (Σᴾ _ Q) p (m , q) = ⊗ᴾ-comma-fst (Πᴾ _ P) (Q m) p q
  ⊗ᴾ-comma-fst (Πᴾ M P) (Πᴾ N Q) p q       = λ= λ m → ⊗ᴾ-comma-fst (P m) (Πᴾ _ Q) (p m) q

  ⊗ᴾ-comma-snd : ∀ P Q (p : ⟦ P ⟧)(q : ⟦ Q ⟧) → ⊗ᴾ-snd P Q (commaᴾ {P} {Q} p q) ≡ q
  ⊗ᴾ-comma-snd end      Q        p q       = refl
  ⊗ᴾ-comma-snd (Σᴾ M P) Q        (m , p) q = ⊗ᴾ-comma-snd (P m) Q p q
  ⊗ᴾ-comma-snd (Πᴾ M P) end      p q       = refl
  ⊗ᴾ-comma-snd (Πᴾ M P) (Σᴾ _ Q) p (m , q) = pair= refl (⊗ᴾ-comma-snd (Πᴾ _ P) (Q m) p q)
  ⊗ᴾ-comma-snd (Πᴾ M P) (Πᴾ N Q) p q       = λ= λ m → ⊗ᴾ-comma-snd (Πᴾ M P) (Q m) p (q m)

  module _ P Q where
    ⊗→× : ⟦ P ⊗ᴾ Q ⟧ → ⟦ P ⟧ × ⟦ Q ⟧
    ⊗→× pq = ⊗ᴾ-fst P Q pq , ⊗ᴾ-snd P Q pq

    ×→⊗ : ⟦ P ⟧ × ⟦ Q ⟧ → ⟦ P ⊗ᴾ Q ⟧
    ×→⊗ (p , q) = commaᴾ {P} {Q} p q

    ×→⊗→× : ×→⊗ RightInverseOf ⊗→×
    ×→⊗→× = λ { (x , y) → pair×= (⊗ᴾ-comma-fst P Q x y) (⊗ᴾ-comma-snd P Q x y) }

    ⊗→×-has-rinv : Rinv ⊗→×
    ⊗→×-has-rinv = record { rinv = ×→⊗ ; is-rinv = ×→⊗→× }

  {- WRONG
  ⊗→×→⊗ : (×→⊗ P Q) LeftInverseOf (⊗→× P Q)
  ⊗≃×   : ⟦ P ⊗ᴾ Q ⟧ ≃ ⟦ P ⟧ × ⟦ Q ⟧
  ⟦⊗⟧≡× : P ⟦⊗⟧ Q ≡ (⟦ P ⟧ × ⟦ Q ⟧)
  -}

  switchL' : ∀ P Q R (pq : ⟦ P ⅋ᴾ Q ⟧) (r : ⟦ R ⟧) → ⟦ P ⅋ᴾ (Q ⊗ᴾ R) ⟧
  switchL' end      Q        R        q  r = commaᴾ {Q} {R} q r
  switchL' (Σᴾ _ P) end      R        p  r = par (Σᴾ _ P) R p r
  switchL' (Σᴾ _ P) (Σᴾ _ Q) R        (inl m , pq) r = inl m , switchL' (P m) (Σᴾ _ Q) R pq r
  switchL' (Σᴾ _ P) (Σᴾ _ Q) R        (inr m , pq) r = inr m , switchL' (Σᴾ _ P) (Q m) R pq r
  switchL' (Σᴾ _ P) (Πᴾ _ Q) end      pq r = pq
  switchL' (Σᴾ _ P) (Πᴾ _ Q) (Σᴾ _ R) pq (m , r) = inr m , switchL' (Σᴾ _ P) (Πᴾ _ Q) (R m) pq r
  switchL' (Σᴾ _ P) (Πᴾ _ Q) (Πᴾ _ R) pq r (inl m) = switchL' (Σᴾ _ P) (Q m) (Πᴾ _ R) (pq m) r
  switchL' (Σᴾ _ P) (Πᴾ _ Q) (Πᴾ _ R) pq r (inr m) = switchL' (Σᴾ _ P) (Πᴾ _ Q) (R m) pq (r m)
  switchL' (Πᴾ _ P) Q R pq r = λ m → switchL' (P m) Q R (pq m) r

  switchL : ∀ P Q R → ⟦ (P ⅋ᴾ Q) ⊗ᴾ R ⟧ → ⟦ P ⅋ᴾ (Q ⊗ᴾ R) ⟧
  switchL P Q R pqr = switchL' P Q R (⊗ᴾ-fst (P ⅋ᴾ Q) R pqr) (⊗ᴾ-snd (P ⅋ᴾ Q) R pqr)

  -- multiplicative mix (left-biased)
  mmix : ∀ P Q → ⟦ P ⊗ᴾ Q ⟧ → ⟦ P ⅋ᴾ Q ⟧
  mmix P Q pq = par P Q (⊗ᴾ-fst P Q pq) (⊗ᴾ-snd P Q pq)

  -- additive mix (left-biased)
  amix : ∀ P Q → ⟦ P &ᴾ Q ⟧ → ⟦ P ⊕ᴾ Q ⟧
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
CLL-proto `0       = Σᴾ 𝟘 λ()
CLL-proto `⊤       = Πᴾ 𝟘 λ()
CLL-proto (A `⊗ B) = CLL-proto A ⊗ᴾ CLL-proto B
CLL-proto (A `⅋ B) = CLL-proto A ⅋ᴾ CLL-proto B
CLL-proto (A `⊕ B) = CLL-proto A ⊕ᴾ CLL-proto B
CLL-proto (A `& B) = CLL-proto A &ᴾ CLL-proto B

{- The point of this could be to devise a particular equivalence
   relation for processes. It could properly deal with ⅋. -}

{-
module _ where
  trace : ∀ {B E} → Sim (Trace B) (Trace E) → Log B × Log E
  trace {end}   {end}   end = _
  trace {com _} {end}   (comL  (send m s)) = first  (_,_ m) (trace s)
  trace {end}   {com _} (comR (send m s)) = second (_,_ m) (trace s)
  trace {com _} {com c} (comL  (send m s)) = first  (_,_ m) (trace {E = com c} s)
  trace {com c} {com _} (comR (send m s)) = second (_,_ m) (trace {com c} s)

  module _ {P Q} where
    _≈_ : (PQ PQ' : Sim P Q) → ★₁
    PQ ≈ PQ' = ∀ {B P' Q' E} → (P'-P : Dual P' P)(Q-Q' : Dual Q Q')(BP : Sim (Trace B) P')(QE : Sim Q' (Trace E))
       → trace (sim-comp P'-P BP (sim-comp Q-Q' PQ QE)) ≡ trace (sim-comp P'-P BP (sim-comp Q-Q' PQ' QE))
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
