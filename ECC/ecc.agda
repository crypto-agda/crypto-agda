open import Relation.Binary.PropositionalEquality.NP
open import Data.Two.Base
open import Data.List
open import Function
open import Algebra.FunctionProperties.Eq
open Implicits
open import Algebra.Monoid.Commutative
open import Algebra.Ring

module ecc
  {𝔽 : Set} (𝔽-ring : Ring 𝔽)
  {ℙ : Set} (ℙ-monoid : Commutative-Monoid ℙ)
  where

open module 𝔽 = Ring 𝔽-ring

open module ⊕ = Commutative-Monoid ℙ-monoid
  renaming
    ( _∙_ to _⊕_
    ; ∙= to ⊕=
    ; ε∙-identity to ε⊕-identity
    ; ∙ε-identity to ⊕ε-identity
    ; _² to 2·_
    )

2·-⊕-distr : ∀ {P Q} → 2· (P ⊕ Q) ≡ 2· P ⊕ 2· Q
2·-⊕-distr = ⊕.interchange

2·-⊕ : ∀ {P Q R} → 2· P ⊕ (Q ⊕ R) ≡ (P ⊕ Q) ⊕ (P ⊕ R)
2·-⊕ = ⊕.interchange

-- NOT used yet
multiply-bin : List 𝟚 → ℙ → ℙ
multiply-bin scalar P = go scalar
  where
    go : List 𝟚 → ℙ
    go []       = P
    go (b ∷ bs) = [0: x₀ 1: x₁ ] b
      where x₀ = 2· go bs
            x₁ = P ⊕ x₀

{-
multiply : 𝔽 → ℙ → ℙ
multiply scalar P =
  -- if scalar == 0 or scalar >= N: raise Exception("Invalid Scalar/Private Key")
    multiply-bin (bin scalar) P

_·_ = multiply
infixr 8 _·_
-}

infixl 7 1+2*_
1+2*_ = λ x → 1+ 2* x

data Parity-View : 𝔽 → Set where
  zero⟨_⟩    : ∀ {n} → n ≡ 0# → Parity-View n
  even_by⟨_⟩ : ∀ {m n} → Parity-View m → n ≡ 2* m    → Parity-View n
  odd_by⟨_⟩  : ∀ {m n} → Parity-View m → n ≡ 1+ 2* m → Parity-View n

cast_by⟨_⟩ : ∀ {x y} → Parity-View x → y ≡ x → Parity-View y
cast zero⟨ xₑ ⟩       by⟨ yₑ ⟩ = zero⟨ yₑ ∙ xₑ ⟩
cast even xₚ by⟨ xₑ ⟩ by⟨ yₑ ⟩ = even xₚ by⟨ yₑ ∙ xₑ ⟩
cast odd  xₚ by⟨ xₑ ⟩ by⟨ yₑ ⟩ = odd  xₚ by⟨ yₑ ∙ xₑ ⟩

infixr 8 _·ₚ_
_·ₚ_ : ∀ {n} (p : Parity-View n) → ℙ → ℙ
zero⟨ e ⟩      ·ₚ P = ε
even p by⟨ e ⟩ ·ₚ P = 2· (p ·ₚ P)
odd  p by⟨ e ⟩ ·ₚ P = P ⊕ (2· (p ·ₚ P))

_+2*_ : 𝟚 → 𝔽 → 𝔽
0₂ +2* m =   2* m
1₂ +2* m = 1+2* m

{-
postulate
    bin-2* : ∀ {n} → bin (2* n) ≡ 0₂ ∷ bin n
    bin-1+2* : ∀ {n} → bin (1+2* n) ≡ 1₂ ∷ bin n

bin-+2* : (b : 𝟚)(n : 𝔽) → bin (b +2* n) ≡ b ∷ bin n
bin-+2* 1₂ n = bin-1+2*
bin-+2* 0₂ n = bin-2*
-}

-- (msb) most significant bit first
binₚ : ∀ {n} → Parity-View n → List 𝟚
binₚ zero⟨ e ⟩      = []
binₚ even p by⟨ e ⟩ = 0₂ ∷ binₚ p
binₚ odd  p by⟨ e ⟩ = 1₂ ∷ binₚ p

half : ∀ {n} → Parity-View n → 𝔽
half zero⟨ _ ⟩            = 0#
half (even_by⟨_⟩ {m} _ _) = m
half (odd_by⟨_⟩  {m} _ _) = m

{-
bin-parity : ∀ {n} (p : ParityView n) → bin n ≡ parity p ∷ bin (half p)
bin-parity (even n) = bin-2*
bin-parity (odd n)  = bin-1+2*
-}

infixl 6 1+ₚ_ _+ₚ_
1+ₚ_ : ∀ {x} → Parity-View x → Parity-View (1+ x)
1+ₚ zero⟨ e ⟩      = odd zero⟨ refl ⟩ by⟨ ap 1+_ (e ∙ ! 0+-identity) ⟩
1+ₚ even p by⟨ e ⟩ = odd p      by⟨ ap 1+_ e ⟩
1+ₚ odd  p by⟨ e ⟩ = even 1+ₚ p by⟨ ap 1+_ e ∙ ! +-assoc ∙ +-interchange ⟩

_+ₚ_ : ∀ {x y} → Parity-View x → Parity-View y → Parity-View (x + y)
zero⟨ xₑ ⟩       +ₚ yₚ        = cast yₚ by⟨ ap (λ z → z + _) xₑ ∙ 0+-identity ⟩
xₚ              +ₚ zero⟨ yₑ ⟩ = cast xₚ by⟨ ap (_+_ _) yₑ ∙ +-comm ∙ 0+-identity ⟩
even xₚ by⟨ xₑ ⟩ +ₚ even yₚ by⟨ yₑ ⟩ = even     xₚ +ₚ yₚ by⟨ += xₑ yₑ ∙ +-interchange ⟩
even xₚ by⟨ xₑ ⟩ +ₚ odd  yₚ by⟨ yₑ ⟩ = odd      xₚ +ₚ yₚ by⟨ += xₑ yₑ ∙ +-comm ∙ +-assoc ∙ ap 1+_ (+-comm ∙ +-interchange) ⟩
odd  xₚ by⟨ xₑ ⟩ +ₚ even yₚ by⟨ yₑ ⟩ = odd      xₚ +ₚ yₚ by⟨ += xₑ yₑ ∙ +-assoc ∙ ap 1+_ +-interchange ⟩
odd  xₚ by⟨ xₑ ⟩ +ₚ odd  yₚ by⟨ yₑ ⟩ = even 1+ₚ (xₚ +ₚ yₚ) by⟨ += xₑ yₑ ∙ +-on-sides refl +-interchange ⟩

infixl 7 2*ₚ_
2*ₚ_ : ∀ {x} → Parity-View x → Parity-View (2* x)
2*ₚ xₚ = xₚ +ₚ xₚ

open ≡-Reasoning

module _ {P Q} where
    ·ₚ-⊕-distr : ∀ {x} (xₚ : Parity-View x) → xₚ ·ₚ (P ⊕ Q) ≡ xₚ ·ₚ P ⊕ xₚ ·ₚ Q
    ·ₚ-⊕-distr zero⟨ xₑ ⟩       = ! ε⊕-identity
    ·ₚ-⊕-distr even xₚ by⟨ xₑ ⟩ = ap 2·_ (·ₚ-⊕-distr xₚ) ∙ 2·-⊕-distr
    ·ₚ-⊕-distr odd  xₚ by⟨ xₑ ⟩ = ap (λ z → P ⊕ Q ⊕ 2· z) (·ₚ-⊕-distr xₚ)
                               ∙ ap (λ z → P ⊕ Q ⊕ z) (! 2·-⊕)
                               ∙ ⊕.interchange

module _ {P} where
    cast-·ₚ-distr : ∀ {x y} (xₚ : Parity-View x) (yₑ : y ≡ x) → cast xₚ by⟨ yₑ ⟩ ·ₚ P ≡ xₚ ·ₚ P
    cast-·ₚ-distr zero⟨ x₁ ⟩ yₑ = refl
    cast-·ₚ-distr even xₚ by⟨ x₁ ⟩ yₑ = refl
    cast-·ₚ-distr odd xₚ by⟨ x₁ ⟩ yₑ = refl

    1+ₚ-·ₚ-distr : ∀ {x} (xₚ : Parity-View x) → (1+ₚ xₚ) ·ₚ P ≡ P ⊕ xₚ ·ₚ P
    1+ₚ-·ₚ-distr zero⟨ xₑ ⟩       = ap (_⊕_ P) ε⊕-identity
    1+ₚ-·ₚ-distr even xₚ by⟨ xₑ ⟩ = refl
    1+ₚ-·ₚ-distr odd  xₚ by⟨ xₑ ⟩ = ap 2·_ (1+ₚ-·ₚ-distr xₚ) ∙ ⊕.interchange ∙ ⊕.assoc

    +ₚ-·ₚ-distr : ∀ {x y} (xₚ : Parity-View x) (yₚ : Parity-View y)
                 → (xₚ +ₚ yₚ) ·ₚ P ≡ xₚ ·ₚ P ⊕ yₚ ·ₚ P
    +ₚ-·ₚ-distr zero⟨ xₑ ⟩ yₚ = cast-·ₚ-distr yₚ _ ∙ ! ε⊕-identity

    +ₚ-·ₚ-distr even xₚ by⟨ xₑ ⟩ zero⟨ yₑ ⟩ = ! ⊕ε-identity
    +ₚ-·ₚ-distr odd  xₚ by⟨ xₑ ⟩ zero⟨ yₑ ⟩ = ! ⊕ε-identity

    +ₚ-·ₚ-distr even xₚ by⟨ xₑ ⟩ even yₚ by⟨ yₑ ⟩ = ap 2·_ (+ₚ-·ₚ-distr xₚ yₚ) ∙ 2·-⊕-distr
    +ₚ-·ₚ-distr even xₚ by⟨ xₑ ⟩ odd  yₚ by⟨ yₑ ⟩ = ap (_⊕_ P) (ap 2·_ (+ₚ-·ₚ-distr xₚ yₚ) ∙ 2·-⊕-distr) ∙ ⊕.assoc-comm
    +ₚ-·ₚ-distr odd  xₚ by⟨ xₑ ⟩ even yₚ by⟨ yₑ ⟩ = ap (_⊕_ P) (ap 2·_ (+ₚ-·ₚ-distr xₚ yₚ) ∙ 2·-⊕-distr) ∙ ! ⊕.assoc
    +ₚ-·ₚ-distr odd  xₚ by⟨ xₑ ⟩ odd  yₚ by⟨ yₑ ⟩
       = (odd xₚ by⟨ xₑ ⟩ +ₚ odd yₚ by⟨ yₑ ⟩) ·ₚ P
       ≡⟨by-definition⟩
         2·((1+ₚ (xₚ +ₚ yₚ)) ·ₚ P)
       ≡⟨ ap 2·_ helper ⟩
         2·(P ⊕ (xₚ ·ₚ P ⊕ yₚ ·ₚ P))
       ≡⟨ 2·-⊕-distr ⟩
         2· P ⊕ (2·(xₚ ·ₚ P ⊕ yₚ ·ₚ P))
       ≡⟨ ap (_⊕_ (2· P)) 2·-⊕-distr ⟩
         2· P ⊕ (2·(xₚ ·ₚ P) ⊕ 2·(yₚ ·ₚ P))
       ≡⟨ 2·-⊕ ⟩
         P ⊕ 2·(xₚ ·ₚ P) ⊕ (P ⊕ 2·(yₚ ·ₚ P))
       ≡⟨by-definition⟩
         odd xₚ by⟨ xₑ ⟩ ·ₚ P ⊕ odd yₚ by⟨ yₑ ⟩ ·ₚ P
       ∎
        where helper = (1+ₚ (xₚ +ₚ yₚ)) ·ₚ P
                     ≡⟨ 1+ₚ-·ₚ-distr (xₚ +ₚ yₚ) ⟩
                       P ⊕ ((xₚ +ₚ yₚ) ·ₚ P)
                     ≡⟨ ap (_⊕_ P) (+ₚ-·ₚ-distr xₚ yₚ) ⟩
                       P ⊕ (xₚ ·ₚ P ⊕ yₚ ·ₚ P)
                     ∎

*-1+-distr : ∀ {x y} → x * (1+ y) ≡ x + x * y
*-1+-distr = *-+-distrˡ ∙ += *1-identity refl

1+-*-distr : ∀ {x y} → (1+ x) * y ≡ y + x * y
1+-*-distr = *-+-distrʳ ∙ += 1*-identity refl

infixl 7 _*ₚ_
_*ₚ_ : ∀ {x y} → Parity-View x → Parity-View y → Parity-View (x * y)
zero⟨ xₑ ⟩       *ₚ yₚ              = zero⟨ *= xₑ refl ∙ 0*-zero ⟩
xₚ              *ₚ zero⟨ yₑ ⟩       = zero⟨ *= refl yₑ ∙ *0-zero ⟩
even xₚ by⟨ xₑ ⟩ *ₚ yₚ              = even (xₚ *ₚ yₚ) by⟨ *= xₑ refl ∙ *-+-distrʳ ⟩
xₚ              *ₚ even yₚ by⟨ yₑ ⟩ = even (xₚ *ₚ yₚ) by⟨ *= refl yₑ ∙ *-+-distrˡ ⟩
odd xₚ by⟨ xₑ ⟩  *ₚ odd yₚ by⟨ yₑ ⟩  = odd  (xₚ +ₚ yₚ +ₚ 2*ₚ (xₚ *ₚ yₚ)) by⟨ *= xₑ yₑ ∙ helper ⟩
   where
     x = _
     y = _
     helper = (1+2* x)*(1+2* y)
            ≡⟨ 1+-*-distr ⟩
              1+2* y + 2* x * 1+2* y
            ≡⟨ ap (λ z → 1+2* y + z)
                 (2* x * 1+2* y
                 ≡⟨ *-1+-distr ⟩
                 (2* x + 2* x * 2* y)
                 ≡⟨ += refl *-+-distrˡ ∙ +-interchange ⟩
                 (2* (x + 2* x * y))
                 ∎) ⟩
              1+2* y + 2* (x + 2* x * y)
            ≡⟨ +-assoc ∙ ap 1+_ +-interchange ⟩
              1+2*(y + (x + 2* x * y))
            ≡⟨ ap 1+2*_ (! +-assoc ∙ += +-comm refl) ⟩
              1+2*(x + y + 2* x * y)
            ≡⟨ ap (λ z → 1+2*(x + y + z)) *-+-distrʳ ⟩
              1+2*(x + y + 2* (x * y))
            ∎

module _ {P} where
    2·-·ₚ-distr : ∀ {x} (xₚ : Parity-View x) → 2·(xₚ ·ₚ P) ≡ xₚ ·ₚ 2· P
    2·-·ₚ-distr xₚ = ! ·ₚ-⊕-distr xₚ

    2*ₚ-·ₚ-distr : ∀ {x} (xₚ : Parity-View x) → (2*ₚ xₚ) ·ₚ P ≡ 2·(xₚ ·ₚ P)
    2*ₚ-·ₚ-distr xₚ = +ₚ-·ₚ-distr xₚ xₚ

·ₚ-ε : ∀ {x} (xₚ : Parity-View x) → xₚ ·ₚ ε ≡ ε
·ₚ-ε zero⟨ xₑ ⟩       = refl
·ₚ-ε even xₚ by⟨ xₑ ⟩ = ap 2·_ (·ₚ-ε xₚ) ∙ ε⊕-identity
·ₚ-ε odd xₚ by⟨ xₑ ⟩  = ε⊕-identity ∙ ap 2·_ (·ₚ-ε xₚ) ∙ ε⊕-identity

*ₚ-·ₚ-distr : ∀ {x y} (xₚ : Parity-View x) (yₚ : Parity-View y) {P} → (xₚ *ₚ yₚ) ·ₚ P ≡ xₚ ·ₚ yₚ ·ₚ P
*ₚ-·ₚ-distr zero⟨ xₑ ⟩ yₚ = refl
*ₚ-·ₚ-distr even xₚ by⟨ xₑ ⟩ zero⟨ yₑ ⟩ = ! ·ₚ-ε even xₚ by⟨ xₑ ⟩
*ₚ-·ₚ-distr odd  xₚ by⟨ xₑ ⟩ zero⟨ yₑ ⟩ = ! ·ₚ-ε odd  xₚ by⟨ xₑ ⟩

*ₚ-·ₚ-distr even xₚ by⟨ xₑ ⟩ even yₚ by⟨ yₑ ⟩ = ap 2·_ (*ₚ-·ₚ-distr xₚ even yₚ by⟨ yₑ ⟩)
*ₚ-·ₚ-distr even xₚ by⟨ xₑ ⟩ odd  yₚ by⟨ yₑ ⟩ = ap 2·_ (*ₚ-·ₚ-distr xₚ odd  yₚ by⟨ yₑ ⟩)

*ₚ-·ₚ-distr odd  xₚ by⟨ xₑ ⟩ even yₚ by⟨ yₑ ⟩ {P} =
   ap 2·_ (*ₚ-·ₚ-distr odd xₚ by⟨ xₑ ⟩ yₚ) ∙ 2·-⊕-distr ∙ ap (λ z → 2· (yₚ ·ₚ P) ⊕ 2· z) (2·-·ₚ-distr xₚ)
*ₚ-·ₚ-distr odd  xₚ by⟨ xₑ ⟩ odd  yₚ by⟨ yₑ ⟩ {P} =
   ap (_⊕_ P)
     (ap 2·_
        (+ₚ-·ₚ-distr (xₚ +ₚ yₚ) (2*ₚ (xₚ *ₚ yₚ))
        ∙ ⊕= (+ₚ-·ₚ-distr xₚ yₚ) (2*ₚ-·ₚ-distr (xₚ *ₚ yₚ))
        ∙ ⊕= ⊕.comm (ap 2·_ (*ₚ-·ₚ-distr xₚ yₚ) ∙ 2·-·ₚ-distr xₚ) ∙ ⊕.assoc
        ∙ ⊕= refl (! ·ₚ-⊕-distr xₚ) ) ∙ 2·-⊕-distr)
     ∙ ⊕.!assoc
-- -}
-- -}
-- -}
-- -}
