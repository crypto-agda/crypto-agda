--open import prelude renaming (Bool to 𝟚; true to 1₂; false to 0₂)
open import Relation.Binary.PropositionalEquality.NP
open import Data.Two
open import Data.List
open import Function
open import Algebra.FunctionProperties.Eq

module _ where

infixl 6 _+_ -- _-_
infixl 7 _*_ -- _%_
infixl 6 _+P_

postulate
  Number : Set
  _+_ _*_ : Number → Number → Number
 -- _-_ _/_ _%_ : Number → Number → Number
  -- Pcurve Acurve : Number
  0ₙ 1ₙ {-2ₙ 3ₙ-} : Number
  -- bin : Number → List 𝟚

  Point : Set
  _+P_ : Point → Point → Point
  +P-assoc : ∀ {P Q R} → (P +P Q) +P R ≡ P +P (Q +P R)
  +P-comm : ∀ {P Q} → P +P Q ≡ Q +P P

  0P : Point
  0P+-cancel : ∀ {x} → 0P +P x ≡ x

+0P-cancel : ∀ {x} → x +P 0P ≡ x
+0P-cancel = +P-comm ∙ 0P+-cancel

2·_ : Point → Point
2· P = P +P P

+P= : ∀ {x x' y y'} → x ≡ x' → y ≡ y' → x +P y ≡ x' +P y'
+P= {x} {y' = y'} p q = ap (_+P_ x) q ∙ ap (λ z → z +P y') p

+P-interchange : ∀ {x y z t} → (x +P y) +P (z +P t) ≡ (x +P z) +P (y +P t)
+P-interchange = InterchangeFromAssocComm.·-interchange _+P_ +P-assoc +P-comm

2·-+P-2· : ∀ {P Q} → 2· (P +P Q) ≡ 2· P +P 2· Q
2·-+P-2· = +P-interchange

+P-comm-2of3 : ∀ {P Q R} → P +P (Q +P R) ≡ Q +P (P +P R)
+P-comm-2of3 = ! +P-assoc ∙ +P= +P-comm refl ∙ +P-assoc

2·-+P : ∀ {P Q R} → 2· P +P (Q +P R) ≡ (P +P Q) +P (P +P R)
2·-+P = +P-interchange
 
{-
ec-multiply-bin : List 𝟚 → Point → Point
ec-multiply-bin scalar P = go scalar
  where
    go : List 𝟚 → Point
    go []       = P
    go (b ∷ bs) = [0: x₀ 1: x₁ ] b
      where x₀ = 2· go bs
            x₁ = P +P x₀

ec-multiply : Number → Point → Point
ec-multiply scalar P =
  -- if scalar == 0 or scalar >= N: raise Exception("Invalid Scalar/Private Key")
    ec-multiply-bin (bin scalar) P

_·_ = ec-multiply
infixr 8 _·_
-}

infixl 6 1+_
infixl 7 2*_ 1+2*_
1+_ = λ x → 1ₙ + x
2*_ = λ x → x + x
1+2*_ = λ x → 1+ 2* x

data Parity-View : Number → Set where
  zero⟨_⟩    : ∀ {n} → n ≡ 0ₙ → Parity-View n
  even_by⟨_⟩ : ∀ {m n} → Parity-View m → n ≡ 2* m    → Parity-View n
  odd_by⟨_⟩  : ∀ {m n} → Parity-View m → n ≡ 1+ 2* m → Parity-View n

cast_by⟨_⟩ : ∀ {x y} → Parity-View x → y ≡ x → Parity-View y
cast zero⟨ xₑ ⟩       by⟨ yₑ ⟩ = zero⟨ yₑ ∙ xₑ ⟩
cast even xₚ by⟨ xₑ ⟩ by⟨ yₑ ⟩ = even xₚ by⟨ yₑ ∙ xₑ ⟩
cast odd  xₚ by⟨ xₑ ⟩ by⟨ yₑ ⟩ = odd  xₚ by⟨ yₑ ∙ xₑ ⟩

infixr 8 _·ₚ_
_·ₚ_ : ∀ {n} (p : Parity-View n) → Point → Point
zero⟨ e ⟩      ·ₚ P = 0P
even p by⟨ e ⟩ ·ₚ P = 2· (p ·ₚ P)
odd  p by⟨ e ⟩ ·ₚ P = P +P (2· (p ·ₚ P))

+= : ∀ {x x' y y'} → x ≡ x' → y ≡ y' → x + y ≡ x' + y'
+= {x} {y' = y'} p q = ap (_+_ x) q ∙ ap (λ z → z + y') p

*= : ∀ {x x' y y'} → x ≡ x' → y ≡ y' → x * y ≡ x' * y'
*= {x} {y' = y'} p q = ap (_*_ x) q ∙ ap (λ z → z * y') p

module Addₚ
       (+-assoc : ∀ {x y z} → (x + y) + z ≡ x + (y + z))
       (+-comm : ∀ {x y} → x + y ≡ y + x)
       (0+-cancel : ∀ {x} → 0ₙ + x ≡ x)
       where

    +-interchange : ∀ {x y z t} → (x + y) + (z + t) ≡ (x + z) + (y + t)
    +-interchange = InterchangeFromAssocComm.·-interchange _+_ +-assoc +-comm

    +-on-sides : ∀ {x x' y y' z z' t t'}
                 → x + z ≡ x' + z'
                 → y + t ≡ y' + t'
                 → (x + y) + (z + t) ≡ (x' + y') + (z' + t')
    +-on-sides p q = +-interchange ∙ += p q ∙ +-interchange

    -- only needs interchange and comm
    {- UNUSED
    +-inner : ∀ {x y y' z z' t} → y + z ≡ z' + y' → (x + y) + (z + t) ≡ (x + y') + (z' + t)
    +-inner p = += +-comm refl ∙ +-on-sides (p ∙ +-comm) refl ∙ += +-comm refl
    -}

    _+2*_ : 𝟚 → Number → Number
    0₂ +2* m =   2* m
    1₂ +2* m = 1+2* m

    {-
    postulate
        bin-2* : ∀ {n} → bin (2* n) ≡ 0₂ ∷ bin n
        bin-1+2* : ∀ {n} → bin (1+2* n) ≡ 1₂ ∷ bin n

    bin-+2* : (b : 𝟚)(n : Number) → bin (b +2* n) ≡ b ∷ bin n
    bin-+2* 1₂ n = bin-1+2*
    bin-+2* 0₂ n = bin-2*
    -}

    -- (msb) most significant bit first
    binₚ : ∀ {n} → Parity-View n → List 𝟚
    binₚ zero⟨ e ⟩      = []
    binₚ even p by⟨ e ⟩ = 0₂ ∷ binₚ p
    binₚ odd  p by⟨ e ⟩ = 1₂ ∷ binₚ p

    half : ∀ {n} → Parity-View n → Number
    half zero⟨ _ ⟩            = 0ₙ
    half (even_by⟨_⟩ {m} _ _) = m
    half (odd_by⟨_⟩  {m} _ _) = m

    {-
    bin-parity : ∀ {n} (p : ParityView n) → bin n ≡ parity p ∷ bin (half p)
    bin-parity (even n) = bin-2*
    bin-parity (odd n)  = bin-1+2*
    -}

    infixl 6 1+ₚ_ _+ₚ_
    1+ₚ_ : ∀ {x} → Parity-View x → Parity-View (1+ x)
    1+ₚ zero⟨ e ⟩      = odd zero⟨ refl ⟩ by⟨ ap 1+_ (e ∙ ! 0+-cancel) ⟩
    1+ₚ even p by⟨ e ⟩ = odd p      by⟨ ap 1+_ e ⟩
    1+ₚ odd  p by⟨ e ⟩ = even 1+ₚ p by⟨ ap 1+_ e ∙ ! +-assoc ∙ +-interchange ⟩

    _+ₚ_ : ∀ {x y} → Parity-View x → Parity-View y → Parity-View (x + y)
    zero⟨ xₑ ⟩       +ₚ yₚ        = cast yₚ by⟨ ap (λ z → z + _) xₑ ∙ 0+-cancel ⟩
    xₚ              +ₚ zero⟨ yₑ ⟩ = cast xₚ by⟨ ap (_+_ _) yₑ ∙ +-comm ∙ 0+-cancel ⟩
    even xₚ by⟨ xₑ ⟩ +ₚ even yₚ by⟨ yₑ ⟩ = even     xₚ +ₚ yₚ by⟨ += xₑ yₑ ∙ +-interchange ⟩
    even xₚ by⟨ xₑ ⟩ +ₚ odd  yₚ by⟨ yₑ ⟩ = odd      xₚ +ₚ yₚ by⟨ += xₑ yₑ ∙ +-comm ∙ +-assoc ∙ ap 1+_ (+-comm ∙ +-interchange) ⟩
    odd  xₚ by⟨ xₑ ⟩ +ₚ even yₚ by⟨ yₑ ⟩ = odd      xₚ +ₚ yₚ by⟨ += xₑ yₑ ∙ +-assoc ∙ ap 1+_ +-interchange ⟩
    odd  xₚ by⟨ xₑ ⟩ +ₚ odd  yₚ by⟨ yₑ ⟩ = even 1+ₚ (xₚ +ₚ yₚ) by⟨ += xₑ yₑ ∙ +-on-sides refl +-interchange ⟩

    infixl 7 2*ₚ_
    2*ₚ_ : ∀ {x} → Parity-View x → Parity-View (2* x)
    2*ₚ xₚ = xₚ +ₚ xₚ

    open ≡-Reasoning

    module _ {P Q} where
        ·ₚ-+P-distr : ∀ {x} (xₚ : Parity-View x) → xₚ ·ₚ (P +P Q) ≡ xₚ ·ₚ P +P xₚ ·ₚ Q
        ·ₚ-+P-distr zero⟨ xₑ ⟩       = ! 0P+-cancel
        ·ₚ-+P-distr even xₚ by⟨ xₑ ⟩ = ap 2·_ (·ₚ-+P-distr xₚ) ∙ 2·-+P-2·
        ·ₚ-+P-distr odd  xₚ by⟨ xₑ ⟩ = ap (λ z → P +P Q +P 2· z) (·ₚ-+P-distr xₚ)
                                   ∙ ap (λ z → P +P Q +P z) (! 2·-+P)
                                   ∙ +P-interchange

    module _ {P} where
        cast-·ₚ-distr : ∀ {x y} (xₚ : Parity-View x) (yₑ : y ≡ x) → cast xₚ by⟨ yₑ ⟩ ·ₚ P ≡ xₚ ·ₚ P
        cast-·ₚ-distr zero⟨ x₁ ⟩ yₑ = refl
        cast-·ₚ-distr even xₚ by⟨ x₁ ⟩ yₑ = refl
        cast-·ₚ-distr odd xₚ by⟨ x₁ ⟩ yₑ = refl
    
        1+ₚ-·ₚ-distr : ∀ {x} (xₚ : Parity-View x) → (1+ₚ xₚ) ·ₚ P ≡ P +P xₚ ·ₚ P
        1+ₚ-·ₚ-distr zero⟨ xₑ ⟩       = ap (_+P_ P) 0P+-cancel
        1+ₚ-·ₚ-distr even xₚ by⟨ xₑ ⟩ = refl
        1+ₚ-·ₚ-distr odd  xₚ by⟨ xₑ ⟩ = ap 2·_ (1+ₚ-·ₚ-distr xₚ) ∙ +P-interchange ∙ +P-assoc

        +ₚ-·ₚ-distr : ∀ {x y} (xₚ : Parity-View x) (yₚ : Parity-View y)
                     → (xₚ +ₚ yₚ) ·ₚ P ≡ xₚ ·ₚ P +P yₚ ·ₚ P
        +ₚ-·ₚ-distr zero⟨ xₑ ⟩ yₚ = cast-·ₚ-distr yₚ _ ∙ ! 0P+-cancel

        +ₚ-·ₚ-distr even xₚ by⟨ xₑ ⟩ zero⟨ yₑ ⟩ = ! +0P-cancel
        +ₚ-·ₚ-distr odd  xₚ by⟨ xₑ ⟩ zero⟨ yₑ ⟩ = ! +0P-cancel

        +ₚ-·ₚ-distr even xₚ by⟨ xₑ ⟩ even yₚ by⟨ yₑ ⟩ = ap 2·_ (+ₚ-·ₚ-distr xₚ yₚ) ∙ 2·-+P-2·
        +ₚ-·ₚ-distr even xₚ by⟨ xₑ ⟩ odd  yₚ by⟨ yₑ ⟩ = ap (_+P_ P) (ap 2·_ (+ₚ-·ₚ-distr xₚ yₚ) ∙ 2·-+P-2·) ∙ +P-comm-2of3
        +ₚ-·ₚ-distr odd  xₚ by⟨ xₑ ⟩ even yₚ by⟨ yₑ ⟩ = ap (_+P_ P) (ap 2·_ (+ₚ-·ₚ-distr xₚ yₚ) ∙ 2·-+P-2·) ∙ ! +P-assoc
        +ₚ-·ₚ-distr odd  xₚ by⟨ xₑ ⟩ odd  yₚ by⟨ yₑ ⟩
           = (odd xₚ by⟨ xₑ ⟩ +ₚ odd yₚ by⟨ yₑ ⟩) ·ₚ P
           ≡⟨by-definition⟩
             2·((1+ₚ (xₚ +ₚ yₚ)) ·ₚ P)
           ≡⟨ ap 2·_ helper ⟩
             2·(P +P (xₚ ·ₚ P +P yₚ ·ₚ P))
           ≡⟨ 2·-+P-2· ⟩
             2· P +P (2·(xₚ ·ₚ P +P yₚ ·ₚ P))
           ≡⟨ ap (_+P_ (2· P)) 2·-+P-2· ⟩
             2· P +P (2·(xₚ ·ₚ P) +P 2·(yₚ ·ₚ P))
           ≡⟨ 2·-+P ⟩
             P +P 2·(xₚ ·ₚ P) +P (P +P 2·(yₚ ·ₚ P))
           ≡⟨by-definition⟩
             odd xₚ by⟨ xₑ ⟩ ·ₚ P +P odd yₚ by⟨ yₑ ⟩ ·ₚ P
           ∎
            where helper = (1+ₚ (xₚ +ₚ yₚ)) ·ₚ P
                         ≡⟨ 1+ₚ-·ₚ-distr (xₚ +ₚ yₚ) ⟩
                           P +P ((xₚ +ₚ yₚ) ·ₚ P)
                         ≡⟨ ap (_+P_ P) (+ₚ-·ₚ-distr xₚ yₚ) ⟩
                           P +P (xₚ ·ₚ P +P yₚ ·ₚ P)
                         ∎

    module Multₚ
       (+-*-distr : ∀ {x y z} → (x + y) * z ≡ x * z + y * z)
       (*-+-distr : ∀ {x y z} → x * (y + z) ≡ x * y + x * z)
       (1*-cancel : ∀ {x} → 1ₙ * x ≡ x)
       (*1-cancel : ∀ {x} → x * 1ₙ ≡ x)
       (0*-cancel : ∀ {x} → 0ₙ * x ≡ 0ₙ)
       (*0-cancel : ∀ {x} → x * 0ₙ ≡ 0ₙ)
       --(modinv-*-distr : ∀ {x y} → modinv (x * y) ≡ modinv x * modinv y)
       --(modinv-modinv : ∀ {x} → modinv (modinv x) ≡ x)
       --(*-assoc : ∀ {x y z} → (x * y) * z ≡ x * (y * z))
       --(*-comm : ∀ {x y} → x * y ≡ y * x)
       --(modinv-cancel : ∀ {x y} → x * modinv x * y ≡ y)
       --(2*1ₙ : 2* 1ₙ ≡ 2ₙ)
       --(2*-spec : ∀ {n} → 2* n ≡ 2ₙ * n)
       where

        *-1+-distr : ∀ {x y} → x * (1+ y) ≡ x + x * y
        *-1+-distr = *-+-distr ∙ += *1-cancel refl

        1+-*-distr : ∀ {x y} → (1+ x) * y ≡ y + x * y
        1+-*-distr = +-*-distr ∙ += 1*-cancel refl

        infixl 7 _*ₚ_
        _*ₚ_ : ∀ {x y} → Parity-View x → Parity-View y → Parity-View (x * y)
        zero⟨ xₑ ⟩       *ₚ yₚ              = zero⟨ *= xₑ refl ∙ 0*-cancel ⟩
        xₚ              *ₚ zero⟨ yₑ ⟩       = zero⟨ *= refl yₑ ∙ *0-cancel ⟩
        even xₚ by⟨ xₑ ⟩ *ₚ yₚ              = even (xₚ *ₚ yₚ) by⟨ *= xₑ refl ∙ +-*-distr ⟩
        xₚ              *ₚ even yₚ by⟨ yₑ ⟩ = even (xₚ *ₚ yₚ) by⟨ *= refl yₑ ∙ *-+-distr ⟩
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
                         ≡⟨ += refl *-+-distr ∙ +-interchange ⟩
                         (2* (x + 2* x * y))
                         ∎) ⟩
                      1+2* y + 2* (x + 2* x * y)
                    ≡⟨ +-assoc ∙ ap 1+_ +-interchange ⟩
                      1+2*(y + (x + 2* x * y))
                    ≡⟨ ap 1+2*_ (! +-assoc ∙ += +-comm refl) ⟩
                      1+2*(x + y + 2* x * y)
                    ≡⟨ ap (λ z → 1+2*(x + y + z)) +-*-distr ⟩
                      1+2*(x + y + 2* (x * y))
                    ∎

        module _ {P} where
            2·-·ₚ-distr : ∀ {x} (xₚ : Parity-View x) → 2·(xₚ ·ₚ P) ≡ xₚ ·ₚ 2· P
            2·-·ₚ-distr xₚ = ! ·ₚ-+P-distr xₚ

            2*ₚ-·ₚ-distr : ∀ {x} (xₚ : Parity-View x) → (2*ₚ xₚ) ·ₚ P ≡ 2·(xₚ ·ₚ P)
            2*ₚ-·ₚ-distr xₚ = +ₚ-·ₚ-distr xₚ xₚ

        ·ₚ-0P : ∀ {x} (xₚ : Parity-View x) → xₚ ·ₚ 0P ≡ 0P
        ·ₚ-0P zero⟨ xₑ ⟩       = refl
        ·ₚ-0P even xₚ by⟨ xₑ ⟩ = ap 2·_ (·ₚ-0P xₚ) ∙ 0P+-cancel
        ·ₚ-0P odd xₚ by⟨ xₑ ⟩  = 0P+-cancel ∙ ap 2·_ (·ₚ-0P xₚ) ∙ 0P+-cancel

        *ₚ-·ₚ-distr : ∀ {x y} (xₚ : Parity-View x) (yₚ : Parity-View y) {P} → (xₚ *ₚ yₚ) ·ₚ P ≡ xₚ ·ₚ yₚ ·ₚ P
        *ₚ-·ₚ-distr zero⟨ xₑ ⟩ yₚ = refl
        *ₚ-·ₚ-distr even xₚ by⟨ xₑ ⟩ zero⟨ yₑ ⟩ = ! ·ₚ-0P even xₚ by⟨ xₑ ⟩
        *ₚ-·ₚ-distr odd  xₚ by⟨ xₑ ⟩ zero⟨ yₑ ⟩ = ! ·ₚ-0P odd  xₚ by⟨ xₑ ⟩

        *ₚ-·ₚ-distr even xₚ by⟨ xₑ ⟩ even yₚ by⟨ yₑ ⟩ = ap 2·_ (*ₚ-·ₚ-distr xₚ even yₚ by⟨ yₑ ⟩)
        *ₚ-·ₚ-distr even xₚ by⟨ xₑ ⟩ odd  yₚ by⟨ yₑ ⟩ = ap 2·_ (*ₚ-·ₚ-distr xₚ odd  yₚ by⟨ yₑ ⟩)

        *ₚ-·ₚ-distr odd  xₚ by⟨ xₑ ⟩ even yₚ by⟨ yₑ ⟩ {P} = ap 2·_ (*ₚ-·ₚ-distr odd xₚ by⟨ xₑ ⟩ yₚ) ∙ 2·-+P-2· ∙ ap (λ z → 2· (yₚ ·ₚ P) +P 2· z) (2·-·ₚ-distr xₚ)
        *ₚ-·ₚ-distr odd  xₚ by⟨ xₑ ⟩ odd  yₚ by⟨ yₑ ⟩ {P} =
           ap (_+P_ P)
             (ap 2·_
                (+ₚ-·ₚ-distr (xₚ +ₚ yₚ) (2*ₚ (xₚ *ₚ yₚ))
                ∙ +P= (+ₚ-·ₚ-distr xₚ yₚ) (2*ₚ-·ₚ-distr (xₚ *ₚ yₚ))
                ∙ +P= +P-comm (ap 2·_ (*ₚ-·ₚ-distr xₚ yₚ) ∙ 2·-·ₚ-distr xₚ) ∙ +P-assoc
                ∙ +P= refl (! ·ₚ-+P-distr xₚ) ) ∙ 2·-+P-2·)
             ∙ ! +P-assoc
-- -}
-- -}
-- -}
-- -}
