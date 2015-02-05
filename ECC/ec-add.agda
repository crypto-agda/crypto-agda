open import Relation.Binary.PropositionalEquality.NP
open import Data.Bool
open import Data.Product
open import Reflection.NP
open import Algebra.Field

module _
  (ℤq : Set)
  (ℤq-field : Field ℤq)
  ({-N unused-} a b : ℤq)
  where

open Field ℤq-field

open ≡-Reasoning

TODO
x³ + ax + b 

-_ = 0-_

  -- A = 7
  -- B = 0
  -- N ≈ 2^256 - ...
  -- y² = x³ + Ax + B
On-curve : (x y : ℤq) → Set
On-curve x y = y ² ≡ x ³ + a * x + b

record PrePoint : Set where
  constructor _,_by⟨_⟩
  field
    x y       : ℤq
    .on-curve : On-curve x y

data Point : Set where
  ∞  : Point
  pp : (p : PrePoint) → Point

-ₚₚ-on-curve : ∀ {x y} → On-curve x y → On-curve x (- y)
-ₚₚ-on-curve e = ²-0--distr ∙ e

-ₚₚ_ : PrePoint → PrePoint
-ₚₚ (x , y by⟨ e ⟩) = x , - y by⟨ -ₚₚ-on-curve e ⟩

-ₚ_ : Point → Point
-ₚ ∞    = ∞
-ₚ pp p = pp (-ₚₚ p)

module Line (Px Py Qx Qy : ℤq) 
            (u v   : ℤq)
            (v≢0   : v ≢ 0ᶠ)
           .(u-def : u ≡ Qy − Py)
           .(v-def : v ≡ Qx − Px)
           where

    s  = u / v -- the slope

    -- line: y = s * x - s * Px + Py
    line : ℤq → ℤq
    line x = s * (x − Px) + Py

    On-line : (x y : ℤq) → Set
    On-line x y = y ≡ line x

    -- TODO move earlier
    P-on-line : On-line Px Py
    P-on-line = {!!}

    -- TODO move earlier
    .Q-on-line : On-line Qx Qy
    Q-on-line = Qy
              ≡⟨ ! +0-identity ⟩
                Qy + 0ᶠ
              ≡⟨ += refl (! 0--inverse) ⟩
                Qy + (- Py + Py)
              ≡⟨ ! +-assoc ⟩
                Qy − Py + Py
              ≡⟨ += (! u-def) refl ⟩
                u + Py
              ≡⟨ ap (λ z → z + Py) (! *1-identity) ⟩
                u * 1ᶠ + Py
              ≡⟨ ap (λ z → u * z + Py) (! ⁻¹-inverse v≢0) ⟩
                u * (v ⁻¹ * v) + Py
              ≡⟨ ap (λ z → u * (v ⁻¹ * z) + Py) v-def ⟩
                u * (v ⁻¹ * (Qx − Px)) + Py
              ≡⟨ += (! *-assoc) refl ⟩
                s * (Qx − Px) + Py
              ∎

-- add two different points together
module Diff-add (p q : PrePoint) where
  module P = PrePoint p
  module Q = PrePoint q

  module _
          (u v   : ℤq)
          (v≢0   : v ≢ 0ᶠ)
         .(u-def : u ≡ Q.y − P.y)
         .(v-def : v ≡ Q.x − P.x)
         -- (H : {!!})
         -- (p ≢  q)
         -- (p ≢ -q)
       where

    -- foo : s * P.x + - s * P.x ≡ 0ᶠ

    -- line x = s * (x − P.x) + P.y

    -- On-curve X Y ≡ ((s * X - s * P.x + P.y)² ≡ X³ + aX + b)
    -- Rx = s² - (P.x + Q.x)

    -- R is P + Q

    open Line P.x P.y Q.x Q.y u v v≢0 u-def v-def

    Rx = s ² − (P.x + Q.x)
    -- Rx - P.x ≡ s² - (2Px + Qx)

    sx = s * (P.x − Rx)
    Ry = sx − P.y

    .Ry-spec : Ry ≡ -(line Rx)
    Ry-spec = Ry
            ≡⟨ −= *-−-distr refl ⟩
              s * P.x − (s * Rx) − P.y
            ≡⟨ ap (λ z → z − P.y) +-comm ⟩
              -(s * Rx) + s * P.x − P.y
            ≡⟨ ap (λ z → -(s * Rx) + z − P.y) (! 0--involutive) ⟩
              -(s * Rx) − - (s * P.x) − P.y
            ≡⟨ ap (λ z → z − P.y) (! 0--+-distr) ⟩
              - (s * Rx − s * P.x) − P.y
            ≡⟨ ! 0--+-distr ⟩
              -(s * Rx − s * P.x + P.y)
            ≡⟨ ap 0-_ (ap (λ z → z + P.y) (! *-−-distr)) ⟩ 
              -(s * (Rx − P.x) + P.y)
            ≡⟨by-definition⟩
              -(line Rx)
            ∎

    -- P.y ² ≡ P.x ³ + a * P.x + b

    .-R-on-curve : On-curve Rx (line Rx)
    -R-on-curve = (line Rx)²
                ≡⟨ ²-+-distr ⟩
                  (s * (Rx − P.x)) ² + P.y ² + 2* (s * (Rx − P.x)) * P.y
                ≡⟨ {!!} ⟩
                  Rx ³ + a * Rx + b
                ∎

    {-
    .R-on-curve : On-curve Rx Ry
    R-on-curve = Ry ²
               ≡⟨by-definition⟩
                 (sx − P.y)²
                 --(s * (P.x − Rx) − P.y) * (s * (P.x − Rx) − P.y)
               ≡⟨ ²-−-distr ⟩
                 sx ² + P.y ² − 2* sx * P.y
               ≡⟨ ap (λ z → z + P.y ² − 2* sx * P.y) ²-*-distr ⟩
                 s ² * (P.x − Rx)² + P.y ² − 2* sx * P.y
               ≡⟨ {!!} ⟩
                 (s ² − (P.x + Q.x)) ³ + a * (s ² − (P.x + Q.x)) + b
               ≡⟨by-definition⟩
                 Rx ³ + a * Rx + b
               ∎

    R : PrePoint
    R = Rx , Ry by⟨ R-on-curve ⟩

_+ₚₚ_ : PrePoint → PrePoint → Point
p +ₚₚ q = {!!}
  -- if q == p  then dbl p
  -- if q == -p then ∞
  -- else diff-add p q

_+ₚ_ : Point → Point → Point
∞    +ₚ q    = q
pp p +ₚ ∞    = pp p
pp p +ₚ pp q = p +ₚₚ q

∞+-identity : ∀ {p} → ∞ +ₚ p ≡ p
∞+-identity = refl

+∞-identity : ∀ {p} → p +ₚ ∞ ≡ p
+∞-identity {∞}    = refl
+∞-identity {pp p} = refl

dbl : Point → Point
dbl (ax , ay) = (px , py)
  module EC-double where
  -- (3 * (ax)² + A)/(2ay)
    lam = ((3ᶠ * ax * ax + Acurve) * modinv (2ᶠ * ay) Pcurve) % Pcurve
    px = (lam * lam - 2ᶠ * ax)  % Pcurve
    -- px = (lam * lam - ax - ax)  % Pcurve
    py = (lam * (ax - px) - ay) % Pcurve
 
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
