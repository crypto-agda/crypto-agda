module ec-linkable-ring-sig where

open import Data.Nat  using (ℕ;   zero; suc)
open import Data.Fin  using (Fin; zero; suc; fromℕ)
open import Data.Vec  using (Vec; tabulate; lookup)
open import Data.Bool using (Bool; true; false; if_then_else_)

_‼_ : ∀ {a} {A : Set a} {n} → Vec A n → Fin n → A
v ‼ i = lookup i v

infix 5 _+_ _-_
infix 6 _·_ _*_
postulate
    Point    : Set
    Msg      : Set
    FieldN   : Set
    FieldP   : Set

    _·_ : FieldN → Point → Point
    _+_ : Point → Point → Point
    _*_ : FieldN → FieldN → FieldN
    _-_ : FieldN → FieldN → FieldN
    _==_ : FieldN → FieldN → Bool
    G   : Point
    N-1 : ℕ
    map-to-point : FieldP → Point

N : ℕ
N = suc N-1

PrvKey   : Set
PrvKey   = FieldN
PubKey   : Set
PubKey   = Point
[PubKey] : Set
[PubKey] = Vec PubKey N
[FieldN] : Set
[FieldN] = Vec FieldN N
Index    : Set
Index    = Fin N

max : Index
max = fromℕ N-1

record Sig : Set where
  constructor sig
  field
    c* : FieldN
    s* : [FieldN]
    Y* : Point

module Core-sign (H* : Point)
                 (Y  : Index → PubKey)
                 (Y* : Point)
                 (H₁ : Point → Point → FieldN)
                 (u  : FieldN)
                 (s  : [FieldN])
                 (xπ : FieldN)
                 (π  : Index)
                 where

    c : Index → FieldN
    c i = {!!}
      where
        sᵢ = s ‼ i
        c-suc-π = H₁ (u · G) (u · H*)
        c-suc-i = H₁ (sᵢ · G + c i · Y i) (sᵢ · H* + c i · Y*)

    sπ  = u - xπ * c π

    s* : Index → FieldN
    s* i = {!if i ≟ π then sπ else s ‼ i!}

    core-sign : Sig
    core-sign = record
      { c* = c zero
      ; s* = tabulate s*
      ; Y* = Y* }

module _
  (H₁      : [PubKey] → Point → Msg → Point → Point → FieldN)
  (H₂      : [PubKey] → FieldP)
  (pubKeys : [PubKey])
  (m       : Msg)
  where

    private
        Y : Index → Point
        Y i = pubKeys ‼ i

        H* = map-to-point (H₂ pubKeys)

    sign : Index → PrvKey → [FieldN] → Sig
    sign π xπ s{-random-} = sg
      where
        Y*  = xπ · H*
        u   = s ‼ π
        H₁C = H₁ pubKeys Y* m
        sg  = Core-sign.core-sign H* Y Y* H₁C u s xπ π

    verify : Sig → Bool
    verify (sig c* s* Y*) = res
      where
        H₁C = H₁ pubKeys Y* m
        module M i where
            Yᵢ   = Y i
            sᵢ   = s* ‼ i
            cᵢ   = {!!}
            Zᵢ   = sᵢ · G  + cᵢ · Yᵢ
            Tᵢ   = sᵢ · H* + cᵢ · Y*
            cᵢ+1 = H₁C Zᵢ Tᵢ
        res = c* == H₁C (M.Zᵢ max) (M.Tᵢ max)

{-
sign-using-ecdsa pubKeys m π xπ s =
  h = ?
  r = ?
  Rx , s = ecdsa.sign h r xπ
-}

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
