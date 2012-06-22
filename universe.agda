module universe where

import Level as L
open import Data.Nat.NP using (ℕ; _+_; _*_; _^_)
open import Data.Bits using (Bit)
open import Data.Unit using (⊤)
open import Data.Product using (_×_; _,_) renaming (zip to ×-zip)
open import Data.Vec using (Vec)

record Universe {t} (T : Set t) : Set t where
  constructor mk
  field
    `⊤    : T
    `Bit  : T
    _`×_  : T → T → T
    _`^_  : T → ℕ → T

  `Vec : T → ℕ → T
  `Vec A n = A `^ n

  `Bits : ℕ → T
  `Bits n = `Bit `^ n

  infixr 2 _`×_
  infixl 2 _`^_

Set-U : Universe Set
Set-U = mk ⊤ Bit _×_ Vec

width-U : Universe ℕ
width-U = mk 0 1 _+_ _*_

card-U : Universe ℕ
card-U = mk 1 2 _*_ _^_

⊤-U : Universe ⊤
⊤-U = mk _ _ _ _

×-U : ∀ {s t} {S : Set s} {T : Set t} → Universe S → Universe T → Universe (S × T)
×-U S-U T-U = mk (S.`⊤ , T.`⊤) (S.`Bit , T.`Bit) (×-zip S._`×_ T._`×_)
                 (λ { (A₀ , A₁) n → S.`Vec A₀ n , T.`Vec A₁ n })
  where module S = Universe S-U
        module T = Universe T-U

Sym-U : ∀ t → Set (L.suc t)
Sym-U t = ∀ {T : Set t} → Universe T

data U : Set where
  ⊤′ Bit′ : U
  _×′_    : U → U → U
  _^′_    : U → ℕ → U

syn-U : Universe U
syn-U = mk ⊤′ Bit′ _×′_ _^′_

fold-U : ∀ {t} {T : Set t} → Universe T → U → T
fold-U {_} {T} uni = go
  where open Universe uni
        go : U → T
        go ⊤′         = `⊤
        go Bit′       = `Bit
        go (t₀ ×′ t₁) = go t₀ `× go t₁
        go (t ^′ n)   = go t `^ n

UniOp : ∀ {s t} (S : Set s) (T : Set t) → Set _
UniOp S T = Universe S → Universe T

UniOp₂ : ∀ {r s t} (R : Set r) (S : Set s) (T : Set t) → Set _
UniOp₂ R S T = Universe R → Universe S → Universe T
