open import Type
open import Data.Bool using (Bool; true; false) -- ; if_then_else_; _∨_)
{-
open import Function
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
-}
-- open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

module schnorr
-- (q : ℕ) -- Prime q

(ℤq : ★)

(G : ★) -- = ⟨ℤp⟩★ should for a group of order q
(g : G)   -- generator of the group G
(_^_  : G → ℤq → G)
(_∙_  : G → G → G)

(_⊟_  : ℤq → ℤq → ℤq)
(_⊠_  : ℤq → ℤq → ℤq)

(ℤq★ : ★) -- ℤq excluding 0
(weaken : ℤq★ → ℤq)

(_==_ : ℤq → ℤq → Bool)
-- (_==ᴳ_ : G → G → Bool)

(M : ★)
(ℋ⟨_∥_⟩ : G → M → ℤq)  -- I flipped the order of arguments to fit the
                        -- "random prefix" assumption
where

Sig : ★
Sig = ℤq × ℤq

-- Do not call directly this function, use Sign
Sign★ : (m : M) (x : ℤq) (k : ℤq) → Sig
Sign★ m x k = (s , e)

  where r = g ^ k
        e = ℋ⟨ r ∥ m ⟩
        s = k ⊟ (x ⊠ e)

Sign : (m : M) (x : ℤq★) (k : ℤq★) → Sig
Sign m x′ k′ = Sign★ m (weaken x′) (weaken k′)

-- Reject the signature if 0 < r < q or 0 < s < q is not satisfied.
Ver : (m : M) (gˣ : G) (sig : Sig) → Bool
Ver m gˣ (s , e) = eᵥ == e

  module Ver where rᵥ = (g ^ s) ∙ (gˣ ^ e)
                   eᵥ = ℋ⟨ rᵥ ∥ m ⟩

open import Relation.Binary.PropositionalEquality

_^′_ : G → ℤq★ → G
g ^′ x = g ^ weaken x

module Proof
  (^-⊟ : ∀ α x y → (α ^ (x ⊟ y)) ∙ (α ^ y) ≡ α ^ x)
  (^-⊠ : ∀ α x y → (α ^ x) ^ y ≡ α ^(x ⊠ y))
  (==-refl : ∀ {x} → x == x ≡ true)
  (m : M) (x k : ℤq) where

  gˣ  = g ^ x
  sig = Sign★ m x k
  s   = proj₁ sig
  e   = proj₂ sig

  r   = g ^ k

  pf1 : e ≡ ℋ⟨ r ∥ m ⟩
  pf1 = refl
  pf2 : s ≡ k ⊟ (x ⊠ e)
  pf2 = refl

  open Ver m gˣ s e

  rᵥ≡r : rᵥ ≡ r
  rᵥ≡r rewrite ^-⊠ g x e
             | ^-⊟ g k (x ⊠ e) = refl
             
  eᵥ≡e : eᵥ ≡ e
  eᵥ≡e rewrite rᵥ≡r = refl

  pf : Ver m gˣ (Sign★ m x k) ≡ true
  pf rewrite eᵥ≡e = ==-refl

module HashFunctionRequirements
    (Rd : ★)
    (Message : ★)
    (Hash : ★)
    (_==ᴴ_ : Hash → Hash → Bool)
    (ℋ⟨_∥_⟩ : Rd → Message → Hash)
    where

    RPPAdv : ★ → ★
    RPPAdv Rₐ = (Rₐ → Hash)
              × (Rₐ → Rd → Message)

    RPP-advantage : ∀ {Rₐ} → RPPAdv Rₐ → (Rₐ × Rd) → Bool
    RPP-advantage (A₀ , A₁) (rₐ , rd) = ℋ⟨ rd ∥ m ⟩ ==ᴴ h
      where h = A₀ rₐ
            m = A₁ rₐ rd

    RPSPAdv : ★ → ★
    RPSPAdv Rₐ = (Rₐ → Message)
               × (Rₐ → Rd → Message)

    RPSP-advantage : ∀ {Rₐ} → RPSPAdv Rₐ → (Rₐ × Rd) → Bool
    RPSP-advantage (A₀ , A₁) (rₐ , rd) = ℋ⟨ rd ∥ m₀ ⟩ ==ᴴ ℋ⟨ rd ∥ m₁ ⟩
      where m₀ = A₀ rₐ
            m₁ = A₁ rₐ rd

Rd = G
Message = M
Hash = ℤq
open HashFunctionRequirements Rd Message Hash _==_ ℋ⟨_∥_⟩
