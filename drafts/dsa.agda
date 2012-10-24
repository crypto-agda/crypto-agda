-- Draft: we should move to something provably secure, like Schnorr signature.

open import Function
open import Data.Bool using (Bool; true; false; if_then_else_; _∨_)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)

module dsa

-- (N : ℕ) -- = 256
-- (L : ℕ) -- = 2048

-- (q : ℕ) -- Bits N, Prime q
-- (p : ℕ) -- Bits L, Prime p, st. ∃ k, q * k = p-1

(ℤq : Set)

(G : Set) -- = ⟨ℤp⟩★ should for a group of order q
(g : G)   -- generator of the group G
(_^_  : G → ℤq → G)
(_∙pq_  : G → G → ℤq)

(g^_  : ℤq → ℤq)
(_⊞_  : ℤq → ℤq → ℤq)
(_∙_  : ℤq → ℤq → ℤq)
(_/_  : ℤq → ℤq → ℤq)

(ℤq★ : Set)
(refine? : ℤq → Maybe ℤq★)
(weaken : ℤq★ → ℤq)
(_==_ : ℤq → ℤq → Bool)
(_⁻¹ : ℤq★ → ℤq)

(M : Set)
(ℋ : M → ℤq)

where

Sig : Set
Sig = ℤq★ × ℤq★

Sign : (m : M) (x : ℤq) (r : ℤq) → Maybe Sig
Sign m x r = case (refine? R , refine? S) of λ
                { (just R′ , just S′) → just (R′ , S′)
                ; _                   → nothing
                }
  where R = g^ r
        S = (ℋ m ⊞ (x ∙ R)) / r

-- Reject the signature if 0 < r < q or 0 < s < q is not satisfied.
Ver : (m : M) (gˣ : G) (sig : Sig) → Bool
Ver m gˣ (R′ , S′) = R == v
  where R = weaken R′
        S = weaken S′
        w = S′ ⁻¹
        u₁ = ℋ m ∙ w -- mod q
        u₂ = R ∙ w    -- mod q
        v = (g ^ u₁) ∙pq (gˣ ^ u₂) {-mod p [mod-q] -}
