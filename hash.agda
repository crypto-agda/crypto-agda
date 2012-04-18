module hash where

open import Data.Bits
open import Data.Fin as Fin hiding (_<_; _≤_; fromℕ) renaming (_+_ to _+f_)
open import Data.Fin.Props
open import Data.Vec hiding (last)
open import Data.Nat.NP
open import Data.Product
open import Data.Bool
open import Relation.Binary.PropositionalEquality.NP
open import Function

record PaddingScheme (M : Set) (B : Set) : Set where
  constructor mk
  field
    padlen : M → ℕ
    pad : (m : M) → Vec B (padlen m)

module Merkle-Damgård₁
  {T : Set}             -- Tag space
  {n}                   -- Block length
  (h : T → Bits n → T) -- Compression function
  where

  H₁ : ∀ {ℓ} → T → Vec (Bits n) ℓ → T
  H₁ tag []       = tag
  H₁ tag (x ∷ xs) = H₁ (h tag x) xs

module Merkle-Damgård₂
  {T : Set}             -- Tag space
  {n}                   -- Block length
  (h : T → Bits n → T) -- Compression function

  (IV : T)              -- Initialization vector

  {M : Set}
  (paddingSch : PaddingScheme M (Bits n))
  where

  open Merkle-Damgård₁ h
  open PaddingScheme paddingSch

  H₂ : M → T
  H₂ m = H₁ IV (pad m)

{-
lengthPadding₁ : ∀ {ℓ n} → PaddingScheme (Bits ℓ) (Bits n)
lengthPadding₁ = mk padlen pad where
  padlen : ∀ {ℓ} → Bits ℓ → ℕ
  padlen xs = {!!}

  pad : ∀ {ℓ n} → (m : Bits ℓ) → Vec (Bits n) (padlen m)
  pad [] = {!!}
  pad (b ∷ bs) = {!!}
-}

-- Fin (2 ^ n) → Bits n

lengthPadding₀ : ∀ {n s} → ℕ → Bits (1 + n + s)
lengthPadding₀ {n} {s} x = 1b ∷ 0ⁿ {n} ++ fromℕ {s} x

infixl 6 _ℕ-ℕ'_

-- adapted from Data.Fin, looks better this way:
_ℕ-ℕ'_ : (n : ℕ) → Fin n → ℕ
zero  ℕ-ℕ' ()
suc n ℕ-ℕ' zero   = suc n
suc n ℕ-ℕ' suc i  = n ℕ-ℕ' i

n-m+m≡n : ∀ n (m : Fin n) → (n ℕ-ℕ' m) + Fin.toℕ m ≡ n
n-m+m≡n zero ()
n-m+m≡n (suc n) zero rewrite ℕ°.+-comm n 0 = refl
n-m+m≡n (suc n) (suc m)
   = (suc n ℕ-ℕ' suc m) + Fin.toℕ (suc m) ≡⟨ ℕ°.+-comm (n ℕ-ℕ' m) (Fin.toℕ (suc m)) ⟩
     suc (Fin.toℕ m + (n ℕ-ℕ' m)) ≡⟨ cong suc (ℕ°.+-comm (Fin.toℕ m) (n ℕ-ℕ' m)) ⟩
     suc ((n ℕ-ℕ' m) + Fin.toℕ m) ≡⟨ cong suc (n-m+m≡n n m) ⟩
     suc n ∎ where open ≡-Reasoning

module LengthPadding₁
  {n}
  {s : Fin n}              -- Length of the size part of the padding block
  (sizemsg : Bits (Fin.toℕ s))      -- Usually the size of the message
  {ℓ : Fin n}
  where
  lengthPadding₁ : PaddingScheme (Bits (Fin.toℕ ℓ)) (Bits n)
  lengthPadding₁ = mk padlen pad where
    padlen : ∀ {ℓ} → Bits (Fin.toℕ ℓ) → ℕ
    padlen xs = if (Fin.toℕ ℓ + Fin.toℕ s) <= suc n then 1 else 2

    pad : (m : Bits (Fin.toℕ ℓ)) → Vec (Bits n) (padlen m)
    pad bs with (Fin.toℕ ℓ + Fin.toℕ s) <= suc n | <=.sound (Fin.toℕ ℓ + Fin.toℕ s) (suc n)
    ... | false | _ = helper (bounded _) bs ∷ block₂ ∷ []
         where
           helper : ∀ {n' n} → n' < n → Bits n' → Bits n
           helper (s≤s p) [] = 1b ∷ 0ⁿ
           helper (s≤s p) (b ∷ bs) = b ∷ helper p bs
           block₂ : Bits n
           block₂ = subst Bits (n-m+m≡n n s) (0ⁿ {n ℕ-ℕ' s} ++ sizemsg)
    ... | true | p = helper' ∷ [] where
           helper : ∀ {#0s #m} → Bits #m → Bits (#m + 1 + #0s + Fin.toℕ s)
           helper {p} []       = 1b ∷ 0ⁿ {p} ++ sizemsg
           helper     (b ∷ bs) = b ∷ helper bs

   ℓ + s <= suc n
   suc n ≥ ℓ + s
   suc n ∸ (ℓ + s) ≥ 0

           helper' : ∀ {#0s #m} → #m + 1 + #0s + Fin.toℕ s ≡ n → Bits #m → Bits n
           helper' : ∀ {#0s #m} → #m < n → ℓ + s < n → #m + 1 + #0s + Fin.toℕ s ≡ n → Bits #m → Bits n
           helper' : ∀ {#0s #m} → #m + 1 + #0s + Fin.toℕ s ≡ n → Bits (toN b) → Bits n

           pf = Fin.toℕ ℓ + 1 + (n ∸ (Fin.toℕ ℓ + 1 + Fin.toℕ s)) + Fin.toℕ s ≡⟨ {!!} ⟩
                (n ∸ (Fin.toℕ ℓ + 1 + Fin.toℕ s)) + Fin.toℕ ℓ + 1 + Fin.toℕ s ≡⟨ {!!} ⟩
                (n ∸ Fin.toℕ (ℓ +f suc s)) + Fin.toℕ ℓ + 1 + Fin.toℕ s ≡⟨ {!!} ⟩
                (n ∸ Fin.toℕ (ℓ +f suc s)) + Fin.toℕ (ℓ +f suc s) ≡⟨ {!!} ⟩
                {- (n ℕ-ℕ' (ℓ +f suc s)) + Fin.toℕ (ℓ +f suc s) ≡⟨ ? ⟩ -}
                n ∎ where open ≡-Reasoning

           helper' : Bits n
           helper' = subst Bits pf (helper {n ∸ (Fin.toℕ ℓ + 1 + Fin.toℕ s)} bs)

record WithLast ℓ n : Set where
  constructor mk
  field
    main : Vec (Bits n) ℓ
    {m}  : Fin n
    last : Bits (Fin.toℕ m)

lengthPadding₂ : ∀ {ℓ n} → (∀ m → PaddingScheme (Bits (Fin.toℕ m)) (Bits n)) → PaddingScheme (WithLast ℓ n) (Bits n)
lengthPadding₂ {ℓ} {n} ps = mk padlen pad where
  padlen : WithLast ℓ n → ℕ
  padlen (mk _ last) = ℓ + PaddingScheme.padlen (ps _) last

  pad : (m : WithLast ℓ n) → Vec (Bits n) (padlen m)
  pad (mk xs last) = xs ++ PaddingScheme.pad (ps _) last

-- lengthPadding₃ : ∀ {ℓ n} → PaddingScheme (WithLast ℓ n) (Bits n)
-- lengthPadding₃ = lengthPadding₂ (λ _ → LengthPadding₁.lengthPadding₁)
