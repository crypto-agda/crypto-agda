{-# OPTIONS --type-in-type #-}
module pisearch where
open import Type hiding (★_)
open import Function
open import Data.Product
open import Data.Sum
open import Data.Bool.NP
open import Search.Type
open import Search.Searchable.Product
open import Search.Searchable
open import sum

Π' : ∀ {A} → Search A → (A → ★) → ★
Π' sA B = sA _×_ B

Π : (A : ★₀) → (B : A → ★₀) → ★₀
Π A B = (x : A) → B x

P→ : ∀ {A} (sA : Search A) → ★₀
P→ {A} sA = ∀ {B} → Π' sA B → Π A B

P← : ∀ {A} (sA : Search A) → ★₀
P← {A} sA = ∀ {B} → Π A B → Π' sA B

P→Σ : ∀ {A} {B : A → ★} (sA : Search A) (sB : ∀ {x} → Search (B x))
     → P→ sA
     → (∀ {x} → P→ (sB {x}))
     → P→ (ΣSearch sA (λ {x} → sB {x}))
P→Σ _ _ PA PB t = uncurry (PB ∘ PA t)

P←Σ : ∀ {A} {B : A → ★} (sA : Search A) (sB : ∀ {x} → Search (B x))
      → P← sA
      → (∀ {x} → P← (sB {x}))
      → P← (ΣSearch sA (λ {x} → sB {x}))
P←Σ _ _ PA PB f = PA (PB ∘ curry f)

P→× : ∀ {A B} (sA : Search A) (sB : Search B) → P→ sA → P→ sB → P→ (sA ×Search sB)
P→× sA sB PA PB = P→Σ sA sB PA PB

P←× : ∀ {A B} (sA : Search A) (sB : Search B) → P← sA → P← sB → P← (sA ×Search sB)
P←× sA sB PA PB = P←Σ sA sB PA PB

P→Bit : P→ (search μBit)
P→Bit (f , t) false = f
P→Bit (f , t) true  = t

P←Bit : P← (search μBit)
P←Bit f = f false , f true

P→⊎ : ∀ {A B} (sA : Search A) (sB : Search B) → P→ sA → P→ sB → P→ (sA +Search sB)
P→⊎ sA sB PA PB (t , u) (inj₁ x) = PA t x
P→⊎ sA sB PA PB (t , u) (inj₂ x) = PB u x

P←⊎ : ∀ {A B} (sA : Search A) (sB : Search B) → P← sA → P← sB → P← (sA +Search sB)
P←⊎ sA sB PA PB f = PA (f ∘ inj₁) , PB (f ∘ inj₂)

-- P→Ind : ∀ {A} {sA : Search A} → SearchInd sA → P→ sA
-- P→Ind {A} {sA} indA {B} t = ?

P←Ind : ∀ {A} {sA : Search A} → SearchInd sA → P← sA
P←Ind indA = indA (λ s → Π' s _) _,_
