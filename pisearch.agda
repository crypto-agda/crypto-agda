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

Tree : ∀ {A} → Search A → (A → ★) → ★
Tree sA B = sA _×_ B

Π : (A : ★) → (B : A → ★) → ★
Π A B = (x : A) → B x

ToFun : ∀ {A} (sA : Search A) → ★
ToFun {A} sA = ∀ {B} → Tree sA B → Π A B

FromFun : ∀ {A} (sA : Search A) → ★
FromFun {A} sA = ∀ {B} → Π A B → Tree sA B

toFun-Σ : ∀ {A} {B : A → ★} (sA : Search A) (sB : ∀ {x} → Search (B x))
          → ToFun sA
          → (∀ {x} → ToFun (sB {x}))
          → ToFun (ΣSearch sA (λ {x} → sB {x}))
toFun-Σ _ _ PA PB t = uncurry (PB ∘ PA t)

fromFun-Σ : ∀ {A} {B : A → ★} (sA : Search A) (sB : ∀ {x} → Search (B x))
            → FromFun sA
            → (∀ {x} → FromFun (sB {x}))
            → FromFun (ΣSearch sA (λ {x} → sB {x}))
fromFun-Σ _ _ PA PB f = PA (PB ∘ curry f)

toFun-× : ∀ {A B} (sA : Search A) (sB : Search B) → ToFun sA → ToFun sB → ToFun (sA ×Search sB)
toFun-× sA sB PA PB = toFun-Σ sA sB PA PB

fromFun-× : ∀ {A B} (sA : Search A) (sB : Search B) → FromFun sA → FromFun sB → FromFun (sA ×Search sB)
fromFun-× sA sB PA PB = fromFun-Σ sA sB PA PB

toFun-Bit : ToFun (search μBit)
toFun-Bit (f , t) false = f
toFun-Bit (f , t) true  = t

fromFun-Bit : FromFun (search μBit)
fromFun-Bit f = f false , f true

toFun-⊎ : ∀ {A B} (sA : Search A) (sB : Search B) → ToFun sA → ToFun sB → ToFun (sA +Search sB)
toFun-⊎ sA sB PA PB (t , u) (inj₁ x) = PA t x
toFun-⊎ sA sB PA PB (t , u) (inj₂ x) = PB u x

fromFun-⊎ : ∀ {A B} (sA : Search A) (sB : Search B) → FromFun sA → FromFun sB → FromFun (sA +Search sB)
fromFun-⊎ sA sB PA PB f = PA (f ∘ inj₁) , PB (f ∘ inj₂)

-- toFun-searchInd : ∀ {A} {sA : Search A} → SearchInd sA → ToFun sA
-- toFun-searchInd {A} {sA} indA {B} t = ?

fromFun-searchInd : ∀ {A} {sA : Search A} → SearchInd sA → FromFun sA
fromFun-searchInd indA = indA (λ s → Tree s _) _,_
