{-# OPTIONS --type-in-type #-}
module pisearch where
open import Type hiding (★_)
open import Function.NP
open import Data.Product
open import Data.Sum
open import Data.Bool.NP
open import Search.Type
open import Search.Searchable.Product
open import Search.Searchable
open import sum

Tree : ∀ {A} → Search A → (A → ★) → ★
Tree sA B = sA _×_ B

ToFun : ∀ {A} (sA : Search A) → ★
ToFun {A} sA = ∀ {B} → Tree sA B → Π A B

FromFun : ∀ {A} (sA : Search A) → ★
FromFun {A} sA = ∀ {B} → Π A B → Tree sA B

fromFun-searchInd : ∀ {A} {sA : Search A} → SearchInd sA → FromFun sA
fromFun-searchInd indA = indA (λ s → Tree s _) _,_

toFun-Σ : ∀ {A} {B : A → ★} (sA : Search A) (sB : ∀ {x} → Search (B x))
          → ToFun sA
          → (∀ {x} → ToFun (sB {x}))
          → ToFun (ΣSearch sA (λ {x} → sB {x}))
toFun-Σ _ _ toFunA toFunB t = uncurry (toFunB ∘ toFunA t)

fromFun-Σ : ∀ {A} {B : A → ★} (sA : Search A) (sB : ∀ {x} → Search (B x))
            → FromFun sA
            → (∀ {x} → FromFun (sB {x}))
            → FromFun (ΣSearch sA (λ {x} → sB {x}))
fromFun-Σ _ _ fromFunA fromFunB f = fromFunA (fromFunB ∘ curry f)

open import Relation.Binary.PropositionalEquality
ToFrom : ∀ {A} (sA : Search A)
           (toFunA : ToFun sA)
           (fromFunA : FromFun sA)
         → ★
ToFrom {A} sA toFunA fromFunA = ∀ {B} (f : Π A B) x → toFunA (fromFunA f) x ≡ f x

FromTo : ∀ {A} (sA : Search A)
           (toFunA : ToFun sA)
           (fromFunA : FromFun sA)
         → ★
FromTo sA toFunA fromFunA = ∀ {B} (t : Tree sA B) → fromFunA (toFunA t) ≡ t

module Σ-props {A} {B : A → ★}
                (μA : Searchable A) (μB : ∀ {x} → Searchable (B x)) where
    sA = search μA
    sB : ∀ {x} → Search (B x)
    sB {x} = search (μB {x})
    fromFunA : FromFun sA
    fromFunA = fromFun-searchInd (search-ind μA)
    fromFunB : ∀ {x} → FromFun (sB {x})
    fromFunB {x} = fromFun-searchInd (search-ind (μB {x}))
    module ToFrom
             (toFunA : ToFun sA)
             (toFunB : ∀ {x} → ToFun (sB {x}))
             (toFromA : ToFrom sA toFunA fromFunA)
             (toFromB : ∀ {x} → ToFrom (sB {x}) toFunB fromFunB) where
        toFrom-Σ : ToFrom (ΣSearch sA (λ {x} → sB {x})) (toFun-Σ sA sB toFunA toFunB) (fromFun-Σ sA sB fromFunA fromFunB)
        toFrom-Σ f (x , y) rewrite toFromA (fromFunB ∘ curry f) x = toFromB (curry f x) y

    {- we need a search-ind-ext...
    module FromTo
                 (toFunA : ToFun sA)
                 (toFunB : ∀ {x} → ToFun (sB {x}))
                 (toFromA : FromTo sA toFunA fromFunA)
                 (toFromB : ∀ {x} → FromTo (sB {x}) toFunB fromFunB) where
        toFrom-Σ : FromTo (ΣSearch sA (λ {x} → sB {x})) (toFun-Σ sA sB toFunA toFunB) (fromFun-Σ sA sB fromFunA fromFunB)
        toFrom-Σ t = {!toFromA!} -- {!(λ x → toFromB (toFunA t x))!}
    -}

toFun-× : ∀ {A B} (sA : Search A) (sB : Search B) → ToFun sA → ToFun sB → ToFun (sA ×Search sB)
toFun-× sA sB toFunA toFunB = toFun-Σ sA sB toFunA toFunB

fromFun-× : ∀ {A B} (sA : Search A) (sB : Search B) → FromFun sA → FromFun sB → FromFun (sA ×Search sB)
fromFun-× sA sB fromFunA fromFunB = fromFun-Σ sA sB fromFunA fromFunB

toFun-Bit : ToFun (search μBit)
toFun-Bit (f , t) false = f
toFun-Bit (f , t) true  = t

fromFun-Bit : FromFun (search μBit)
fromFun-Bit f = f false , f true

toFun-⊎ : ∀ {A B} (sA : Search A) (sB : Search B) → ToFun sA → ToFun sB → ToFun (sA +Search sB)
toFun-⊎ sA sB toFunA toFunB (t , u) (inj₁ x) = toFunA t x
toFun-⊎ sA sB toFunA toFunB (t , u) (inj₂ x) = toFunB u x

fromFun-⊎ : ∀ {A B} (sA : Search A) (sB : Search B) → FromFun sA → FromFun sB → FromFun (sA +Search sB)
fromFun-⊎ sA sB fromFunA fromFunB f = fromFunA (f ∘ inj₁) , fromFunB (f ∘ inj₂)

-- toFun-searchInd : ∀ {A} {sA : Search A} → SearchInd sA → ToFun sA
-- toFun-searchInd {A} {sA} indA {B} t = ?
