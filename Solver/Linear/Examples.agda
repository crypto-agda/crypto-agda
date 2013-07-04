module Solver.Linear.Examples where

open import Solver.Linear
open import Data.String
open import Data.Zero
open import Relation.Binary.NP
open import Relation.Nullary.Decidable
open import Data.Vec
open import Data.Product
open import Data.Unit
open import Function
open import FunUniverse.Agda

module example1 where

  -- need to etaexpand this because otherwise we get an error
  open Syntaxˢ funLin
  test : (A B C : Set) → (A × B) × C → (B × A) × C
  test A B C = rewireˢ Γ "(A,B),C↦(B,A),C"
   where
    Γ : String → _
    Γ "A" = A
    Γ "B" = B
    Γ "C" = C
    Γ  _  = 𝟘

module example2 where
  open Syntaxᶠ funLin
  test2 : (A B C : Set) → (A × B) × C → (B × A) × C
  test2 A B C = rewireᶠ (A ∷ B ∷ C ∷ []) (λ a b c → (a , b) , c ↦ (b , a) , c)

  {-
module example3 where

  open import Data.Vec

  data Ty : Set where
    _×_ : Ty → Ty → Ty
    ⊤ : Ty

  infix 4 _⟶_ 

  data _⟶_ : Ty → Ty → Set where
    id' : ∀ {A} → A ⟶ A
    _∻'_ : ∀ {A B C} → A ⟶ B → B ⟶ C → A ⟶ C
    <id,tt>' : ∀ {A} → (A × ⊤) ⟶ A
    <id,tt>⁻¹' : ∀ {A} → A ⟶ (A × ⊤)
    <tt,id>' : ∀ {A} → (⊤ × A) ⟶ A
    <tt,id>⁻¹' : ∀ {A} → A ⟶ (⊤ × A)
    ⟨_×'_⟩   : ∀ {A B C D} → A ⟶ C → B ⟶ D → (A × B) ⟶ (C × D)
    first    : ∀ {A B C} → A ⟶ B → A × C ⟶ B × C
    second   : ∀ {A B C} → B ⟶ C → A × B ⟶ A × C 
    assoc'   : ∀ {A B C} → (A × (B × C)) ⟶ ((A × B) × C)
    assoc⁻¹' : ∀ {A B C} → ((A × B) × C) ⟶ (A × (B × C))
    swap'    : ∀ {A B}   → (A × B) ⟶ (B × A)
  

  module STest {n} M = Syntax _×_ ⊤ _⟶_ id' _∻'_ <id,tt>' <id,tt>⁻¹' <tt,id>' <tt,id>⁻¹' ⟨_×'_⟩ first second assoc' assoc⁻¹' swap' {n} M

  test2 : (A B C : Ty) → (A × B) × C ⟶  (B × A) × C
  test2 A B C = rewire ((# 0 , # 1) , # 2) ((# 1 , # 0) , # 2) _ where
    open STest (λ i → lookup i (A ∷ B ∷ C ∷ []))

module example₃ where

  open import Data.Unit
  open import Data.Product
  open import Data.Vec

  open import Function using (flip ; const)
  
  open import Function.Inverse
  open import Function.Related.TypeIsomorphisms.NP

  open ×-CMon using () renaming (∙-cong to ×-cong ; assoc to ×-assoc)

  module STest {n} M = Syntax _×_ ⊤ _↔_ id (flip _∘_) A×⊤↔A (sym A×⊤↔A) (A×⊤↔A ∘ swap-iso) (swap-iso ∘ sym A×⊤↔A)
                            ×-cong first-iso (λ x → second-iso (const x))
                            (sym (×-assoc _ _ _)) (×-assoc _ _ _) swap-iso {n} M

  test : ∀ A B C → ((A × B) × C) ↔ (C × (B × A))
  test A B C = rewire ((# 0 , # 1) , # 2) (# 2 , (# 1 , # 0)) _ where
    open STest (λ i → lookup i (A ∷ B ∷ C ∷ []))
-- -}
-- -}
-- -}
-- -}
