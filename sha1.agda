-- https://upload.wikimedia.org/wikipedia/commons/e/e2/SHA-1.svg
-- http://www.faqs.org/rfcs/rfc3174.html
open import Type
open import Data.Nat
--open import Data.Product
open import Function.NP hiding (id)
open import FunUniverse.Core hiding (_,_)
open import Data.Fin using (Fin; zero; suc; #_; inject+; raise) renaming (toℕ to Fin▹ℕ)

module sha1
  {t}
  {T : ★_ t}
  {funU : FunUniverse T}
  (funOps : FunOps funU)
  where

open FunUniverse funU renaming (`⊤ to `𝟙; `Bit to `𝟚)
open FunOps funOps hiding (_∘_)

Word : T
Word = `Bits 32

map²ʷ : (`𝟚 `× `𝟚 `→ `𝟚) → Word `× Word `→ Word
map²ʷ = zipWith

mapʷ : (`𝟚 `→ `𝟚) → Word `→ Word
mapʷ = map

lift : ∀ {Γ A B} → (A `→ B) → Γ `→ A → Γ `→ B
lift f g = g ⁏ f

lift₂ : ∀ {Γ A B C} → (A `× B `→ C) → Γ `→ A → Γ `→ B → Γ `→ C
lift₂ op₂ f₀ f₁ = < f₀ , f₁ > ⁏ op₂

`not : ∀ {Γ} (f : Γ `→ Word) → Γ `→ Word
`not = lift (mapʷ not)

infixr 3 _`⊕_
_`⊕_ : ∀ {Γ} (f₀ f₁ : Γ `→ Word) → Γ `→ Word
_`⊕_ = lift₂ (map²ʷ <xor>)

infixr 3 _`∧_
_`∧_ : ∀ {Γ} (f₀ f₁ : Γ `→ Word) → Γ `→ Word
_`∧_ = lift₂ (map²ʷ <and>)

infixr 2 _`∨_
_`∨_ : ∀ {Γ} (f₀ f₁ : Γ `→ Word) → Γ `→ Word
_`∨_ = lift₂ (map²ʷ <or>)

open import Solver.Linear
open import Data.Vec as Vec using ([]; _∷_)

module STest n M = Syntax T _`×_ `𝟙 _`→_ id _⁏_ fst <id,tt> snd <tt,id> <_×_> first second assoc′ assoc swap n M

iter : ∀ {n A B C D} → (D `× A `× B `→ D `× C) → D `× `Vec A n `× `Vec B n `→ `Vec C n
iter {zero}  F = <[]>
iter {suc n} F = < id × < uncons × uncons > >
               ⁏ (helper ⁏ < F × id > ⁏ < swap × id > ⁏ assoc ⁏ < id × iter F >)
               ⁏ <∷>

  where
    helper : ∀ {A B D VA VB} → (D `× (A `× VA) `× (B `× VB)) `→ (D `× A `× B) `× (VA `× VB)
    helper {A} {B} {D} {VA} {VB} = solve (! 2 , (! 0 , ! 3) , (! 1 , ! 4))
                                 ((! 2 , ! 0 , ! 1) , (! 3 , ! 4)) _ where
      open STest 5 (λ i → Vec.lookup i (A ∷ B ∷ D ∷ VA ∷ VB ∷ [])) renaming (rewire to solve; #_ to !_)

<⊞> adder : Word `× Word `→ Word
adder = <tt⁏ <0b> , id > ⁏ iter full-adder
<⊞> = adder

infixl 4 _`⊞_
_`⊞_ : ∀ {A} (f g : A `→ Word) → A `→ Word
_`⊞_ = lift₂ <⊞>
  
<_,_,_> : ∀ {Γ A B C} → Γ `→ A → Γ `→ B → Γ `→ C → Γ `→ (A `× B `× C)
< f₀ , f₁ , f₂ > = < f₀ , < f₁ , f₂ > >

<_,_,_,_,_> : ∀ {Γ A B C D E} → Γ `→ A → Γ `→ B → Γ `→ C
                              → Γ `→ D → Γ `→ E
                              → Γ `→ (A `× B `× C `× D `× E)
< f₀ , f₁ , f₂ , f₃ , f₄ > = < f₀ , < f₁ , < f₂ , f₃ , f₄ > > >

<<<₅ : Word `→ Word
<<<₅ = rot-left 5

<<<₃₀ : Word `→ Word
<<<₃₀ = rot-left 30

Word² = Word `× Word
Word³ = Word `× Word²
Word⁴ = Word `× Word³
Word⁵ = Word `× Word⁴

iterateⁿ : ∀ {A} n → (Fin n → A `→ A) → A `→ A
iterateⁿ zero    f = id
iterateⁿ (suc n) f = f zero ⁏ iterateⁿ n (f ∘ suc)

_²⁰ : ∀ {A} → (Fin 20 → A `→ A) → (A `→ A)
_²⁰ = iterateⁿ 20

A-E : T
A-E = Word⁵

module _ (#ʷ : ℕ → `𝟙 `→ Word) where

  module Iterations
    (A B C D E : A-E `→ Word)
    where

    module _ (F : A-E `→ Word)
             (K : `𝟙  `→ Word)
             (W : `𝟙  `→ Word) where
        Iteration = < A' , A , (B ⁏ <<<₃₀) , C , D >
         where A' = F `⊞ E `⊞ (A ⁏ <<<₅) `⊞ (tt ⁏ W) `⊞ (tt ⁏ K)

    module _ 
        (W : Fin 80 → `𝟙 `→ Word) where

        Iteration⁸⁰ =
              (Iteration F₀ K₀ ∘ W₀)²⁰ ⁏
              (Iteration F₂ K₂ ∘ W₂)²⁰ ⁏
              (Iteration F₄ K₄ ∘ W₄)²⁰ ⁏
              (Iteration F₆ K₆ ∘ W₆)²⁰
          where
            F₀ = B `∧ C `∨ `not B `∧ D
            F₂ = B `⊕ C `⊕ D
            F₄ = B `∧ C `∨ B `∧ D `∨ C `∧ D
            F₆ = F₂

            K₀ = #ʷ 0x5A827999
            K₂ = #ʷ 0x6ED9EBA1
            K₄ = #ʷ 0x8F1BBCDC
            K₆ = #ʷ 0xCA62C1D6

            W₀ W₂ W₄ W₆ : Fin 20 → `𝟙 `→ Word
            W₀ = W ∘ inject+ 60
            W₂ = W ∘ inject+ 40 ∘ raise 20
            W₄ = W ∘ inject+ 20 ∘ raise 40
            W₆ = W              ∘ raise 60

  SHA1 : (Fin 80 → `𝟙 `→ Word) → A-E `→ A-E
  SHA1 = Iterations.Iteration⁸⁰ H0 H1 H2 H3 H4
   where
    H0 = tt ⁏ #ʷ 0x67452301
    H1 = tt ⁏ #ʷ 0xEFCDAB89
    H2 = tt ⁏ #ʷ 0x98BADCFE
    H3 = tt ⁏ #ʷ 0x10325476
    H4 = tt ⁏ #ʷ 0xC3D2E1F0

-- -}
