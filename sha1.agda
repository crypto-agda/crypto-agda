{-# OPTIONS --without-K #-}
-- https://upload.wikimedia.org/wikipedia/commons/e/e2/SHA-1.svg
-- http://www.faqs.org/rfcs/rfc3174.html
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_)
import Data.Vec as V
open V using (Vec; []; _∷_)
open import Function using (_∘_)
open import FunUniverse.Core hiding (_,_)
open import Data.Fin using (Fin; zero; suc; #_; inject+; raise) renaming (toℕ to Fin▹ℕ)

open import Solver.Linear

module sha1 where

Endo : Set → Set
Endo A = A → A

module FunSHA1
  {t}
  {T : Set t}
  {funU : FunUniverse T}
  (funOps : FunOps funU)
  where

    open FunUniverse funU
    open FunOps funOps renaming (_∘_ to _`∘_)
    module LinSolver = Syntaxᶠ linRewiring

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


    --iter : ∀ {n A B S} → (S `× A `→ S `× B) → S `× `Vec A n `→ `Vec B n

    iter : ∀ {n A B C D} → (D `× A `× B `→ D `× C) → D `× `Vec A n `× `Vec B n `→ `Vec C n
    iter {zero}  F = <[]>
    iter {suc n} F = < id × < uncons × uncons > >
                   ⁏ (helper ⁏ < F × id > ⁏ < swap × id > ⁏ assoc ⁏ < id × iter F >)
                   ⁏ <∷>

      where
        open LinSolver
        helper = λ {A} {B} {D} {VA} {VB} →
          rewireᶠ (A ∷ B ∷ D ∷ VA ∷ VB ∷ [])
                  (λ a b d va vb → (d , (a , va) , (b , vb)) ↦ (d , a , b) , (va , vb))

    <⊞> adder : Word `× Word `→ Word
    adder = <tt⁏ <0₂> , id > ⁏ iter full-adder
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

    <<<₅ : `Endo Word
    <<<₅ = rot-left 5

    <<<₃₀ : `Endo Word
    <<<₃₀ = rot-left 30

    Word² = Word `× Word
    Word³ = Word `× Word²
    Word⁴ = Word `× Word³
    Word⁵ = Word `× Word⁴

    open import Data.Digit

    bits : ∀ ℓ → ℕ → `𝟙 `→ `Bits ℓ
    bits ℓ n₀ =  constBits (L▹V (L.map F▹𝟚 (proj₁ (toDigits 2 n₀))))
      where open import Data.List as L
            open import Data.Product
            open import Data.Two
            L▹V : ∀ {n} → List 𝟚 → Vec 𝟚 n
            L▹V {zero} xs = []
            L▹V {suc n} [] = V.replicate 0₂
            L▹V {suc n} (x ∷ xs) = x ∷ L▹V xs
            F▹𝟚 : Fin 2 → 𝟚
            F▹𝟚 zero    = 0₂
            F▹𝟚 (suc _) = 1₂

            {-
    [_-_mod_] : ℕ → ℕ → ℕ → ℕ
    [ m - n mod p ] = {!!}

    [_+_mod_] : ℕ → ℕ → ℕ → ℕ
    [ m + n mod p ] = {!!}
    -}

    #ʷ = bits 32

    <⊞⁵> : Word⁵ `× Word⁵ `→ Word⁵
    <⊞⁵> = < <⊞> `zip` < <⊞> `zip` < <⊞> `zip` < <⊞> `zip` <⊞> > > > >

    iterateⁿ : ∀ {A} n → (Fin n → `Endo A) → `Endo A
    iterateⁿ zero    f = id
    iterateⁿ (suc n) f = f zero ⁏ iterateⁿ n (f ∘ suc)

    _²⁰ : ∀ {A} → (Fin 20 → `Endo A) → `Endo A
    _²⁰ = iterateⁿ 20

    module _ where

      K₀ = #ʷ 0x5A827999
      K₂ = #ʷ 0x6ED9EBA1
      K₄ = #ʷ 0x8F1BBCDC
      K₆ = #ʷ 0xCA62C1D6

      H0 = #ʷ 0x67452301
      H1 = #ʷ 0xEFCDAB89
      H2 = #ʷ 0x98BADCFE
      H3 = #ʷ 0x10325476
      H4 = #ʷ 0xC3D2E1F0

      A B C D E : Word⁵ `→ Word
      A = fst
      B = snd ⁏ fst
      C = snd ⁏ snd ⁏ fst
      D = snd ⁏ snd ⁏ snd ⁏ fst
      E = snd ⁏ snd ⁏ snd ⁏ snd

      F₀ = B `∧ C `∨ `not B `∧ D
      F₂ = B `⊕ C `⊕ D
      F₄ = B `∧ C `∨ B `∧ D `∨ C `∧ D
      F₆ = F₂

      module _ (F : Word⁵ `→ Word)
               (K : `𝟙  `→ Word)
               (W : `𝟙  `→ Word) where
        Iteration = < A' , A , (B ⁏ <<<₃₀) , C , D >
          where A' = F `⊞ E `⊞ (A ⁏ <<<₅) `⊞ (tt ⁏ W) `⊞ (tt ⁏ K)

      module _ (W : Fin 80 → `𝟙 `→ Word) where
        W₀ W₂ W₄ W₆ : Fin 20 → `𝟙 `→ Word
        W₀ = W ∘ inject+ 60 ∘ raise  0
        W₂ = W ∘ inject+ 40 ∘ raise 20
        W₄ = W ∘ inject+ 20 ∘ raise 40
        W₆ = W ∘ inject+  0 ∘ raise 60

        Iteration⁸⁰ : `Endo Word⁵
        Iteration⁸⁰ =
          (Iteration F₀ K₀ ∘ W₀)²⁰ ⁏
          (Iteration F₂ K₂ ∘ W₂)²⁰ ⁏
          (Iteration F₄ K₄ ∘ W₄)²⁰ ⁏
          (Iteration F₆ K₆ ∘ W₆)²⁰

        pad0s : ℕ → ℕ
        pad0s zero = 512 ∸ 65
        pad0s (suc _) = STUCK where postulate STUCK : ℕ
        -- pad0s n = [ 512 - [ n + 65 mod 512 ] mod 512 ]

        paddedLength : ℕ → ℕ
        paddedLength n = n + (1 + pad0s n + 64)

        padding : ∀ {n} → `Bits n `→ `Bits (paddedLength n)
        padding {n} = < id ,tt⁏ <1∷ < <0ⁿ> {pad0s n} ++ bits 64 n > > > ⁏ append

        ite : Endo (`Endo Word⁵)
        ite f = dup ⁏ first f ⁏ <⊞⁵>

        hash-block : `Endo Word⁵
        hash-block = ite Iteration⁸⁰

      ite' : ∀ n (W : Fin n → Fin 80 → `𝟙 `→ Word)
             → ((Fin 80 → `𝟙 `→ Word) → `Endo Word⁵) → `Endo Word⁵
      ite' zero    W f = id
      ite' (suc n) W f = f (W zero) ⁏ ite' n (W ∘ suc) f

      SHA1 : ∀ n (W : Fin n → Fin 80 → `𝟙 `→ Word) → `𝟙 `→ Word⁵
      SHA1 n W = < H0 , H1 , H2 , H3 , H4 >
               ⁏ ite' n W hash-block

      SHA1-on-0s : `𝟙 `→ Word⁵
      SHA1-on-0s = SHA1 1 (λ _ _ → <0ⁿ>)

module AgdaSHA1 where
  open import FunUniverse.Agda
  open FunSHA1 agdaFunOps
  open import Data.Two

import FunUniverse.Cost as Cost
sha1-cost : ℕ
sha1-cost = FunSHA1.SHA1-on-0s Cost.timeOps

open import Data.Nat.Show
open import FFI.JS using (JS!)
import FFI.JS.Console as Console
main : JS!
main = Console.log (show sha1-cost)

{-
open import IO
import IO.Primitive
open import Data.One
open import Data.Two
open import Data.Product
open import Coinduction
putBit : 𝟚 → IO 𝟙
putBit 1₂ = putStr "1"
putBit 0₂ = putStr "0"
putBits : ∀ {n} → Vec 𝟚 n → IO 𝟙
putBits [] = return _
putBits (x ∷ bs) = ♯ putBit x >> ♯ putBits bs
put× : ∀ {A B : Set} → (A → IO 𝟙) → (B → IO 𝟙) → (A × B) → IO 𝟙
put× pA pB (x , y) = ♯ pA x >> ♯ pB y
{-
main : IO.Primitive.IO 𝟙
main = IO.run (put× putBits (put× putBits (put× putBits (put× putBits
          putBits))) AgdaSHA1.SHA1-on-0s)
-}
firstBit : ∀ {A : Set} → (V.Vec 𝟚 32 × A) → 𝟚
firstBit ((b ∷ _) , _) = b
main : IO.Primitive.IO 𝟙
--main = IO.run (putBit (firstBit (AgdaSHA1.SHA1-on-0s _)))
main = IO.run (putStrLn (show sha1-cost))
-}

-- -}
