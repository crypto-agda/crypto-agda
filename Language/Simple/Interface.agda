open import Type
open import Function
open import Data.Product using (proj₂)
open import Data.Two as Two
open import Data.Nat.NP using (ℕ; _+_; _*_; module ℕ°)
open import Data.Fin.NP as Fin using (Fin; inject+; raise)
open import Data.Vec.NP using (Vec; []; _∷_; lookup; tabulate; tabulate-ext)
open import Category.Monad.NP
open import Relation.Binary.PropositionalEquality

module Language.Simple.Interface where

module LangSupportFin (E : ★ → ★) where
  _→ᵉ_ : (i o : ℕ) → ★
  i →ᵉ o = Fin o → E (Fin i)

  --efinFunU : FunUniverse ℕ
  --efinFunU = Bits-U , _→ᵉ_

_→ᵛ_ : ∀ {A} → (i o : ℕ) → ★
_→ᵛ_ {A} i o = Vec A i → Vec A o

module EvalSupport {A : ★} {E : ★ → ★}
    (monad : Monad E)
    (eval : ∀ {V} → (V → A) → E V → A) where
  open Monad monad      public
  open LangSupportFin E public

  evalᶠ : ∀ {i} → E (Fin i) → Vec A i → A
  evalᶠ e vs = eval (λ x → lookup x vs) e

  _∘ᵉ_ : ∀ {i j k} → (j →ᵉ k) → (i →ᵉ j) → (i →ᵉ k)
  (f ∘ᵉ g) x = f x >>= g

  evalᵛ : ∀ {i o} → i →ᵉ o → i →ᵛ o
  evalᵛ f is = tabulate (flip evalᶠ is ∘ f)

  evalˢ : E A → A
  evalˢ = eval id

module FromEvalSimple {A : ★} {E : ★ → ★}
                      (monad : Monad E)
                      (evalˢ : E A → A) where
  open Monad monad
  eval : ∀ {V} → (V → A) → E V → A
  eval f x = evalˢ (liftM f x)

record Eval A {E} (monad : Monad E) : ★₁ where
  constructor _,_
  field
    eval : ∀ {V} → (V → A) → E V → A

  open EvalSupport monad eval

  {-
  field
    foo : ∀ (f : A → E A) (e : E A) → evalˢ (e >>= f) ≡ evalˢ (f (evalˢ e))
    bar : ∀ {B} (g : B → A) (f : A → E B) (e : E A) → eval g (e >>= f) ≡ eval g (f (eval id e))
  -}

  field
    eval1-∘ : ∀ {i j} (f : i →ᵉ j) (e : E (Fin j)) → evalᶠ (e >>= f) ≗ evalᶠ e ∘ evalᵛ f
  -- eval1-∘ f e xs = {!bar (λ x → lookup x xs) !}

  ∘ᵉ-assoc : ∀ {i j k ℓ} (f : k →ᵉ ℓ) (g : j →ᵉ k) (h : i →ᵉ j) → f ∘ᵉ (g ∘ᵉ h) ≗ (f ∘ᵉ g) ∘ᵉ h
  ∘ᵉ-assoc f g h x = >>=-assoc (f x) g h

  eval-∘ : ∀ {i j k} (f : j →ᵉ k) (g : i →ᵉ j) → evalᵛ (f ∘ᵉ g) ≗ evalᵛ f ∘ evalᵛ g
  eval-∘ f g x = tabulate-ext (λ y → eval1-∘ g (f y) x)

  open EvalSupport monad eval public

record Lang (Op : ℕ → ★) A (E : ★ → ★) : ★₁ where
  field
    monad    : Monad E
    op       : ∀ {V a} (o : Op a) (es : Vec (E V) a) → E V
    has-eval : Eval A monad

  open Eval has-eval public

  -- One can see the I type as describe the inputs we can read from.
  -- Therefore 'return' can not only be seen as the variable case but
  -- as 'read from input i'
  input : ∀ {I} → I → E I
  input = return
