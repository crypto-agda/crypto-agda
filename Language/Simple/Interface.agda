open import Level.NP
open import Type
open import Function
open import Data.Product using (proj₂)
open import Data.Two as Two
open import Data.Nat.NP using (ℕ; _+_; _*_; module ℕ°)
open import Data.Fin.NP as Fin using (Fin; inject+; raise)
open import Data.Vec.NP using (Vec; []; _∷_; lookup; tabulate; tabulate-ext; reverse; transpose; rewire) renaming (map to vmap)
open import Data.Vec.Properties using (lookup∘tabulate; tabulate∘lookup)
open import Category.Monad.NP
open import Relation.Binary.PropositionalEquality.NP

module Language.Simple.Interface where

module LangSupportFin (E : ★ → ★) where
  _→ᵉ_ : (i o : ℕ) → ★₀
  i →ᵉ o = Fin o → E (Fin i)

  --efinFunU : FunUniverse ℕ
  --efinFunU = Bits-U , _→ᵉ_

_→ᵛ_ : ∀ {A} → (i o : ℕ) → ★
_→ᵛ_ {A} i o = Vec A i → Vec A o

module EvalSupport {R : ★₀} {E : ★₀ → ★₀}
    (monad : Monad E)
    (eval : ∀ {A} → (A → R) → E A → R) where
  open Monad monad
  open LangSupportFin E public

  evalᶠ : ∀ {i} → E (Fin i) → Vec R i → R
  evalᶠ e vs = eval (λ x → lookup x vs) e

  idᵉ : ∀ {i} → i →ᵉ i
  idᵉ = return

  _∘ᵉ_ : ∀ {i j k} → (j →ᵉ k) → (i →ᵉ j) → (i →ᵉ k)
  (f ∘ᵉ g) x = f x >>= g

  evalᵛ : ∀ {i o} → i →ᵉ o → i →ᵛ o
  evalᵛ f is = tabulate (flip evalᶠ is ∘ f)

  evalˢ : E R → R
  evalˢ = eval id

module FromEvalSimple {R : ★} {E : ★ → ★}
                      (monad : Monad E)
                      (evalˢ : E R → R) where
  open Monad monad
  eval : ∀ {V} → (V → R) → E V → R
  eval f x = evalˢ (liftM f x)

record Eval (R : ★) {E : ★ → ★} (monad : Monad E) : ★₁ where
  constructor mk
  open Monad monad
  field
    eval : ∀ {V} → (V → R) → E V → R

    eval-return : ∀ {A} (f : A → R) → eval f ∘ return ≗ f

    eval->>= : ∀ {A B} (f : B → R) (g : A → E B) e
               → eval (eval f ∘ g) e ≡ eval f (e >>= g)

    eval-ext : ∀ {A} {f g : A → R} → f ≗ g → eval f ≗ eval g

  eval-map : ∀ {A B} (f : B → R) (g : A → B) e
             → eval (f ∘ g) e ≡ eval f (g <$> e)
  eval-map _ _ _ = eval-ext (λ _ → ! (eval-return _ _)) _
                 ∙ eval->>= _ _ _
                 ∙ ap (eval _) (! (<$>-liftM _ _))

  -- In particular any eval can be expressed as the combination
  -- of evalˢ (a.k.a. eval id) and functoriality (<$>).
  eval-id : ∀ {A} (f : A → R) (e : E A)
            → eval f e ≡ eval id (f <$> e)
  eval-id = eval-map id

  open EvalSupport monad eval

  ∘ᵉ-assoc : ∀ {i j k ℓ} (f : k →ᵉ ℓ) (g : j →ᵉ k) (h : i →ᵉ j) → f ∘ᵉ (g ∘ᵉ h) ≗ (f ∘ᵉ g) ∘ᵉ h
  ∘ᵉ-assoc f g h x = >>=-assoc (f x) g h

  -- Derived properties of evalˢ (a.k.a. eval id)

  evalˢ-return : evalˢ ∘ return ≗ id
  evalˢ-return = eval-return id

  evalˢ->>= : ∀ {A} (g : A → E R) e
              → evalˢ ((evalˢ ∘ g) <$> e) ≡ evalˢ (e >>= g)
  evalˢ->>= _ _ = ! (eval-id _ _) ∙ eval->>= id _ _

  -- Model ()

  evalᵛ-id : ∀ {i} → evalᵛ {i} idᵉ ≗ id
  evalᵛ-id _ = tabulate-ext (eval-return _) ∙ tabulate∘lookup _

  evalᵛ-∘ : ∀ {i j k} (f : j →ᵉ k) (g : i →ᵉ j)
            → evalᵛ f ∘ evalᵛ g ≗ evalᵛ (f ∘ᵉ g)
  evalᵛ-∘ _ _ _ = tabulate-ext (λ _ →
                    eval-ext (lookup∘tabulate _) _
                    ∙ eval->>= _ _ _)

  open EvalSupport monad eval public

EvalOp : (Op : ℕ → ★) (R : ★) → ★
EvalOp Op R = ∀ {a} (o : Op a) (es : Vec R a) → R

-- 'n' is the length of vectors used as the values.
module VecOps (Op : ℕ → ★) R (evalOp : EvalOp Op R) (n : ℕ) where
  data VecOp : ℕ → ★ where
    `map : ∀ {a} → Op a → VecOp a
    `id `reverse : VecOp 1
    `rewire : (Fin n → Fin n) → VecOp 1
  evalVecOp : EvalOp VecOp (Vec R n)
  evalVecOp (`map o)     xs       = vmap (evalOp o) (transpose xs)
  evalVecOp (`rewire π) (xs ∷ []) = rewire π xs
  evalVecOp `id         (xs ∷ []) = xs
  evalVecOp `reverse    (xs ∷ []) = reverse xs

record Lang (Op : ℕ → ★) R (E : ★ → ★) : ★₁ where
  field
    monad    : Monad E
    op       : ∀ {A} → EvalOp Op (E A)
    evalOp   : EvalOp Op R
    has-eval : Eval R monad

  open Monad monad
  open Eval has-eval

  field
    eval-op : ∀ {A} (f : A → R)
                {n} (o : Op n) es
              → eval f (op o es) ≡ evalOp o (vmap (eval f) es)

  -- One can see the I type as describe the inputs we can read from.
  -- Therefore 'return' can not only be seen as the variable case but
  -- as 'read from input i'
  input : ∀ {I} → I → E I
  input = return

  open Monad monad   public
  open Eval has-eval public
-- -}
-- -}
-- -}
