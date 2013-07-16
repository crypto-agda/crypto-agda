open import Type
open import Function
open import Data.Two renaming (nand to nand₂)
open import Data.Product
open import Data.Nat.NP using (ℕ; _+_)
open import Data.Fin.NP using (Fin; inject+; raise)
open import Data.Bits   using (Bits)
open import Data.Vec.NP using (Vec; []; _∷_; lookup; tabulate) renaming (map to vmap)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Relation.Binary.PropositionalEquality
open import Category.Monad.NP

open import Language.Simple.Interface

module Language.Simple.Two.Nand where

data E (I : ★) : ★ where
  var   : I → E I
  nand  : (e₀ e₁ : E I) → E I
  0₂ 1₂ : E I

rawMonad : RawMonad E
rawMonad = record { return = var; _>>=_ = _>>=_ }
  where
    _>>=_ : ∀ {I J} → E I → (I → E J) → E J
    var x    >>= f = f x
    nand e₀ e₁ >>= f = nand (e₀ >>= f) (e₁ >>= f)
    0₂         >>= f = 0₂
    1₂         >>= f = 1₂

isMonadic : IsMonadic rawMonad
isMonadic = record { return->>= = return->>=; >>=-return = >>=-return; >>=-assoc = >>=-assoc }
  where
    open RawMonad rawMonad
    return->>= : ∀ {I J} (f : I → E J) x → (var x >>= f) ≡ f x
    return->>= _ _ = refl

    >>=-return : ∀ {i} (e : E i) → (e >>= var) ≡ e
    >>=-return (var x) = refl
    >>=-return (nand e₀ e₁) rewrite >>=-return e₀
                                  | >>=-return e₁
                                  = refl
    >>=-return 0₂ = refl
    >>=-return 1₂ = refl

    >>=-assoc : ∀ {A B C} (mx : E A) (my : A → E B) (k : B → E C)
          → (mx >>= λ x → my x >>= k) ≡ ((mx >>= my) >>= k)
    >>=-assoc (var x) my k = refl
    >>=-assoc (nand mx₀ mx₁) my k rewrite >>=-assoc mx₀ my k
                                        | >>=-assoc mx₁ my k
                                        = refl
    >>=-assoc 0₂ my k = refl
    >>=-assoc 1₂ my k = refl

monad : Monad E
monad = rawMonad , isMonadic

data Op : ℕ → ★ where
  nand  : Op 2
  0₂ 1₂ : Op 0

open Monad monad

has-eval : Eval 𝟚 monad
has-eval = mk eval eval-return eval->>= eval-ext
  where
    R = 𝟚

    module _ {I} (f : I → R) where
        eval : E I → R
        eval (var x)      = f x
        eval 0₂           = 0₂
        eval 1₂           = 1₂
        eval (nand e₀ e₁) = nand₂ (eval e₀) (eval e₁)

    eval-return : ∀ {A} (f : A → R) → eval f ∘ return ≗ f
    eval-return _ _ = refl

    module _ {A B} (f : B → R) (g : A → E B) where
        eval->>= : ∀ e → eval (eval f ∘ g) e ≡ eval f (e >>= g)
        eval->>= (var x) = refl
        eval->>= (nand e₀ e₁) = cong₂ nand₂ (eval->>= e₀)
                                            (eval->>= e₁)
        eval->>= 0₂ = refl
        eval->>= 1₂ = refl

    module _ {A} {f g : A → R} (pf : f ≗ g) where
        eval-ext : eval f ≗ eval g
        eval-ext (var x) = pf x
        eval-ext (nand e₀ e₁) = cong₂ nand₂ (eval-ext e₀)
                                            (eval-ext e₁)
        eval-ext 0₂ = refl
        eval-ext 1₂ = refl

open Eval has-eval

lang : Lang Op 𝟚 E
lang = record { monad = monad; evalOp = evalOp
              ; has-eval = has-eval; op = op
              ; eval-op = eval-op }
  where
    evalOp : EvalOp Op 𝟚
    evalOp nand (x ∷ y ∷ []) = nand₂ x y
    evalOp 0₂   []           = 0₂
    evalOp 1₂   []           = 1₂

    op : ∀ {A} → EvalOp Op (E A)
    op nand (x ∷ y ∷ []) = nand x y
    op 0₂   []           = 0₂
    op 1₂   []           = 1₂

    R = 𝟚
    module _ {A} (f : A → R) where
      eval-op : ∀ {n} (o : Op n) es
                → eval f (op o es) ≡ evalOp o (vmap (eval f) es)
      eval-op nand (x ∷ y ∷ []) = refl
      eval-op 0₂   []           = refl
      eval-op 1₂   []           = refl
