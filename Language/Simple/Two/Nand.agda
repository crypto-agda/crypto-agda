open import Type
open import Function
open import Data.Two renaming (nand to nand₂)
open import Data.Product
open import Data.Nat.NP using (ℕ; _+_)
open import Data.Fin.NP using (Fin; inject+; raise)
open import Data.Bits   using (Bits)
open import Data.Vec.NP using (Vec; []; _∷_; lookup; tabulate)
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

has-eval : Eval 𝟚 monad
has-eval = eval , eval1-∘
  where
    module _ {I} (f : I → 𝟚) where
        eval : E I → 𝟚
        eval (var x)      = f x
        eval (nand e₀ e₁) = nand₂ (eval e₀) (eval e₁)
        eval 0₂           = 0₂
        eval 1₂           = 1₂

    open EvalSupport monad eval

    module _ {i j} (f : i →ᵉ j) where
        eval1-∘ : (e : E (Fin j)) → evalᶠ (e >>= f) ≗ evalᶠ e ∘ evalᵛ f
        eval1-∘ (var v)      x rewrite lookup∘tabulate (λ y → evalᶠ (f y) x) v = refl
        eval1-∘ (nand e₀ e₁) x rewrite eval1-∘ e₀ x | eval1-∘ e₁ x = refl
        eval1-∘ 0₂ _ = refl
        eval1-∘ 1₂ _ = refl

lang : Lang Op 𝟚 E
lang = record { monad = monad; has-eval = has-eval; op = op }
  where
    op : ∀ {V a} (o : Op a) (es : Vec (E V) a) → E V
    op nand (x ∷ y ∷ []) = nand x y
    op 0₂   []           = 0₂
    op 1₂   []           = 1₂
