open import Type
open import Function
open import Data.Two renaming (mux to mux₂)
open import Data.Product
open import Data.Nat.NP using (ℕ; _+_)
open import Data.Fin.NP using (Fin; inject+; raise)
open import Data.Vec.NP using (Vec; []; _∷_; lookup; tabulate)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Data.Bits   using (Bits)
open import Relation.Binary.PropositionalEquality
open import Category.Monad.NP

module Language.Simple.Two.Mux where

open import Language.Simple.Interface

data E (I : ★) : ★ where
  var   : I → E I
  mux   : (c e₀ e₁ : E I) → E I
  0₂ 1₂ : E I

rawMonad : RawMonad E
rawMonad = record { return = var ; _>>=_ = _>>=_ }
  where
    _>>=_ : ∀ {I J} → E I → (I → E J) → E J
    var x       >>= f = f x
    mux c e₀ e₁ >>= f = mux (c >>= f) (e₀ >>= f) (e₁ >>= f)
    0₂          >>= f = 0₂
    1₂          >>= f = 1₂

isMonadic : IsMonadic rawMonad
isMonadic = record { return->>= = return->>=; >>=-return = >>=-return; >>=-assoc = >>=-assoc }
  where
    open RawMonad rawMonad
    return->>= : ∀ {I J} (f : I → E J) x → (return x >>= f) ≡ f x
    return->>= _ _ = refl

    >>=-return : ∀ {i} (e : E i) → (e >>= return) ≡ e
    >>=-return (var x) = refl
    >>=-return (mux e₀ e₁ e₂) rewrite >>=-return e₀
                                    | >>=-return e₁
                                    | >>=-return e₂
                                    = refl
    >>=-return 0₂ = refl
    >>=-return 1₂ = refl

    >>=-assoc : ∀ {A B C} (mx : E A) (my : A → E B) (k : B → E C)
          → (mx >>= λ x → my x >>= k) ≡ ((mx >>= my) >>= k)
    >>=-assoc (var x) my k = refl
    >>=-assoc (mux mx₀ mx₁ mx₂) my k rewrite >>=-assoc mx₀ my k
                                           | >>=-assoc mx₁ my k
                                           | >>=-assoc mx₂ my k
                                           = refl
    >>=-assoc 0₂ my k = refl
    >>=-assoc 1₂ my k = refl

monad : Monad E
monad = rawMonad , isMonadic

has-eval : Eval 𝟚 monad
has-eval = eval , eval1-∘
  where
    module _ {I} (f : I → 𝟚) where
        eval : E I → 𝟚
        eval (var x)       = f x
        eval 0₂            = 0₂
        eval 1₂            = 1₂
        eval (mux c e₀ e₁) = mux₂ (eval c , (eval e₀ , eval e₁))

    open EvalSupport monad eval

    module _ {i j} (f : i →ᵉ j) where
        eval1-∘ : (e : E (Fin j)) → evalᶠ (e >>= f) ≗ evalᶠ e ∘ evalᵛ f
        eval1-∘ (var x)       y rewrite lookup∘tabulate (λ x → evalᶠ (f x) y) x = refl
        eval1-∘ (mux e e₁ e₂) y rewrite eval1-∘ e y | eval1-∘ e₁ y | eval1-∘ e₂ y = refl
        eval1-∘ 0₂ x = refl
        eval1-∘ 1₂ x = refl

data Op : ℕ → ★ where
  mux   : Op 3
  0₂ 1₂ : Op 0

lang : Lang Op 𝟚 E
lang = record { monad = monad; has-eval = has-eval; op = op }
  where
    op : ∀ {V a} (o : Op a) (es : Vec (E V) a) → E V
    op mux (x ∷ y ∷ z ∷ []) = mux x y z
    op 0₂  []               = 0₂
    op 1₂  []               = 1₂
