open import Type
open import Function
open import Data.Nat.NP using (ℕ)
open import Data.Fin.NP using (Fin)
open import Data.Vec.NP using (Vec; []; _∷_; lookup) renaming (map to vmap)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Relation.Binary.PropositionalEquality using (_≡_; _≗_; refl)
open import Category.Monad.NP

open import Language.Simple.Interface

module Language.Simple.Abstract (Op : ℕ → ★) where

data E (I : ★) : ★ where
  var : I → E I
  op  : ∀ {a} (o : Op a) (es : Vec (E I) a) → E I

rawMonad : RawMonad E
rawMonad = record { return = var; _>>=_ = _>>=_ }
  module MonadInternals where
    _>>=_  : ∀ {I J} → E I → (I → E J) → E J
    _>>=*_ : ∀ {n I J} → Vec (E I) n → (I → E J) → Vec (E J) n

    var x   >>= f = f x
    op o es >>= f = op o (es >>=* f)

    []       >>=* f = []
    (x ∷ es) >>=* f = x >>= f ∷ es >>=* f

isMonadic : IsMonadic rawMonad
isMonadic = record { return->>= = return->>=; >>=-return = >>=-return; >>=-assoc = >>=-assoc }
  where
    open MonadInternals using (_>>=_; _>>=*_)

    return->>= : ∀ {I J} (f : I → E J) x → (var x >>= f) ≡ f x
    return->>= _ _ = refl

    >>=-return  : ∀ {i} (e : E i) → (e >>= var) ≡ e
    >>=*-return : ∀ {n i} (es : Vec (E i) n) → (es >>=* var) ≡ es

    >>=-return (var x) = refl
    >>=-return (op o es) rewrite >>=*-return es = refl

    >>=*-return [] = refl
    >>=*-return (x ∷ es) rewrite >>=-return x | >>=*-return es = refl

    >>=-assoc : ∀ {A B C} (mx : E A) (my : A → E B) (k : B → E C)
                → (mx >>= λ x → my x >>= k) ≡ ((mx >>= my) >>= k)
    >>=*-assoc : ∀ {n A B C} (mxs : Vec (E A) n) (my : A → E B) (k : B → E C)
                 → (mxs >>=* λ x → my x >>= k) ≡ ((mxs >>=* my) >>=* k)

    >>=-assoc (var x)    my k = refl
    >>=-assoc (op o mxs) my k rewrite >>=*-assoc mxs my k = refl

    >>=*-assoc []         my k = refl
    >>=*-assoc (mx ∷ mxs) my k rewrite >>=-assoc mx my k | >>=*-assoc mxs my k = refl

monad : Monad E
monad = _ , isMonadic

module _ {A : ★} (evalOp : ∀ {n} → Op n → Vec A n → A) where
  module _ {I} (f : I → A) where

    eval  : E I → A
    eval* : ∀ {n} → Vec (E I) n → Vec A n

    eval (var x)   = f x
    eval (op o es) = evalOp o (eval* es)

    eval* []       = []
    eval* (x ∷ es) = eval x ∷ eval* es

  open EvalSupport monad eval
  open MonadInternals using (_>>=*_)

  evalˢ* : ∀ {n} → Vec (E A) n → Vec A n
  evalˢ* = eval* id

  evalᶠ* : ∀ {n i} → Vec (E (Fin i)) n → Vec A i → Vec A n
  evalᶠ* e vs = eval* (λ x → lookup x vs) e

  module _ {i j} (f : i →ᵉ j) where

    eval1-∘  :       (e  :      E (Fin j))    → evalᶠ  (e  >>=  f) ≗ evalᶠ  e  ∘ evalᵛ f
    eval1-∘* : ∀ {n} (es : Vec (E (Fin j)) n) → evalᶠ* (es >>=* f) ≗ evalᶠ* es ∘ evalᵛ f

    eval1-∘ (var v)   x rewrite lookup∘tabulate (λ y → evalᶠ (f y) x) v = refl
    eval1-∘ (op o es) x rewrite eval1-∘* es x = refl

    eval1-∘* []       x = refl
    eval1-∘* (e ∷ es) x rewrite eval1-∘ e x | eval1-∘* es x = refl

  has-eval : Eval A monad
  has-eval = eval , eval1-∘
