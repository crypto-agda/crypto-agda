{-# OPTIONS --without-K #-}
open import Type
open import Function
open import Data.Nat.NP using (ℕ)
open import Data.Fin.NP using (Fin)
open import Data.Vec.NP using (Vec; []; _∷_; lookup) renaming (map to vmap)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Relation.Binary.PropositionalEquality.NP using (_≡_; _≗_; refl; ap; cong₂)
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

    >>=-return (var x)   = refl
    >>=-return (op o es) = ap (op o) (>>=*-return es)

    >>=*-return []       = refl
    >>=*-return (x ∷ es) = cong₂ _∷_ (>>=-return x) (>>=*-return es)

    >>=-assoc : ∀ {A B C} (mx : E A) (my : A → E B) (k : B → E C)
                → (mx >>= λ x → my x >>= k) ≡ ((mx >>= my) >>= k)
    >>=*-assoc : ∀ {n A B C} (mxs : Vec (E A) n) (my : A → E B) (k : B → E C)
                 → (mxs >>=* λ x → my x >>= k) ≡ ((mxs >>=* my) >>=* k)

    >>=-assoc (var x)    my k = refl
    >>=-assoc (op o mxs) my k = ap (op o) (>>=*-assoc mxs my k)

    >>=*-assoc []         my k = refl
    >>=*-assoc (mx ∷ mxs) my k = cong₂ _∷_ (>>=-assoc mx my k) (>>=*-assoc mxs my k)

monad : Monad E
monad = _ , isMonadic

open Monad monad

module WithEvalOp {R : ★} (evalOp : ∀ {n} → Op n → Vec R n → R) where
  module _ {I} (f : I → R) where

    eval  : E I → R
    eval* : ∀ {n} → Vec (E I) n → Vec R n

    eval (var x)   = f x
    eval (op o es) = evalOp o (eval* es)

    eval* []       = []
    eval* (x ∷ es) = eval x ∷ eval* es

    eval*-vmap-eval : ∀ {n} (es : Vec _ n)
                      → eval* es ≡ vmap eval es
    eval*-vmap-eval []       = refl
    eval*-vmap-eval (e ∷ es) = ap (_∷_ (eval e)) (eval*-vmap-eval es)

  open EvalSupport monad eval
  open MonadInternals using (_>>=*_)

  eval-return : ∀ {A} (f : A → R) → eval f ∘ return ≗ f
  eval-return _ _ = refl

  module _ {A B} (f : B → R) (g : A → E B) where
    eval->>= : ∀ e → eval (eval f ∘ g) e ≡ eval f (e >>= g)
    eval->>=* : ∀ {n} (e : Vec _ n) → eval* (eval f ∘ g) e ≡ eval* f (e >>=* g)
    eval->>=  (var x)   = refl
    eval->>=  (op o es) = ap (evalOp o) (eval->>=* es)
    eval->>=* []        = refl
    eval->>=* (x ∷ xs)  = cong₂ _∷_ (eval->>= x) (eval->>=* xs)

  module _ {A} {f g : A → R} (pf : f ≗ g) where
    eval-ext : eval f ≗ eval g
    eval-ext* : ∀ {n} → eval* f {n} ≗ eval* g
    eval-ext  (var x)   = pf x
    eval-ext  (op o es) = ap (evalOp o) (eval-ext* es)
    eval-ext* []        = refl
    eval-ext* (x ∷ xs)  = cong₂ _∷_ (eval-ext x) (eval-ext* xs)

  has-eval : Eval R monad
  has-eval = mk eval eval-return eval->>= eval-ext

  eval-op : ∀ {A} (f : A → R) {n} (o : Op n) es
            → eval f (op o es) ≡ evalOp o (vmap (eval f) es)
  eval-op _ _ _ = ap (evalOp _) (eval*-vmap-eval _ _)

  lang : Lang Op R E
  lang = record { monad = monad
                ; op = op
                ; evalOp = evalOp
                ; has-eval = has-eval
                ; eval-op = eval-op }
