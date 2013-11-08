module Control.Strategy where

open import Function
open import Type using (★)
open import Category.Monad
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality.NP

data Strategy (Q : ★) (R : Q → ★) (A : ★) : ★ where
  ask  : (q? : Q) (cont : R q? → Strategy Q R A) → Strategy Q R A
  done : A → Strategy Q R A

infix 2 _≈_
data _≈_ {Q R A} : (s₀ s₁ : Strategy Q R A) → ★ where
  ask-ask : ∀ (q? : Q) {k₀ k₁} (cont : ∀ r → k₀ r ≈ k₁ r) → ask q? k₀ ≈ ask q? k₁
  done-done : ∀ x → done x ≈ done x

≈-refl : ∀ {Q R A} {s : Strategy Q R A} → s ≈ s
≈-refl {s = ask q? cont} = ask-ask q? (λ r → ≈-refl)
≈-refl {s = done x}      = done-done x

module _ {Q : ★} {R : Q → ★} where
  private
    M : ★ → ★
    M = Strategy Q R

  _=<<_ : ∀ {A B} → (A → M B) → M A → M B
  f =<< ask q? cont = ask q? (λ r → f =<< cont r)
  f =<< done x      = f x

  return : ∀ {A} → A → M A
  return = done

  map : ∀ {A B} → (A → B) → M A → M B
  map f s = (done ∘ f) =<< s

  join : ∀ {A} → M (M A) → M A
  join s = id =<< s

  _>>=_ : ∀ {A B} → M A → (A → M B) → M B
  _>>=_ = flip _=<<_

  rawMonad : RawMonad M
  rawMonad = record { return = return; _>>=_ = _>>=_ }

  return-=<< : ∀ {A} (m : M A) → return =<< m ≈ m
  return-=<< (ask q? cont) = ask-ask q? (λ r → return-=<< (cont r))
  return-=<< (done x)      = done-done x

  return->>= : ∀ {A B} (x : A) (f : A → M B) → return x >>= f ≡ f x
  return->>= _ _ = refl

  >>=-assoc : ∀ {A B C} (mx : M A) (my : A → M B) (f : B → M C) → (mx >>= λ x → (my x >>= f)) ≈ (mx >>= my) >>= f
  >>=-assoc (ask q? cont) my f = ask-ask q? (λ r → >>=-assoc (cont r) my f)
  >>=-assoc (done x)      my f = ≈-refl

  map-id : ∀ {A} (s : M A) → map id s ≈ s
  map-id = return-=<<

  map-∘ : ∀ {A B C} (f : A → B) (g : B → C) s → map (g ∘ f) s ≈ (map g ∘ map f) s
  map-∘ f g s = >>=-assoc s (done ∘ f) (done ∘ g)

  module EffectfulRun
           (E : ★ → ★)
           (_>>=E_  : ∀ {A B} → E A → (A → E B) → E B)
           (returnE : ∀ {A} → A → E A)
           (Oracle  : (q : Q) → E (R q)) where
    runE : ∀ {A} → M A → E A
    runE (ask q? cont) = Oracle q? >>=E (λ r → runE (cont r))
    runE (done x)      = returnE x

  module _ (Oracle : (q : Q) → R q) where
    run : ∀ {A} → M A → A
    run (ask q? cont) = run (cont (Oracle q?))
    run (done x)      = x

    module _ {A B : ★} (f : A → M B) where
        run->>= : (s : M A) → run (s >>= f) ≡ run (f (run s))
        run->>= (ask q? cont) = run->>= (cont (Oracle q?))
        run->>= (done x)      = refl

    module _ {A B : ★} (f : A → B) where
        run-map : (s : M A) → run (map f s) ≡ f (run s)
        run-map = run->>= (return ∘ f) 

    module _ {A B : ★} where
        run-≈ : {s₀ s₁ : M A} → s₀ ≈ s₁ → run s₀ ≡ run s₁
        run-≈ (ask-ask q? cont) = run-≈ (cont (Oracle q?))
        run-≈ (done-done x)     = refl

  private
    State : (S A : ★) → ★
    State S A = S → A × S

  -- redundant since we have EffectfulRun, but...
  module StatefulRun {S : ★} (Oracle : (q : Q) → State S (R q)) where
    runS : ∀ {A} → M A → State S A
    runS (ask q? cont) s = case Oracle q? s of λ { (x , s') → runS (cont x) s' }
    runS (done x)      s = x , s

    evalS : ∀ {A} → M A → S → A
    evalS x s = proj₁ (runS x s)

    execS : ∀ {A} → M A → S → S
    execS x s = proj₂ (runS x s)
-- -}
-- -}
-- -}
-- -}
