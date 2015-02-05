module Control.Strategy where

open import Data.Nat
open import Function.NP
open import Type using (★)
open import Category.Monad
open import Data.Product hiding (map)
open import Data.List as List using (List; []; _∷_)
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

  module Repeat {I O : ★} where

    ind : (I → M O) → List I → M (List O)
    ind g [] = done []
    ind g (x ∷ xs) = g x >>= (λ o → map (_∷_ o) (ind g xs))

    module _ (Oracle : (q : Q) → R q)(g : I → M O) where
      run-ind : ∀ xs → run Oracle (ind g xs) ≡ List.map (run Oracle ∘ g) xs
      run-ind [] = refl
      run-ind (x ∷ xs) = run->>= Oracle (λ o → map (_∷_ o) (ind g xs)) (g x)
                       ∙ run-map Oracle (_∷_ (run Oracle (g x))) (ind g xs)
                       ∙ ap (_∷_ (run Oracle (g x))) (run-ind xs)

  module RepeatIndex {O : ★} where

    map-list : (ℕ → (q : Q) → R q → O) → List Q → M (List O)
    map-list _ [] = done []
    map-list f (x ∷ xs) = ask x λ r → map (_∷_ (f 0 x r)) (map-list (f ∘ suc) xs)

    -- belongs to list
    mapIndex : {A B : Set} → (ℕ → A → B) → List A → List B
    mapIndex f []       = []
    mapIndex f (x ∷ xs) = f 0 x ∷ mapIndex (f ∘ suc) xs

    module _ (Oracle : (q : Q) → R q) where
      run-map-list : ∀ xs (g : ℕ → (q : Q) → R q → O) → run Oracle (map-list g xs) ≡ mapIndex (λ i q → g i q (Oracle q)) xs
      run-map-list [] _       = refl
      run-map-list (x ∷ xs) g = run-map Oracle (_∷_ (g 0 x (Oracle x))) (map-list (g ∘ suc) xs) ∙ ap (_∷_ (g 0 x (Oracle x))) (run-map-list xs (g ∘ suc))

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

  private
    Transcript = List (Σ Q R)
  module TranscriptRun (Oracle : Transcript → Π Q R){A} where
    runT : M A → Transcript → A × Transcript
    runT (ask q? cont) t = let r = Oracle t q? in runT (cont r) ((q? , r) ∷ t)
    runT (done x)      t = x , t

    open StatefulRun
    -- runT is runS where the state is the transcript and the Oracle cannot change it
    runT-runS : ∀ (str : M A) t → runT str t ≡ runS (λ q s → let r = Oracle s q in r , (q , r) ∷ s) str t
    runT-runS (ask q? cont) t = let r = Oracle t q? in runT-runS (cont r) ((q? , r) ∷ t)
    runT-runS (done x)      t = refl

  module TranscriptConstRun (Oracle : Π Q R){A} where
    open TranscriptRun
    runT-run : ∀ (str : M A) {t} → proj₁ (runT (const Oracle) str t) ≡ run Oracle str
    runT-run (ask q? cont) = let r = Oracle q? in runT-run (cont r)
    runT-run (done x) = refl
-- -}
-- -}
-- -}
-- -}
