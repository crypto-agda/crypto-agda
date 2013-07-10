{-# OPTIONS --without-K #-}
module prefect-bintree-sorting where
open import Type
import Level as L
open import Function.NP
import Data.Nat.NP as Nat
open Nat using (ℕ; zero; suc; 2^_; _+_; _∸_; module ℕ°; module ℕ≤; +-≤-inj; ¬n+≤y<n; sucx≰x; ¬n≤x<n; module ℕcmp) renaming (module <= to ℕ<=; _<=_ to _ℕ<=_)
open import Data.Bool.NP hiding (toℕ)
open import Data.Sum
open import Data.Bits
open import Data.Bits.Count
open import Data.Unit using (⊤)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; uncurry) renaming (swap to swap-×)
open import Data.Vec.NP using (Vec; _++_; module Alternative-Reverse; shallow-η)
open import Relation.Nullary
open import Relation.Binary
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_; _≗_; module ≡-Reasoning; [_])
open import Algebra.FunctionProperties
import Relation.Binary.ToNat as ToNat
open import prefect-bintree
open import Data.Nat.Properties
open Nat using (z≤n; s≤s; ≤-pred; 2*_; 2*′_; 2*-spec; 2*′-spec; suc-injective) renaming (_≤_ to _ℕ≤_; _<_ to _ℕ<_)

module MM where
 open Nat using (_≤_; _<_)
 split-≤ : ∀ {x y} → x ≤ y → x ≡ y ⊎ x < y
 split-≤ {zero} {zero} p = inj₁ ≡.refl
 split-≤ {zero} {suc y} p = inj₂ (s≤s z≤n)
 split-≤ {suc x} {zero} ()
 split-≤ {suc x} {suc y} (s≤s p) with split-≤ {x} {y} p
 ... | inj₁ q rewrite q = inj₁ ≡.refl
 ... | inj₂ q = inj₂ (s≤s q)

 <→≤ : ∀ {x y} → x < y → x ≤ y
 <→≤ (s≤s p) = ≤-steps 1 p

 Monotone : ℕ → Endo ℕ → ★
 Monotone ub f = ∀ {x y} → x ≤ y → y < ub → f x ≤ f y

 IsInj : ℕ → Endo ℕ → ★
 IsInj ub f = ∀ {x y} → x < ub → y < ub → f x ≡ f y → x ≡ y

 Bounded : ℕ → Endo ℕ → ★
 Bounded ub f = ∀ x → x < ub → f x < ub

 module M (f : ℕ → ℕ) {ub}
          (f-mono : Monotone ub f)
          (f-inj : IsInj ub f)
          (f-bounded : Bounded ub f) where

  f-mono-< : ∀ {x y} → x < y → y < ub → f x < f y
  f-mono-< {x} {y} p y<ub with split-≤ (f-mono {x} {y} (<→≤ p) y<ub)
  ... | inj₁ q = ⊥-elim (sucx≰x y (≡.subst (λ z → suc z ℕ≤ y) (f-inj {x} {y} (<-trans p y<ub) y<ub q) p))
  ... | inj₂ q = q

  le : ∀ n → suc n < ub → f (suc n) ≤ n → f n < n
  le n 1+n<ub p = ℕ≤.trans (f-mono-< {n} {suc n} ℕ≤.refl 1+n<ub) p

  fp : ∀ b → b < ub → Bounded (suc b) f → f b ≡ b
  fp b b<ub bub with split-≤ (bub b ℕ≤.refl)
  ... | inj₁ p = suc-injective p
  ... | inj₂ p = ⊥-elim (bo b b<ub (≤-pred p))
    where
      bo : ∀ b → b < ub → ¬(f b < b)
      bo zero _ ()
      bo (suc b) b<ub (s≤s p) = bo b (ℕ≤.trans (s≤s (≤-step ℕ≤.refl)) b<ub) (le b b<ub p)

  ob : ∀ b → b ≤ ub → Bounded b f → ∀ x → x < b → f x ≡ x
  ob zero b≤ub bub _ ()
  ob (suc b) b≤ub bub x pf with split-≤ pf
  ... | inj₁ p rewrite suc-injective p = fp b b≤ub bub
  ... | inj₂ (s≤s p) = ob b (<→≤ b≤ub) ((λ y y<b → ℕ≤.trans (f-mono-< y<b b≤ub) (ℕ≤.reflexive (fp b b≤ub bub)))) x p

  is-id : ∀ x → x < ub → f x ≡ x
  is-id = ob ub ℕ≤.refl f-bounded

open BitsSorting
open import Data.Bits.OperationSyntax
open BijSpec
open EvalTree
open Alternative-Reverse

sortBijT : ∀ {n} → Tree (Bits n) n → Bij n
sortBijT = bij ∘ sort-bij

sortBij : ∀ {n} → Endo (Bits n) → Bij n
sortBij = sortBijT ∘ fromFun

sortBij-sort : ∀ {n} (t : Tree (Bits n) n) → evalTree (sortBijT t) t ≡ sort t
sortBij-sort = proof ∘ sort-bij

IsInj : ∀ {i o} → (Bits i → Bits o) → ★
IsInj f = ∀ {x y} → f x ≡ f y → x ≡ y

idT : ∀ {n} → Tree (Bits n) n
idT = fromFun id

toFun-idT : ∀ {n} → toFun idT ≗ id {A = Bits n}
toFun-idT x = toFun∘fromFun id x

InjT : ∀ {n} → Tree (Bits n) n → ★
InjT = IsInj ∘ toFun

_⁻¹-inverseTree : ∀ {n} f → evalTree (f `⁏ f ⁻¹) ≗ id {A = Tree (Bits n) n}
(f ⁻¹-inverseTree) t = evalTree (f `⁏ f ⁻¹) t
                     ≡⟨ ≡.sym (fromFun∘toFun (evalTree (f `⁏ f ⁻¹) t)) ⟩
                       fromFun (toFun (evalTree (f `⁏ f ⁻¹) t))
                     ≡⟨ fromFun-≗ (evalTree-eval′ (f `⁏ f ⁻¹) t) ⟩
                       fromFun (toFun t ∘ eval (f ⁻¹ ⁻¹ `⁏ f ⁻¹))
                     ≡⟨ fromFun-≗ (λ x → ≡.cong (toFun t) (VecBijKit._⁻¹-inverse′ _ (f ⁻¹) x)) ⟩
                       fromFun (toFun t)
                     ≡⟨ fromFun∘toFun t ⟩
                       t
                     ∎ where open ≡-Reasoning

module SortedMonotonicFunctionsBits {n} where
    open SortedMonotonicFunctions (_≤_ {n}) isPreorder public
open SortedMonotonicFunctionsBits hiding (Sorted)

-- _∘-inj_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} {f : B → C} {g : A → B} → IsInj f → IsInj g → IsInj (f ∘ g)
_∘-inj_ : ∀ {a b c} {f : Bits b → Bits c} {g : Bits a → Bits b} → IsInj f → IsInj g → IsInj (f ∘ g)
f-inj ∘-inj g-inj = g-inj ∘ f-inj

_∷-inj : ∀ {n} b → IsInj (_∷_ {n = n} b)
(_ ∷-inj) ≡.refl = ≡.refl

lemvec : ∀ {n} (xs ys : Bits (suc n)) → head xs ≡ head ys → tail xs ≡ tail ys → xs ≡ ys
lemvec (x ∷ xs) (.x ∷ .xs) ≡.refl ≡.refl = ≡.refl

≤→≤ᴮ : ∀ {n} {x y : Bits n} → x ≤ y → x ≤ᴮ y
≤→≤ᴮ {x = []}         {[]}         p = []
≤→≤ᴮ {suc n} {true ∷ xs}  {true ∷ ys}  p = there 1b (≤→≤ᴮ {x = xs} {ys} (ℕ<=.complete {toℕ xs} {toℕ ys} (+-≤-inj (2^ n) (ℕ<=.sound _ _ p))))
≤→≤ᴮ {x = false ∷ xs} {false ∷ ys} p = there 0b (≤→≤ᴮ {x = xs} {ys} p)
≤→≤ᴮ {suc n} {true ∷ xs}  {false ∷ ys} p = ⊥-elim (2ⁿ+≰toℕ ys (ℕ<=.sound (2^ n + toℕ xs) (toℕ ys) p))
≤→≤ᴮ {x = false ∷ xs} {true ∷ ys}  p = 0-1 xs ys

≤ᴮ→≤ : ∀ {n} {x y : Bits n} → x ≤ᴮ y → x ≤ y
≤ᴮ→≤ [] = _
≤ᴮ→≤ {suc n} (there true p) = ℕ<=.complete (ℕ≤.refl {2^ n} +-mono (ℕ<=.sound _ _ (≤ᴮ→≤ p)))
≤ᴮ→≤ (there false p) = ≤ᴮ→≤ p
≤ᴮ→≤ (0-1 p q) = ℕ<=.complete (toℕ≤2ⁿ+ p {toℕ q})

Monotone' : ∀ {i o} → (Bits i → Bits o) → Set _
Monotone' {i} {o} f = ∀ {p q : Bits i} → p ≤ᴮ q → f p ≤ᴮ f q

toEndoℕ : ∀ {n} → Endo (Bits n) → Endo ℕ
toEndoℕ f = toℕ ∘ f ∘ fromℕ

open Nat using (_≰_)

module ToEndoℕ {n} (f : Endo (Bits n)) where
    fℕ = toEndoℕ f

    fromℕn = fromℕ {n}

    mono : Monotone f → MM.Monotone (2^ n) fℕ
    mono f-mono {x} {y} x≤y y<2ⁿ
       = ℕ<=.sound _ _
          (f-mono
            (≤→≤ᴮ (ℕ<=.complete {toℕ (fromℕn x)} {toℕ (fromℕn y)}
                     (ℕ≤.trans (ℕ≤.reflexive (toℕ∘fromℕ {n} x (ℕ≤.trans (s≤s x≤y) y<2ⁿ)))
                        (ℕ≤.trans x≤y (ℕ≤.reflexive (≡.sym (toℕ∘fromℕ {n} y y<2ⁿ))))))))

    inj : IsInj f → MM.IsInj (2^ n) fℕ
    inj f-inj {x} {y} x< y< = fromℕ-inj x< y< ∘ f-inj ∘ toℕ-inj _ _

    bounded : MM.Bounded (2^ n) fℕ
    bounded x x≤2ⁿ = toℕ-bound (f (fromℕ x))

lem : ∀ {n} (f : Endo (Bits n)) → Monotone f → IsInj f → toℕ ∘ f ≗ toℕ
lem {n} f f-mono f-inj x = ≡.trans (≡.cong (toℕ ∘ f) (≡.sym (fromℕ∘toℕ x)))
                                   (MM.M.is-id (toEndoℕ f) {2^ n} (mono f-mono) (inj f-inj) bounded (toℕ x) (toℕ-bound x))
  where open ToEndoℕ f

IsInj-toFunFromFun : ∀ {n} (f : Endo (Bits n)) → IsInj f → IsInj (toFun (fromFun f))
IsInj-toFunFromFun f f-inj {x} {y} eq
  rewrite toFun∘fromFun f x
        | toFun∘fromFun f y
        = f-inj eq

sort-spec′ : ∀ {n} (t : Tree (Bits n) n) → Sorted (evalTree (sortBijT t) t)
sort-spec′ t rewrite sortBij-sort t = sort-spec t

sort-id′′ : ∀ {n} (t : Tree (Bits n) n) → InjT t → Sorted t → toFun t ≗ id
sort-id′′ t Pt st x = toℕ-inj _ _ (lem (toFun t) (DataSorted→Sorted st) Pt x)

toFun-eval-inj : ∀ {n} (f : Bij n) → IsInj (eval f)
toFun-eval-inj f {x} {y} eq = x
                            ≡⟨ ≡.sym ((f ⁻¹-inverse) x) ⟩
                              eval (f ⁻¹) (eval f x)
                            ≡⟨ ≡.cong (eval (f ⁻¹)) eq ⟩
                              eval (f ⁻¹) (eval f y)
                            ≡⟨ (f ⁻¹-inverse) y ⟩
                              y
                            ∎ where open ≡-Reasoning

toFun-evalTree-inj : ∀ {n} f (t : Tree (Bits n) n) → InjT t → InjT (evalTree f t)
toFun-evalTree-inj f t Pt {x} {y} eq
  rewrite evalTree-eval′ f t x
        | evalTree-eval′ f t y = toFun-eval-inj (f ⁻¹) (Pt eq)

sort-id : ∀ {n} (t : Tree (Bits n) n) → InjT t → toFun (sort t) ≗ id
sort-id t t-inj rewrite ≡.sym (sortBij-sort t)
  = sort-id′′ (evalTree f t) (λ {x} {y} eq → toFun-evalTree-inj f t t-inj eq) (sort-spec′ t)
  where f = sortBijT t

sort-id-fun : ∀ {n} (f : Endo (Bits n)) → IsInj f → sortFun f ≗ id
sort-id-fun f f-inj x = sort-id (fromFun f) (IsInj-toFunFromFun f f-inj) x

thm : ∀ {n} (f : Endo (Bits n)) (f-inj : IsInj f) →
        eval (sortBij f) ≗ f
thm f f-inj x = eval (sortBij f) x
              ≡⟨ ≡.sym (sort-id-fun f f-inj (eval (sortBij f) x)) ⟩
                sortFun f (eval (sortBij f) x)
              ≡⟨ ≡.cong (λ t → toFun t (eval (sortBij f) x)) (≡.sym (sortBij-sort (fromFun f))) ⟩
                toFun (evalTree (sortBij f) (fromFun f)) (eval (sortBij f) x)
              ≡⟨ evalTree-eval′ (sortBij f) (fromFun f) (eval (sortBij f) x) ⟩
                toFun (fromFun f) (eval (sortBij f ⁻¹) (eval (sortBij f) x))
              ≡⟨ toFun∘fromFun f _ ⟩
                f (eval (sortBij f ⁻¹) (eval (sortBij f) x))
              ≡⟨ ≡.cong f ((sortBij f ⁻¹-inverse) x) ⟩
                f x
              ∎ where open ≡-Reasoning

thm# : ∀ {n} (f : Endo (Bits n)) (f-inj : IsInj f) (g : Bits n → Bit) →
       #⟨ g ∘ f ⟩ ≡ #⟨ g ⟩
thm# f f-inj g = #⟨ g ∘ f ⟩
               ≡⟨ #-≗ (g ∘ f) (g ∘ eval (sortBij f)) (λ x → ≡.cong g (≡.sym (thm f f-inj x))) ⟩
                 #⟨ g ∘ eval (sortBij f) ⟩
               ≡⟨ #-bij (sortBij f) g ⟩
                 #⟨ g ⟩
               ∎ where open ≡-Reasoning

-- -}
-- -}
-- -}
-- -}
