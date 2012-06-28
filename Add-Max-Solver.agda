module Add-Max-Solver where

import Algebra

open import Data.Bool using (Bool ; true ; false)
open import Data.Nat.NP
import Data.Nat.Properties as Props
open import Data.Fin using (Fin ; Ordering ; less ; equal ; greater)
import Data.Fin.Props as FP
open import Data.List 
open import Data.Vec hiding ([_] ; _++_)

open import Data.Maybe using (Maybe ; just ; nothing)


open import Relation.Binary.PropositionalEquality hiding ([_])

open import Relation.Nullary using (Dec ; yes ; no)

module ℕP = Algebra.CommutativeSemiring Props.commutativeSemiring 
module ℕ⊔ = Algebra.CommutativeSemiringWithoutOne Props.⊔-⊓-0-commutativeSemiringWithoutOne



+-distr-⊔ : ∀ a m n → a + (m ⊔ n) ≡ (a + m) ⊔ (a + n)
+-distr-⊔ zero m n = refl
+-distr-⊔ (suc a) m n = cong suc (+-distr-⊔ a m n)

+-distr-⊔' : ∀ m n a → (m ⊔ n) + a ≡ (m + a) ⊔ (n + a)
+-distr-⊔' m n a = trans (ℕP.+-comm (m ⊔ n) a) (trans (+-distr-⊔ a m n) 
               (cong₂ _⊔_ (ℕP.+-comm a m) (ℕP.+-comm a n)))

⊔-idem : ∀ m → m ⊔ m ≡ m
⊔-idem zero = refl
⊔-idem (suc m) = cong suc (⊔-idem m)

congL : ∀ {A B C : Set} {x x' y} → (f : A → B → C) → x ≡ x' → f x y ≡ f x' y 
congL f refl = refl

congR : ∀ {A B C : Set} {x : A}{y y' : B} → (f : A → B → C) → y ≡ y' → f x y ≡ f x y' 
congR f refl = refl

module NatSyntax (nrVars : ℕ)(G : Vec ℕ nrVars) where

  Env = Vec ℕ nrVars
  Var = Fin nrVars

  data Syn : Set where
    con : ℕ → Syn 
    var : Var → Syn
    _:+_ : Syn → Syn → Syn 
    _:u_ : Syn → Syn → Syn

  infixl 4 _:+_

  eval : Syn → ℕ
  eval (con x) = x
  eval (var x) = lookup x G
  eval (syn :+ syn₁) = eval syn + eval syn₁
  eval (syn :u syn₁) = eval syn ⊔ eval syn₁


  data N1 : Syn → Set where 
    con_::[] : ∀ x → N1 (con x)
    var_::_ : ∀ {S} (i : Var) → N1 S → N1 (var i :+ S) 

  data N2 : Syn → Set where
    lift : ∀ {S} → N1 S → N2 S
    max  : ∀ {S S'} → N1 S → N2 S' → N2 (S :u S')

  record N1Proof S : Set where
    constructor _⊢_
    field
      {S'} : Syn
      term : N1 S'
      proof : eval S ≡ eval S' 

  record N2Proof S : Set where
    constructor _⊢_
    field
      {S'} : Syn
      term : N2 S'
      proof : eval S ≡ eval S'

  liftP : ∀ {S} → N1Proof S → N2Proof S
  liftP (term ⊢ proof) = (lift term) ⊢ proof

  incr : ∀ {S'} S → N1 S' → N1Proof (S :+ S')
  incr S con x ::[] = con eval S + x ::[] ⊢ refl
  incr {var .i :+ S'} S (var i :: s1) with incr S s1
  ... | s1' ⊢ p = (var i :: s1') ⊢ trans (sym (ℕP.+-assoc (eval S) (lookup i G) (eval S'))) 
                                   (trans(congL _+_ (ℕP.+-comm (eval S) (lookup i G)))
                                   (trans (ℕP.+-assoc (lookup i G) (eval S) (eval S')) 
                                   (cong (_+_ (lookup i G)) p)))

  append : ∀ {S S'} → N1 S → N1 S' → N1Proof (S :+ S')
  append con x ::[] s2 = incr _ s2
  append (var i :: s1) s2 with append s1 s2
  ... |  s3 ⊢ proof = var i :: s3 ⊢ trans (ℕP.+-assoc (lookup i G) _ _) (cong (_+_ (lookup i G)) proof)

  insert : ∀ {S} i → N1 S → N1Proof (var i :+ S)
  insert i con x ::[] = (var i :: con x ::[]) ⊢ refl
  insert {var .j :+ S} i (var j :: s1) with Data.Fin.toℕ i ≤? Data.Fin.toℕ j
  ... | yes _ = var i :: var j :: s1 ⊢ refl
  ... | no  _ with insert i s1
  ... | t ⊢ proof = var j :: t ⊢ trans (sym (ℕP.+-assoc (lookup i G) (lookup j G) (eval S))) 
                                       (trans
                                          (congL _+_ (ℕP.+-comm (lookup i G) (lookup j G))
                                           )
                                       (trans (ℕP.+-assoc (lookup j G) _ _) (cong (_+_ (lookup j G)) proof)))

  merge : ∀ {S S'} → N1 S → N1 S' → N1Proof (S :+ S')
  merge con x ::[] s2 = incr _ s2
  merge (var i :: s1) s2 with merge s1 s2
  ... | t1 ⊢ p1 with insert i t1
  ... | t2 ⊢ p2 = t2 ⊢ trans (trans (ℕP.+-assoc (lookup i G) _ _) (cong (_+_ (lookup i G)) p1)) p2

  mapN1-N2 : ∀ {S S'} → N1 S → N2 S' → N2Proof (S :+ S')
  mapN1-N2 s1 (lift x) = liftP (merge s1 x)
  mapN1-N2 {S} s1 (max x s2) with merge s1 x | mapN1-N2 s1 s2
  ... | t1 ⊢ p1 | t2 ⊢ p2 = (max t1 t2) ⊢ trans (+-distr-⊔ (eval S) _ _) (cong₂ _⊔_ p1 p2)

  u-merge : ∀ {S S'} → N2 S → N2 S' → N2Proof (S :u S')
  u-merge (lift x)   s2 = max x s2 ⊢ refl
  u-merge {S :u S'} (max x s1) s2 with u-merge s1 s2
  ... | t ⊢ p = (max x t) ⊢ trans (ℕ⊔.+-assoc (eval S) _ _) (cong (_⊔_ (eval S)) p)

  +-merge : ∀ {S S'} → N2 S → N2 S' → N2Proof (S :+ S')
  +-merge (lift x)   s2 = mapN1-N2 x s2
  +-merge {S :u S'} (max x s1) s2 with mapN1-N2 x s2 |  +-merge s1 s2
  ... | tx ⊢ px | ts ⊢ ps with u-merge tx ts
  ... | t ⊢ p = t ⊢ trans (trans (+-distr-⊔' (eval S) _ _) (cong₂ _⊔_ px ps)) p

  _≤ℕ_ : ℕ → ℕ → Bool
  m ≤ℕ n with m ≤? n
  ... | yes _ = true
  ... | no  _ = false

  _≤1_ : ∀ {S S'} → N1 S → N1 S' → Bool
  con x ::[] ≤1 con x₁ ::[] = x ≤ℕ x₁
  con x ::[] ≤1 (var i :: ys) = true
  (var i :: xs) ≤1 con x ::[] = false
  (var i :: xs) ≤1 (var j :: ys) with Data.Fin.compare i j
  (var .(Data.Fin.inject least) :: xs) ≤1 (var j :: ys) | less .j least = true
  (var .j :: xs) ≤1 (var j :: ys) | equal .j = xs ≤1 ys
  (var i :: xs) ≤1 (var .(Data.Fin.inject least) :: ys) | greater .i least = false

  _≡1_ : ∀ {S S'} → N1 S → N1 S' → Maybe (eval S ≡ eval S')
  con x ::[] ≡1 con x₁ ::[] with x ≟ x₁
  ... | yes p = just p
  ... | no _  = nothing
  con x ::[] ≡1 (var i :: s2) = nothing
  (var i :: s1) ≡1 con x ::[] = nothing
  (var i :: s1) ≡1 (var i₁ :: s2) with i FP.≟ i₁ | s1 ≡1 s2
  ... | yes p | just p2 = just (cong₂ _+_ (cong₂ lookup p (refl {x = G})) p2)
  ... | yes p | nothing = nothing
  ... | no  _ | m = nothing
    where open import Data.Fin.Props

  N2-insert : ∀ {S S'} → N1 S → N2 S' → N2Proof (S :u S')
  N2-insert {S} x (lift x₁) with x ≤1 x₁
  ... | true = max x (lift x₁) ⊢ refl
  ... | false = max x₁ (lift x) ⊢ ℕ⊔.+-comm (eval S) _
  N2-insert {S} {S' :u S''} x (max x₁ s) with x ≤1 x₁
  ... | true  = (max x (max x₁ s)) ⊢ refl
  ... | false with N2-insert x s
  ... | t ⊢ p = (max x₁ t) ⊢ trans (trans (sym (ℕ⊔.+-assoc (eval S) (eval S') (eval S'')))
                                      (trans (congL _⊔_ (ℕ⊔.+-comm (eval S) _))
                                       (ℕ⊔.+-assoc (eval S') _ _))) (cong (_⊔_ (eval S')) p) 
  Tran = ∀ {S} → N2 S → N2Proof S

  sort : Tran
  sort (lift x) = lift x ⊢ refl
  sort {S :u S'} (max x s1) with sort s1
  ... | s2 ⊢ p2 with N2-insert x s2
  ... | s3 ⊢ p3 = s3 ⊢ (trans (cong (_⊔_ (eval S)) p2) p3)  

  nub : Tran
  nub (lift x) = lift x ⊢ refl
  nub {S :u S'} (max x (lift x₁)) with x ≡1 x₁
  ... | just p  = (lift x) ⊢ trans (cong (_⊔_ (eval S)) (sym p)) (⊔-idem (eval S))
  ... | nothing = max x (lift x₁) ⊢ refl
  nub {S :u (S' :u S'')} (max x (max x₁ x₂)) with nub (max x₁ x₂) | x ≡1 x₁
  ... | t2 ⊢ p2 | just p  = t2 ⊢ trans (trans (sym (ℕ⊔.+-assoc (eval S) (eval S') (eval S''))) 
                                   (congL _⊔_ (trans (congL _⊔_ p) (⊔-idem (eval S'))))) p2
  ... | t2 ⊢ p2 | nothing = max x t2 ⊢ cong (_⊔_ (eval S)) p2

  norm2 : (x : Syn) → N2Proof x
  norm2 (con x) = (lift con x ::[]) ⊢ refl
  norm2 (var x) = lift (var x :: con 0 ::[]) ⊢ ℕP.+-comm 0 (lookup x G)
  norm2 (x :+ x₁) with norm2 x | norm2 x₁
  ... | s1 ⊢ p1 | s2 ⊢ p2 with +-merge s1 s2
  ... | s3 ⊢ p3 = s3 ⊢ (trans (cong₂ _+_ p1 p2) p3)
  norm2 (x :u x₁) with norm2 x | norm2 x₁
  ... | s1 ⊢ p1 | s2 ⊢ p2 with u-merge s1 s2
  ... | s3 ⊢ p3 = s3 ⊢ trans (cong₂ _⊔_ p1 p2) p3


  _∘S_ : Tran → Tran → Tran
  (f ∘S g) x =  (N2Proof.term (f (N2Proof.term (g x)))) ⊢ trans (N2Proof.proof (g x)) (N2Proof.proof (f (N2Proof.term (g x))))

  norm : (x : Syn) → N2Proof x
  norm x with norm2 x
  ... | t1 ⊢ p1 with (nub ∘S sort) t1
  ... | t2 ⊢ p2 = t2 ⊢ trans p1 p2

  proof : (x y : Syn) → eval (N2Proof.S' (norm x)) ≡ eval (N2Proof.S' (norm y))
            → eval x ≡ eval y
  proof x y eq = trans (N2Proof.proof (norm x)) (trans eq (sym (N2Proof.proof (norm y))))

test : ∀ (x y : ℕ) → 5 + x + (9 + y + 10) ≡ 12 + y + x + 12
test x y = proof (con 5 :+ x' :+ (con 9 :+ y' :+ con 10)) (con 12 :+ y' :+ x' :+ con 12) refl where
  open NatSyntax 2 (x ∷ y ∷ [])
  x' = var Data.Fin.zero
  y' = var (Data.Fin.suc Data.Fin.zero)

test' : ∀ (x y : ℕ) → ((x + 3) ⊔ (2 + y)) + 7 ≡ (2 + y + 7) ⊔ (5 + x + 5)
test' x y = proof LHS RHS refl where
  open NatSyntax 2 (x ∷ y ∷ [])
  #_ = con
  x' = var Data.Fin.zero
  y' = var (Data.Fin.suc Data.Fin.zero)
  LHS = ((x' :+ # 3) :u (# 2 :+ y')) :+ # 7 
  RHS = (# 2 :+ y' :+ # 7) :u (# 5 :+ x' :+ # 5) 

test3 : ∀ x → 1 + (x ⊔ x + 0) ≡ 1 + x
test3 x = proof LHS RHS refl where
  open NatSyntax 1 (x ∷ [])
  #_ = con
  x' = var Data.Fin.zero
  LHS = # 1 :+ (x' :u x' :+ # 0)
  RHS = # 1 :+ x'