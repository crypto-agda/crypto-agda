module Solver.Linear where

open import FunUniverse.Types
open import FunUniverse.Rewiring.Linear
open import Data.Two hiding (_≟_)
open import Data.Nat as ℕ using (ℕ)
import Solver.Linear.Syntax as LinSyn
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl; _≢_)
open import Relation.Nullary
import Data.String as String
module String≤ = StrictTotalOrder String.strictTotalOrder
open import Data.Fin using (Fin)
open import Data.Fin.Props using (strictTotalOrder) renaming (_≟_ to _≟ᶠ_)
open import Data.Vec using (Vec; lookup)
open import Data.Vec.N-ary using (N-ary ; _$ⁿ_)
open import Data.Vec using (allFin) renaming (map to vmap)

module Syntax
  {Var : Set}
  (_≤V₂_ : Var → Var → 𝟚)
  (_≟V_ : Decidable (_≡_ {A = Var}))
  {a} {A : Set a}
  {funU : FunUniverse A}
  (linRewiring : LinRewiring funU)
  (Γ : Var → A)
 where

  open FunUniverse funU
  open LinRewiring linRewiring
  open LinSyn Var

  eval : Syn → A
  eval (var x) = Γ x
  eval tt = `⊤
  eval (s , s₁) = eval s `× eval s₁

  EvalEq : Eq → Set
  EvalEq e = eval (LHS e) `→ eval (RHS e)

  data R : Syn → Syn → Set a where
    _``∻_ : ∀ {A B C} → R A B → R B C → R A C
    `<id,tt>⁻¹ : ∀ {A} → R (A , tt) A
    `<tt,id>⁻¹ : ∀ {A} → R (tt , A) A
    `<tt,id> : ∀ {A} → R A (tt , A)
    `<id,tt> : ∀ {A} → R A (A , tt)
    ⟨_``×_⟩ : ∀ {A B C D} → R A C → R B D → R (A , B) (C , D)
    `assoc : ∀ {A B C} → R (A , (B , C)) ((A , B) , C)
    `assoc⁻¹ : ∀ {A B C} → R ((A , B) , C) (A , (B , C))
    `id : ∀ {A} → R A A
    `swap : ∀ {A B} → R (A , B) (B , A)

  `⟨_×_⟩ : ∀ {A B C D} → R A C → R B D → R (A , B) (C , D)
  `⟨ `id × `id ⟩ = `id
  `⟨ r₁  ×  r₂ ⟩ = ⟨ r₁ ``× r₂ ⟩

  _∻_ : ∀ {A B C} → R A B → R B C → R A C
  `id ∻ r₂ = r₂
  r₁ ∻ `id = r₁
  `<tt,id>⁻¹ ∻ `<tt,id> = `id
  `<id,tt>⁻¹ ∻ `<id,tt> = `id
  `<tt,id> ∻ `<tt,id>⁻¹ = `id
  `<id,tt> ∻ `<id,tt>⁻¹ = `id
  `swap ∻ `<id,tt>⁻¹ = `<tt,id>⁻¹
  `swap ∻ `<tt,id>⁻¹ = `<id,tt>⁻¹
  `<id,tt> ∻ `swap = `<tt,id>
  `<tt,id> ∻ `swap = `<id,tt>
  `assoc ∻ `assoc⁻¹ = `id
  `assoc ∻ (`assoc⁻¹ ``∻ r) = r
  `assoc⁻¹ ∻ `assoc = `id
  `assoc⁻¹ ∻ (`assoc ``∻ r) = r
  `swap ∻ `swap = `id
  `swap ∻ (`swap ``∻ r) = r
  (r₁ ``∻ r₂) ∻ r₃ = r₁ ``∻ (r₂ ∻ r₃)
  ⟨ r₁ ``× r₂ ⟩ ∻ ⟨ r₃ ``× r₄ ⟩ = ⟨ r₁ ∻ r₃ ``× r₂ ∻ r₄ ⟩
  ⟨ r₁ ``× r₂ ⟩ ∻ ( ⟨ r₃ ``× r₄ ⟩ ``∻ r₅) with ⟨ r₁ ∻ r₃ ``× r₂ ∻ r₄ ⟩
  ... | `id = r₅
  ... | r₆ = r₆ ``∻ r₅
  r₁ ∻ r₂ = r₁ ``∻ r₂ 

  sym : ∀ {S S'} → R S S' → R S' S
  sym (r ``∻ r₁) = sym r₁ ∻ sym r
  sym `<id,tt> = `<id,tt>⁻¹
  sym `<tt,id> = `<tt,id>⁻¹
  sym `<id,tt>⁻¹ = `<id,tt>
  sym `<tt,id>⁻¹ = `<tt,id>
  sym ⟨ r ``× r₁ ⟩ = ⟨ sym r ``× sym r₁ ⟩
  sym `assoc = `assoc⁻¹
  sym `assoc⁻¹ = `assoc
  sym `id = `id
  sym `swap = `swap

  proof₁ : ∀ {S S'} → R S S' → eval S `→ eval S'
  proof₁ (r ``∻ r₁) = proof₁ r ⁏ proof₁ r₁
  proof₁ `<id,tt> = <id,tt>
  proof₁ `<tt,id> = <tt,id>
  proof₁ `<id,tt>⁻¹ = fst<,tt>
  proof₁ `<tt,id>⁻¹ = snd<tt,>
  proof₁ ⟨ `id ``× r ⟩ = second (proof₁ r)
  proof₁ ⟨ r ``× `id ⟩ = first  (proof₁ r)
  proof₁ ⟨ r ``× r₁ ⟩  = < proof₁ r × proof₁ r₁ >
  proof₁ `assoc = assoc′
  proof₁ `assoc⁻¹ = assoc
  proof₁ `id = id
  proof₁ `swap = swap

  proof₂ : ∀ {S S'} → R S S' → eval S' `→ eval S
  proof₂ r = proof₁ (sym r)

  data NF : Syn → Set a where
    tt : NF tt
    var : ∀ x → NF (var x)
    var_::_ : ∀ {S} i → NF S → NF (var i , S)

  record NFP S : Set a where
    constructor _⊢_
    field
      {S'} : Syn
      term : NF S'
      proof : R S' S
  
 
  merge : ∀ {S S'} → NF S → NF S' → NFP (S , S')
  merge tt n2 = n2 ⊢ `<tt,id>
  merge (var i) n2 = (var i :: n2) ⊢ `id
  merge (var i :: n1) n2 with merge n1 n2
  ... | t ⊢ p = (var i :: t) ⊢ (⟨ `id ``× p ⟩ ∻ `assoc)

  norm : (x : Syn) → NFP x
  norm (var x) = (var x) ⊢ `id
  norm tt = tt ⊢ `id
  norm (x , x₁) with norm x | norm x₁
  ... | t1 ⊢ p1 | t2 ⊢ p2 with merge t1 t2
  ... | t3 ⊢ p3 = t3 ⊢ (p3 ∻ ⟨ p1 ``× p2 ⟩)

  insert : ∀ {S} x → NF S → NFP (var x , S)
  insert y tt = (var y) ⊢ `<id,tt>
  insert y (var i) with y ≤V₂ i
  ... | 1' = (var y :: var i) ⊢ `id
  ... | 0' = (var i :: var y) ⊢ `swap
  insert y (var i :: n1) with y ≤V₂ i
  ... | 1' = (var y :: (var i :: n1)) ⊢ `id
  ... | 0' with insert y n1
  ... | t ⊢ p = (var i :: t) ⊢ (⟨ `id ``× p ⟩ ∻ (`assoc ∻ (⟨ `swap ``× `id ⟩ ∻ `assoc⁻¹)))

  sort : ∀ {x : Syn} → NF x → NFP x
  sort tt = tt ⊢ `id
  sort (var i) = var i ⊢ `id
  sort (var i :: n1) with sort n1
  ... | t1 ⊢ p1 with insert i t1
  ... | t2 ⊢ p2 = t2 ⊢ (p2 ∻ ⟨ `id ``× p1 ⟩)

  normal : (x : Syn) → NFP x
  normal x with norm x
  ... | t1 ⊢ p1 with sort t1
  ... | t2 ⊢ p2 = t2 ⊢ (p2 ∻ p1)

  import Data.Unit
  import Data.Empty

  id≡ : ∀ {S S'} → S ≡ S' → R S S'
  id≡ refl = `id

  var-inj : ∀ {i j} → i ≢ j → Syn.var i ≢ var j
  var-inj p refl = p refl

  ,-inj₁ : ∀ {x y a b} → x ≢ y → (x Syn., a) ≢ (y , b)
  ,-inj₁ p refl = p refl

  ,-inj₂ : ∀ {x y a b} → a ≢ b → (x Syn., a) ≢ (y , b)
  ,-inj₂ p refl = p refl

  _≟_ : (x y : Syn) → Dec (x ≡ y)
  var x ≟ var x₁ with x ≟V x₁
  var .x₁ ≟ var x₁ | yes refl = yes refl
  ... | no  p    = no (var-inj p)
  var x ≟ tt = no (λ ())
  var x ≟ (y , y₁) = no (λ ())
  tt ≟ var x = no (λ ())
  tt ≟ tt = yes refl
  tt ≟ (y , y₁) = no (λ ())
  (x , x₁) ≟ var x₂ = no (λ ())
  (x , x₁) ≟ tt = no (λ ())
  (x , x₁) ≟ (y , y₁) with x ≟ y | x₁ ≟ y₁
  (x , x₁) ≟ (.x , .x₁) | yes refl | yes refl = yes refl
  (x , x₁) ≟ (y , y₁) | yes p | no ¬p = no (,-inj₂ ¬p)
  (x , x₁) ≟ (y , y₁) | no ¬p | q = no (,-inj₁ ¬p)

  data equation-not-ok : Set where

  CHECK : Syn → Syn → Set
  CHECK s1 s2 with s1 ≟ s2
  ... | yes p = Data.Unit.⊤
  ... | no  p = equation-not-ok

  EqOk? : Eq → Set
  EqOk? e = CHECK (NFP.S' (normal (LHS e))) (NFP.S' (normal (RHS e)))

  rewire : (e : Eq) {prf : EqOk? e} → EvalEq e
  rewire (s₁ ↦ s₂) {eq} with NFP.S' (normal s₁) ≟ NFP.S' (normal s₂)
  ... | yes p = proof₁
                  ((sym (NFP.proof (normal s₁)) ∻ id≡ p) ∻ NFP.proof (normal s₂))
  rewire (_ ↦ _) {()} | no _
    -- proof₂ (NFP.proof (normal s₁)) ∻' (eq ∻' proof₁ (NFP.proof (normal s₂)))

module Syntaxᶠ {a} {A : Set a} {funU : FunUniverse A} (linRewiring : LinRewiring funU) where
  module _ {n} where
    open LinSyn (Fin n) public

  module _ {n} (Γ : Vec A n)
           (f : N-ary n (LinSyn.Syn (Fin n)) (LinSyn.Eq (Fin n)))
           where
    open Syntax {Fin n} ((λ x y → ⌊ StrictTotalOrder._<?_ (strictTotalOrder n) x y ⌋))
                _≟ᶠ_ {a} {A} {funU} linRewiring (λ i → lookup i Γ) public

    private
      e = f $ⁿ vmap Syn.var (allFin n)

    rewireᶠ : {e-ok : EqOk? e} → EvalEq e
    rewireᶠ {e-ok} = rewire e {e-ok}

module Syntaxˢ {a} {A} {funU} linRewiring Γ where
  open Syntax (λ x y → ⌊ String≤._<?_ x y ⌋) String._≟_ {a} {A} {funU} linRewiring Γ public
  open import Solver.Linear.Parser

  rewireˢ : ∀ s {s-ok} →
            let e = parseEqˢ s {s-ok} in
            {e-ok : EqOk? e} → EvalEq e
  rewireˢ s {s-ok} {e-ok} = rewire (parseEqˢ s {s-ok}) {e-ok}
-- -}
-- -}
-- -}
