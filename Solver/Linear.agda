module Solver.Linear where

open import Data.Nat as ℕ using (ℕ)
open import Data.Fin as F using (Fin)
import Data.Fin.Props as FP

module Syntax {a} (A : Set a)(_x_ : A → A → A)(T : A)
  (R' : A → A → Set)
  (id' : ∀ {A} → R' A A)
  (_∻'_ : ∀ {A B C} → R' A B → R' B C → R' A C)
  (<id,tt>' : ∀ {A} → R' (A x T) A)
  (<id,tt>⁻¹' : ∀ {A} → R' A (A x T))
  (<tt,id>' : ∀ {A} → R' (T x A) A)
  (<tt,id>⁻¹' : ∀ {A} → R' A (T x A))
  (⟨_×'_⟩   : ∀ {A B C D} → R' A C → R' B D → R' (A x B) (C x D))
  (first'   : ∀ {A B C} → R' A B → R' (A x C) (B x C))
  (second'  : ∀ {A B C} → R' B C → R' (A x B) (A x C))
  (assoc'   : ∀ {A B C} → R' (A x (B x C)) ((A x B) x C))
  (assoc⁻¹' : ∀ {A B C} → R' ((A x B) x C) (A x (B x C)))
  (swap'    : ∀ {A B}   → R' (A x B) (B x A))
  nrVars (!_ : Fin nrVars → A) where

  Var = Fin nrVars

  open import Relation.Nullary using (yes ; no)
  open import Relation.Nullary.Decidable

  infixr 5 _,_
  data Syn : Set where
   var : Var → Syn
   tt  : Syn
   _,_ : Syn → Syn → Syn

  #_ : ∀ m {m<n : True (ℕ.suc m ℕ.≤? nrVars)} → Syn
  #_ m {p} = var (F.#_ m {nrVars} {p})

  eval : Syn → A
  eval (var x) = ! x
  eval tt = T
  eval (s , s₁) = eval s x eval s₁

  data R : Syn → Syn → Set where
    _∻''_ : ∀ {A B C} → R A B → R B C → R A C
    <id,tt> : ∀ {A} → R (A , tt) A
    <tt,id> : ∀ {A} → R (tt , A) A
    <tt,id>⁻¹ : ∀ {A} → R A (tt , A)
    <id,tt>⁻¹ : ∀ {A} → R A (A , tt)
    ⟨_×''_⟩ : ∀ {A B C D} → R A C → R B D → R (A , B) (C , D)
    assoc : ∀ {A B C} → R (A , (B , C)) ((A , B) , C)
    assoc⁻¹ : ∀ {A B C} → R ((A , B) , C) (A , (B , C))
    id : ∀ {A} → R A A
    swap : ∀ {A B} → R (A , B) (B , A)

  ⟨_×_⟩ : ∀ {A B C D} → R A C → R B D → R (A , B) (C , D)
  ⟨ id × id ⟩ = id
  ⟨ r₁ × r₂ ⟩ = ⟨ r₁ ×'' r₂ ⟩

  _∻_ : ∀ {A B C} → R A B → R B C → R A C
  id ∻ r₂ = r₂
  r₁ ∻ id = r₁
  <tt,id>⁻¹ ∻ <tt,id> = id
  <id,tt>⁻¹ ∻ <id,tt> = id
  <tt,id> ∻ <tt,id>⁻¹ = id
  <id,tt> ∻ <id,tt>⁻¹ = id
  swap ∻ <id,tt> = <tt,id>
  swap ∻ <tt,id> = <id,tt>
  <id,tt>⁻¹ ∻ swap = <tt,id>⁻¹
  <tt,id>⁻¹ ∻ swap = <id,tt>⁻¹
  assoc ∻ assoc⁻¹ = id
  assoc ∻ (assoc⁻¹ ∻'' r) = r
  assoc⁻¹ ∻ assoc = id
  assoc⁻¹ ∻ (assoc ∻'' r) = r
  swap ∻ swap = id
  swap ∻ (swap ∻'' r) = r
  (r₁ ∻'' r₂) ∻ r₃ = r₁ ∻ (r₂ ∻ r₃)
  ⟨ r₁ ×'' r₂ ⟩ ∻ ⟨ r₃ ×'' r₄ ⟩ = ⟨ r₁ ∻ r₃ × r₂ ∻ r₄ ⟩
  ⟨ r₁ ×'' r₂ ⟩ ∻ (⟨ r₃ ×'' r₄ ⟩ ∻'' r₅) with ⟨ r₁ ∻ r₃ × r₂ ∻ r₄ ⟩
  ... | id = r₅
  ... | r₆ = r₆ ∻'' r₅
  r₁ ∻ r₂ = r₁ ∻'' r₂ 

  sym : ∀ {S S'} → R S S' → R S' S
  sym (r ∻'' r₁) = sym r₁ ∻ sym r
  sym <id,tt> = <id,tt>⁻¹
  sym <tt,id> = <tt,id>⁻¹
  sym <id,tt>⁻¹ = <id,tt>
  sym <tt,id>⁻¹ = <tt,id>
  sym ⟨ r ×'' r₁ ⟩ = ⟨ sym r × sym r₁ ⟩
  sym assoc = assoc⁻¹
  sym assoc⁻¹ = assoc
  sym id = id
  sym swap = swap

  proof₁ : ∀ {S S'} → R S S' → R' (eval S) (eval S')
  proof₁ (r ∻'' r₁) = proof₁ r ∻' proof₁ r₁
  proof₁ <id,tt> = <id,tt>'
  proof₁ <tt,id> = <tt,id>'
  proof₁ <id,tt>⁻¹ = <id,tt>⁻¹'
  proof₁ <tt,id>⁻¹ = <tt,id>⁻¹'
  proof₁ ⟨ id ×'' r ⟩ = second' (proof₁ r)
  proof₁ ⟨ r ×'' id ⟩ = first'  (proof₁ r)
  proof₁ ⟨ r ×'' r₁ ⟩ = ⟨ proof₁ r ×' proof₁ r₁ ⟩
  proof₁ assoc = assoc'
  proof₁ assoc⁻¹ = assoc⁻¹'
  proof₁ id = id'
  proof₁ swap = swap'

  proof₂ : ∀ {S S'} → R S S' → R' (eval S') (eval S)
  proof₂ r = proof₁ (sym r)

  data NF : Syn → Set where
    tt : NF tt
    var : (x : Var) → NF (var x)
    var_::_ : ∀ {S}(i : Var) → NF S → NF (var i , S)

  record NFP S : Set where
    constructor _⊢_
    field
      {S'} : Syn
      term : NF S'
      proof : R S' S
  
 
  merge : ∀ {S S'} → NF S → NF S' → NFP (S , S')
  merge tt n2 = n2 ⊢ <tt,id>⁻¹
  merge (var i) n2 = (var i :: n2) ⊢ id
  merge (var i :: n1) n2 with merge n1 n2
  ... | t ⊢ p = (var i :: t) ⊢ (⟨ id × p ⟩ ∻ assoc)

  norm : (x : Syn) → NFP x
  norm (var x) = (var x) ⊢ id
  norm tt = tt ⊢ id
  norm (x , x₁) with norm x | norm x₁
  ... | t1 ⊢ p1 | t2 ⊢ p2 with merge t1 t2
  ... | t3 ⊢ p3 = t3 ⊢ (p3 ∻ ⟨ p1 × p2 ⟩)

  insert : ∀ {S} → (x : Var) → NF S → NFP (var x , S)
  insert y tt = (var y) ⊢ <id,tt>⁻¹
  insert y (var i) with (F.toℕ y) ℕ.≤? (F.toℕ i)
  ... | yes _ = (var y :: var i) ⊢ id
  ... | no  _ = (var i :: var y) ⊢ swap
  insert y (var i :: n1) with (F.toℕ y) ℕ.≤? (F.toℕ i)
  ... | yes _ = (var y :: (var i :: n1)) ⊢ id
  ... | no  _ with insert y n1
  ... | t ⊢ p = (var i :: t) ⊢ (⟨ id × p ⟩ ∻ (assoc ∻ (⟨ swap × id ⟩ ∻ assoc⁻¹)))

  sort : ∀ {x : Syn} → NF x → NFP x
  sort tt = tt ⊢ id
  sort (var i) = var i ⊢ id
  sort (var i :: n1) with sort n1
  ... | t1 ⊢ p1 with insert i t1
  ... | t2 ⊢ p2 = t2 ⊢ (p2 ∻ ⟨ id × p1 ⟩)

  normal : (x : Syn) → NFP x
  normal x with norm x
  ... | t1 ⊢ p1 with sort t1
  ... | t2 ⊢ p2 = t2 ⊢ (p2 ∻ p1)

  open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
  open import Relation.Nullary

  import Data.Unit
  import Data.Empty

  id≡ : ∀ {S S'} → S ≡ S' → R S S'
  id≡ refl = id

  _≢_ : ∀ {A : Set} → A → A → Set
  x ≢ y = x ≡ y → Data.Empty.⊥

  ≢-cong : ∀ {A B}{x y : A}(f : A → B) → f x ≢ f y → x ≢ y
  ≢-cong f fr refl = fr refl

  var-inj : ∀ {i j : Fin nrVars} → i ≢ j → Syn.var i ≢ var j
  var-inj p refl = p refl

  ,-inj₁ : ∀ {x y a b} → x ≢ y → (x Syn., a) ≢ (y , b)
  ,-inj₁ p refl = p refl

  ,-inj₂ : ∀ {x y a b} → a ≢ b → (x Syn., a) ≢ (y , b)
  ,-inj₂ p refl = p refl

  _≟_ : (x y : Syn) → Dec (x ≡ y)
  var x ≟ var x₁ with x FP.≟ x₁
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

  CHECK : Syn → Syn → Set
  CHECK s1 s2 with s1 ≟ s2
  ... | yes p = Data.Unit.⊤
  ... | no  p = Data.Empty.⊥

  rewire : (S₁ S₂ : Syn) → CHECK (NFP.S' (normal S₁)) (NFP.S' (normal S₂)) → R' (eval S₁) (eval S₂)
  rewire s₁ s₂ eq with NFP.S' (normal s₁) ≟ NFP.S' (normal s₂)
  ... | yes p = proof₁
                  ((sym (NFP.proof (normal s₁)) ∻ id≡ p) ∻ NFP.proof (normal s₂))
  rewire _ _ () | no _
    -- proof₂ (NFP.proof (normal s₁)) ∻' (eq ∻' proof₁ (NFP.proof (normal s₂)))

  infix 4 _⇛_

  record Eq : Set where
    constructor _⇛_
    field
      LHS RHS : Syn

  open import Data.Vec.N-ary using (N-ary ; _$ⁿ_)
  open import Data.Vec using (allFin) renaming (map to vmap)

  rewire' : (f : N-ary nrVars Syn Eq) → let (S₁ ⇛ S₂) = f $ⁿ (vmap Syn.var (allFin nrVars))
          in CHECK (NFP.S' (normal S₁)) (NFP.S' (normal S₂)) → R' (eval S₁) (eval S₂)
  rewire' f eq = let S ⇛ S' = f $ⁿ vmap Syn.var (allFin  nrVars)
         in rewire S S' eq
 
         {- move them to sub modules
module example where

  open import Data.Vec

  open import Data.Product
  open import Data.Unit

  open import Function

  -- need to etaexpand this because otherwise we get an error
  module STest n M = Syntax Set _×_ ⊤ (λ x x₁ → x → x₁) (λ x → x) 
         (λ x x₁ x₂ → x₁ (x x₂)) (λ x → proj₁ x) (λ x → x , tt) 
         (λ x → proj₂ x) (λ x → tt , x) (λ x x₁ x₂ → (x (proj₁ x₂)) , (x₁ (proj₂ x₂))) 
         (λ x x₁ → (x (proj₁ x₁)) , (proj₂ x₁)) (λ x x₁ → (proj₁ x₁) , (x (proj₂ x₁))) 
         (λ x → ((proj₁ x) , (proj₁ (proj₂ x))) , (proj₂ (proj₂ x))) 
         (λ x → (proj₁ (proj₁ x)) , ((proj₂ (proj₁ x)) , (proj₂ x))) 
         (λ x → (proj₂ x) , (proj₁ x)) n M

  test : (A B C : Set) → (A × B) × C → (B × A) × C
  test A B C = rewire LHS RHS _ where
    open STest 3 (λ i → lookup i (A ∷ B ∷ C ∷ []))

    LHS = (# 0 , # 1) , # 2
    RHS = (# 1 , # 0) , # 2

  test2 : (A B C : Set) → (A × B) × C → (B × A) × C
  test2 A B C = rewire' (λ a b c → (a , b) , c ⇛ (b , a) , c) _ where
    open STest 3 (λ i → lookup i (A ∷ B ∷ C ∷ []))


module example₂ where

  open import Data.Vec

  data Ty : Set where
    _×_ : Ty → Ty → Ty
    ⊤ : Ty

  infix 4 _⟶_ 

  data _⟶_ : Ty → Ty → Set where
    id' : ∀ {A} → A ⟶ A
    _∻'_ : ∀ {A B C} → A ⟶ B → B ⟶ C → A ⟶ C
    <id,tt>' : ∀ {A} → (A × ⊤) ⟶ A
    <id,tt>⁻¹' : ∀ {A} → A ⟶ (A × ⊤)
    <tt,id>' : ∀ {A} → (⊤ × A) ⟶ A
    <tt,id>⁻¹' : ∀ {A} → A ⟶ (⊤ × A)
    ⟨_×'_⟩   : ∀ {A B C D} → A ⟶ C → B ⟶ D → (A × B) ⟶ (C × D)
    first    : ∀ {A B C} → A ⟶ B → A × C ⟶ B × C
    second   : ∀ {A B C} → B ⟶ C → A × B ⟶ A × C 
    assoc'   : ∀ {A B C} → (A × (B × C)) ⟶ ((A × B) × C)
    assoc⁻¹' : ∀ {A B C} → ((A × B) × C) ⟶ (A × (B × C))
    swap'    : ∀ {A B}   → (A × B) ⟶ (B × A)
  

  module STest n M = Syntax Ty _×_ ⊤ _⟶_ id' _∻'_ <id,tt>' <id,tt>⁻¹' <tt,id>' <tt,id>⁻¹' ⟨_×'_⟩ first second assoc' assoc⁻¹' swap' n M

  test2 : (A B C : Ty) → (A × B) × C ⟶  (B × A) × C
  test2 A B C = rewire ((# 0 , # 1) , # 2) ((# 1 , # 0) , # 2) _ where
    open STest 3 (λ i → lookup i (A ∷ B ∷ C ∷ []))


module example₃ where

  open import Data.Unit
  open import Data.Product
  open import Data.Vec

  open import Function using (flip ; const)
  
  open import Function.Inverse
  open import Function.Related.TypeIsomorphisms.NP

  open ×-CMon using () renaming (∙-cong to ×-cong ; assoc to ×-assoc)

  module STest n M = Syntax Set _×_ ⊤ _↔_ id (flip _∘_) A×⊤↔A (sym A×⊤↔A) (A×⊤↔A ∘ swap-iso) (swap-iso ∘ sym A×⊤↔A)
                            ×-cong first-iso (λ x → second-iso (const x))
                            (sym (×-assoc _ _ _)) (×-assoc _ _ _) swap-iso n M

  test : ∀ A B C → ((A × B) × C) ↔ (C × (B × A))
  test A B C = rewire ((# 0 , # 1) , # 2) (# 2 , (# 1 , # 0)) _ where
    open STest 3 (λ i → lookup i (A ∷ B ∷ C ∷ []))

-}
