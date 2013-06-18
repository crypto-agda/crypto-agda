open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ )
open import Data.Unit
open import Data.Empty
open import Function.NP hiding (Cmp)
open import Function.Injection hiding (id ; _∘_)
open import Relation.Binary.PropositionalEquality

module bijection where

Is-Inj : ∀ {A B : Set} → (A → B) → Set
Is-Inj f = ∀ x y → f x ≡ f y → x ≡ y

data Ord : Set where lt eq gt : Ord

Cmp : Set → Set
Cmp X = X → X → Ord

l-mono : Ord → Ord → Set
l-mono lt lt = ⊤
l-mono lt eq = ⊤
l-mono lt gt = ⊥
l-mono eq lt = ⊥
l-mono eq eq = ⊤
l-mono eq gt = ⊥
l-mono gt lt = ⊥
l-mono gt eq = ⊤
l-mono gt gt = ⊤

Is-Mono : ∀ {A B} → Cmp A → Cmp B → (A → B) → Set
Is-Mono AC BC f = ∀ x y → l-mono (AC x y) (BC (f x) (f y))
{-case AC x y of λ 
  { lt → (lt ≡ BC (f x) (f y)) ⊎ (eq ≡ BC (f x) (f y))
  ; eq → eq ≡ BC (f x) (f y)
  ; gt → (gt ≡ BC (f x) (f y)) ⊎ (eq ≡ BC (f x) (f y))
  }
-}

record Interface : Set1 where
  constructor mk
  field
    Ix  : Set
    Rep : Ix → Set
    Syn : Ix → Set
    Tree : Set → Ix → Set
  field
    fromFun : ∀ {i X} → (Rep i → X) → Tree X i
    toFun   : ∀ {i X} → Tree X i → (Rep i → X)
    toFun∘fromFun : ∀ {i X}(f : Rep i → X) → f ≗ toFun (fromFun f)

  Is-InjT : ∀ {i A} → Tree A i → Set
  Is-InjT = Is-Inj ∘ toFun

  field
    evalArg  : ∀ {i} → Syn i → Endo (Rep i)
    evalTree : ∀ {i X} → Syn i → Endo (Tree X i)
    eval-proof : ∀ {i X}(S : Syn i)(T : Tree X i) → toFun T ≗ toFun (evalTree S T) ∘ evalArg S

  field
    inv : ∀ {i} → Endo (Syn i)
    inv-proof : ∀ {i} S → evalArg {i} S ∘ evalArg (inv S) ≗ id

  field
    RC : ∀ {i} → Cmp (Rep i)

  Is-MonoT : ∀ {i X} → Cmp X → Tree X i → Set
  Is-MonoT XC = Is-Mono RC XC ∘ toFun

  field
    sort : ∀ {i X} → Cmp X → Endo (Tree X i)
    sort-syn : ∀ {i X} → Cmp X → Tree X i → Syn i
    sort-proof : ∀ {i X}(X-cmp : Cmp X)(T : Tree X i) → sort X-cmp T ≡ evalTree (sort-syn X-cmp T) T
    sort-mono  : ∀ {i} T → Is-MonoT (RC {i}) (sort {i} RC T)

  field
    mono-inj→id : ∀ {i}(f : Endo (Rep i)) → Is-Inj f → Is-Mono RC RC f → f ≗ id


module abs (Inter : Interface) where
  open Interface Inter


  sort-bij : ∀ {i} → Endo (Rep i) → Syn i
  sort-bij f = sort-syn RC (fromFun f)

  sortFun : ∀ {i} → Endo (Endo (Rep i))
  sortFun = toFun ∘ sort RC ∘ fromFun

  fromFun-inj : ∀ {i} (f : Endo (Rep i)) → Is-Inj f → Is-InjT (fromFun f)
  fromFun-inj f f-inj x y rewrite 
    sym (toFun∘fromFun f x) |
    sym (toFun∘fromFun f y) = f-inj x y

  eval-proof` : ∀ {i X} S T → toFun {i}{X} (evalTree S T) ≗ toFun T ∘ evalArg (inv S)
  eval-proof` S T x = begin 
      toFun (evalTree S T) x 
    ≡⟨ cong (toFun (evalTree S T)) (sym (inv-proof S x)) ⟩
      toFun (evalTree S T) (evalArg S (evalArg (inv S) x)) 
    ≡⟨ sym (eval-proof S T (evalArg (inv S) x)) ⟩ 
      toFun T (evalArg (inv S) x) 
    ∎
    where open ≡-Reasoning


  sort-from-inj : ∀ {i} (T : Tree (Rep i) i) → Is-InjT T → Is-InjT (sort RC T)
  sort-from-inj T T-inj x y prf rewrite sort-proof RC T = begin 
      x 
    ≡⟨ sym (inv-proof (sort-syn RC T) x) ⟩ 
      evalArg (sort-syn RC T) (evalArg (inv (sort-syn RC T)) x)
    ≡⟨ cong (evalArg (sort-syn RC T)) p3 ⟩
      evalArg (sort-syn RC T) (evalArg (inv (sort-syn RC T)) y)
    ≡⟨ inv-proof (sort-syn RC T) y ⟩
      y 
    ∎
    where
      open ≡-Reasoning
      p3 : evalArg (inv (sort-syn RC T)) x ≡ evalArg (inv (sort-syn RC T)) y
      p3 = T-inj (evalArg (inv (sort-syn RC T)) x) (evalArg (inv (sort-syn RC T)) y)
             (trans (sym (eval-proof` (sort-syn RC T) T x)) (trans prf (eval-proof` (sort-syn RC T) T y)))

  sortFun-inj : ∀ {i} (f : Endo (Rep i)) → Is-Inj f → Is-Inj (sortFun f)
  sortFun-inj f f-inj = sort-from-inj (fromFun f) (fromFun-inj f f-inj)

  sortFun-mono : ∀ {i} (f : Endo (Rep i)) → Is-Mono RC RC (sortFun f)
  sortFun-mono f = sort-mono (fromFun f)

  thm : ∀ {i} (f : Endo (Rep i)) → Is-Inj f → f ≗ evalArg (sort-bij f)
  thm f f-inj x = begin 
        f x 
      ≡⟨ toFun∘fromFun f x ⟩ 
        toFun (fromFun f) x
      ≡⟨ eval-proof (sort-bij f) (fromFun f) x ⟩
        toFun (evalTree (sort-bij f) (fromFun f)) (evalArg (sort-bij f) x)
      ≡⟨ cong (λ p → toFun p (evalArg (sort-bij f) x)) (sym (sort-proof RC (fromFun f))) ⟩
        toFun (sort RC (fromFun f)) (evalArg (sort-bij f) x)
      ≡⟨ mono-inj→id (toFun (sort RC (fromFun f))) (sortFun-inj f f-inj) (sortFun-mono f) (evalArg (sort-bij f) x) ⟩
        evalArg (sort-bij f) x 
      ∎
      where open ≡-Reasoning


module Concrete-Bool where

  open import Data.Bool
  open import Data.Product
  open import Data.Unit

  open Interface

  data SBool : Set where `id `not : SBool

  `Tree : Set → Set
  `Tree X = X × X



  `fromFun : ∀ {X} → (Bool → X) → `Tree X
  `fromFun f = (f false) , (f true)

  `toFun : ∀ {X} → `Tree X → (Bool → X)
  `toFun T x = if x then proj₂ T else proj₁ T

  `toFun∘fromFun : ∀ {X} → (f : Bool → X) → f ≗ `toFun (`fromFun f)
  `toFun∘fromFun f true = refl
  `toFun∘fromFun f false = refl

  `evalArg : SBool → Endo Bool
  `evalArg `id = id
  `evalArg `not = not

  `evalTree : ∀{X} → SBool → Endo (`Tree X)
  `evalTree `id = id
  `evalTree `not = swap

  `eval-proof : ∀ {X}S (T : `Tree X) → `toFun T ≗ `toFun (`evalTree S T) ∘ `evalArg S
  `eval-proof `id T x = refl
  `eval-proof `not T true = refl
  `eval-proof `not T false = refl

  `inv : Endo SBool
  `inv x = x

  `inv-proof : ∀ S → `evalArg S ∘ `evalArg (`inv S) ≗ id
  `inv-proof `id x = refl
  `inv-proof `not true = refl
  `inv-proof `not false = refl

  `RC : Cmp Bool
  `RC true true = eq
  `RC true false = gt
  `RC false true = lt
  `RC false false = eq

  `sort : ∀ {X} → Cmp X → Endo (`Tree X)
  `sort XC (x , y) with XC x y
  `sort XC (x , y) | lt = x , y
  `sort XC (x , y) | eq = x , y
  `sort XC (x , y) | gt = y , x

  `sort-syn : ∀ {X} → Cmp X → `Tree X → SBool
  `sort-syn XC (x , y) with XC x y
  `sort-syn XC (x , y) | lt = `id
  `sort-syn XC (x , y) | eq = `id
  `sort-syn XC (x , y) | gt = `not

  `sort-proof : ∀ {X} XC (T : `Tree X) → `sort XC T ≡ `evalTree (`sort-syn XC T) T
  `sort-proof XC (x , y) with XC x y
  `sort-proof XC (x , y) | lt = refl
  `sort-proof XC (x , y) | eq = refl
  `sort-proof XC (x , y) | gt = refl

  `sort-mono : ∀ T → Is-Mono `RC `RC (`toFun (`sort `RC T))
  `sort-mono (true , true) true true = _
  `sort-mono (false , true) true true = _
  `sort-mono (true , false) true true = _
  `sort-mono (false , false) true true = _
  `sort-mono (true , true) true false = _
  `sort-mono (false , true) true false = _
  `sort-mono (true , false) true false = _
  `sort-mono (false , false) true false = _
  `sort-mono (true , true) false true = _
  `sort-mono (false , true) false true = _
  `sort-mono (true , false) false true = _
  `sort-mono (false , false) false true = _
  `sort-mono (true , true) false false = _
  `sort-mono (false , true) false false = _
  `sort-mono (true , false) false false = _
  `sort-mono (false , false) false false = _

  `mono-inj→id : (f : Endo Bool) → Is-Inj f → Is-Mono `RC `RC f 
               → f ≗ id
  `mono-inj→id f f-inj f-mono x with f-mono false true
  `mono-inj→id f f-inj f-mono true | r  with f false | f true | f-inj false true 
  `mono-inj→id f f-inj f-mono true | r | p | true | r2 = refl
  `mono-inj→id f f-inj f-mono true | () | true | false | r2
  `mono-inj→id f f-inj f-mono true | r | false | false | r2 = r2 refl
  `mono-inj→id f f-inj f-mono false | r with f false | f true | f-inj true false 
  `mono-inj→id f f-inj f-mono false | r | true | true | r2 = r2 refl
  `mono-inj→id f f-inj f-mono false | () | true | false | r2
  `mono-inj→id f f-inj f-mono false | r | false | q | r2 = refl


  interface : Interface
  interface = record 
    { Ix            = ⊤
    ; Rep           = λ _ → Bool
    ; Syn           = λ _ → SBool
    ; Tree          = λ X i → `Tree X
    ; fromFun       = `fromFun
    ; toFun         = `toFun
    ; toFun∘fromFun = `toFun∘fromFun
    ; evalArg       = `evalArg
    ; evalTree      = `evalTree
    ; eval-proof    = `eval-proof
    ; inv           = `inv
    ; inv-proof     = `inv-proof
    ; RC            = `RC
    ; sort          = `sort
    ; sort-syn      = `sort-syn
    ; sort-proof    = `sort-proof
    ; sort-mono     = `sort-mono
    ; mono-inj→id   = `mono-inj→id
    }

  open abs interface

  theorem : (f : Endo Bool) → Is-Inj f → f ≗ `evalArg (sort-bij f)
  theorem = thm

-- -}
-- -}
