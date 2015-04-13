{-# OPTIONS --without-K --copatterns #-}
open import Level.NP
open import Function hiding (_$_)
open import Type
open import Algebra
open import Algebra.FunctionProperties
open import Algebra.Structures
open import Data.Nat using (ℕ; zero; suc; _+_; _≤?_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_; _++_)
open import Data.One
open import Data.Two
open import Data.Product.NP
open import Relation.Nullary.Decidable
open import Relation.Binary.NP
open import Relation.Binary.PropositionalEquality.NP as ≡ using (_≡_; !_; _≗_; module ≡-Reasoning)
open import Category.Monad.NP
import Language.Simple.Abstract

module Language.Simple.Free where

module _ {Op : ℕ → ★} where

  open Language.Simple.Abstract Op renaming (E to T)

  data Ctx (X : ★) : ★ where
     hole : Ctx X
     op : ∀ {a b} → Op (a + (1 + b)) → Vec (T X) a → Ctx X → Vec (T X) b → Ctx  X

  module _ {X : ★} where
     η : ∀ {X} → X → T X
     η = var

     _·_ : Ctx X → T X → T X
     hole · e = e
     op o ts E us · e = op o (ts ++ E · e ∷ us)

  open WithEvalOp
  open Monad monad public renaming (liftM to map-T)
  module Unused
                 {X R : ★}
                 (⊢_≡_ : T X → T X → ★)
                 (eval-Op  : ∀ {n} → Op n → Vec R n → R)
                 (eval-X : X → R)
                 (t u : T X)
                 (⊢t≡u : ⊢ t ≡ u)
                 where
     ev = eval eval-Op eval-X
     ≈ = ev t ≡ ev u
  module ℛ {X : ★} (⊢_≡_ : T X → T X → ★) where

     {-
     data _≋*_ : ∀ {a} (ts us : Vec (T X) a) → ★
     data _≋_ : (t u : T X) → ★

     data _≋*_ where
       []    : [] ≋* []
       _∷_ : ∀ {t u a} {ts us : Vec _ a}
               → t ≋ u → ts ≋* us → (t ∷ ts) ≋* (u ∷ us)
     data _≋_ where
       η : ∀ {t u} → ⊢ t ≡ u → t ≋ u
       !η : ∀ {t u} → ⊢ t ≡ u → u ≋ t
       var : ∀ x → var x ≋ var x
       op : ∀ {a} (o : Op a) {ts us} → ts ≋* us → op o ts ≋ op o us
     -}

     module Unused2 where

        data Succ (X : ★) : ★ where
           old : X → Succ X
           new : Succ X

        infix 9 _$_

        _$_ : T (Succ X) → T X → T X
        E $ t = E >>= (λ { new → t ; (old x) → var x })

     infix 0 _≈_
     data _≈_   : (t u : T X) → ★ where
        refl    : Reflexive _≈_
        sym     : Symmetric _≈_
        trans   : Transitive _≈_
        η≡      : ∀ {t u} → ⊢ t ≡ u → t ≈ u
        congCtx : ∀ E {t u} → t ≈ u → E · t ≈ E · u

     ≈-isEquivalence : IsEquivalence _≈_
     ≈-isEquivalence = record { refl = refl ; sym = sym ; trans = trans }

module FreeSemigroup where

    U = Semigroup.Carrier
    record _→ₛ_ (X Y : Semigroup ₀ ₀) : ★ where
      open Semigroup X renaming (_∙_ to _∙x_)
      open Semigroup Y renaming (_∙_ to _∙y_)
      field
        to : U X → U Y
        to-∙-cong : ∀ t u → to (t ∙x u) ≡ to t ∙y to u
    open _→ₛ_ public

    idₛ : ∀ {S} → S →ₛ S
    to idₛ = id
    to-∙-cong idₛ _ _ = ≡.refl

    module _ {X Y Z} where
        _∘ₛ_ : (Y →ₛ Z) → (X →ₛ Y) → X →ₛ Z
        to (f ∘ₛ g) = to f ∘ to g
        to-∙-cong (f ∘ₛ g) t u
           = to (f ∘ₛ g) (t ∙x u)
           ≡⟨ ≡.cong (to f) (to-∙-cong g _ _) ⟩
              to f (to g t ∙y to g u)
           ≡⟨ to-∙-cong f _ _ ⟩
              to (f ∘ₛ g) t ∙z to (f ∘ₛ g) u
           ∎
          where
            open ≡-Reasoning
            open Semigroup X renaming (_∙_ to _∙x_)
            open Semigroup Y renaming (_∙_ to _∙y_)
            open Semigroup Z renaming (_∙_ to _∙z_)

    data Op : ℕ → ★ where
       `μ : Op 2
    open Language.Simple.Abstract Op renaming (E to T)
    open Monad monad

    module _ {X : ★} where
        _∙_ : T X → T X → T X
        t ∙ u = op `μ (t ∷ u ∷ [])

    module _ (X : ★) where
        infix 0 ⊢_≡_
        data ⊢_≡_ : T X → T X → ★ where
           ⊢-∙-assoc : ∀ x y z → ⊢ ((x ∙ y) ∙ z) ≡ (x ∙ (y ∙ z))

        open ℛ ⊢_≡_

        ∙-assoc : Associative _≈_ _∙_
        ∙-assoc x y z = η≡ (⊢-∙-assoc x y z)

        open Equivalence-Reasoning ≈-isEquivalence

        ∙-cong : _∙_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
        ∙-cong {x} {y} {u} {v} p q =
           x ∙ u
             ≈⟨ congCtx (op `μ (x ∷ []) hole []) q ⟩
           x ∙ v
             ≈⟨ congCtx (op `μ [] hole (v ∷ [])) p ⟩
           y ∙ v ∎

        T-IsSemigroup : IsSemigroup _≈_ _∙_
        T-IsSemigroup = record { isEquivalence = ≈-isEquivalence
                                              ; assoc = ∙-assoc
                                              ; ∙-cong = ∙-cong }

        T-Semigroup : Semigroup ₀ ₀
        T-Semigroup = record { Carrier = T X
                                           ; _≈_ = _≈_
                                           ; _∙_ = _∙_
                                           ; isSemigroup = T-IsSemigroup }

    map-T-∙-hom : ∀ {X Y : ★} (f : X → Y) t u
                           → map-T f (t ∙ u) ≡ map-T f t ∙ map-T f u
    map-T-∙-hom _ _ _ = ≡.refl

    Tₛ = T-Semigroup

    Tₛ-hom : ∀ {X Y} (f : X → Y) → Tₛ X →ₛ Tₛ Y
    to (Tₛ-hom f) = map-T f
    to-∙-cong (Tₛ-hom f) = map-T-∙-hom f

    module WithSemigroup (S : Semigroup ₀ ₀) where
       module S = Semigroup S
       open S renaming (Carrier to S₀; _∙_ to _∙ₛ_)
       eval-Op : ∀ {n} → Op n → Vec S₀ n → S₀
       eval-Op `μ (x ∷ y ∷ []) = x ∙ₛ y
       eval-T : T S₀ → S₀
       eval-T = WithEvalOp.eval eval-Op id

       eval-T-var : ∀ x → eval-T (var x) ≡ x
       eval-T-var x = ≡.refl

       eval-T-∙ : ∀ t u → eval-T (t ∙ u) ≡ eval-T t ∙ₛ eval-T u
       eval-T-∙ t u = ≡.refl

       eval-Tₛ : Tₛ S₀ →ₛ S
       to eval-Tₛ = eval-T
       to-∙-cong eval-Tₛ t u = ≡.refl

    {-
    Tₛ : Sets ⟶ Semigroups
    U : Semigroups ⟶ Sets
    Tₛ ⊣ U
    Semigroups(Tₛ X, Y) ≅ Sets(X, U Y)
    -}
    module _ {X : ★} {Y : Semigroup ₀ ₀} where
        open WithSemigroup Y
        open Semigroup Y renaming (Carrier to Y₀; _∙_ to _∙Y_)

        φ : (Tₛ X →ₛ Y) → X → U Y
        φ f = to f ∘ var
        -- var is the unit (η)

        ψ : (f : X → U Y) → Tₛ X →ₛ Y
        ψ f = eval-Tₛ ∘ₛ Tₛ-hom f
        -- eval-Tₛ is the co-unit (ε)

        φ-ψ : ∀ f → φ (ψ f) ≡ f
        φ-ψ f = ≡.refl

        ψ-φ : ∀ f t → to (ψ (φ f)) t ≡ to f t
        ψ-φ f (var x) = ≡.refl
        ψ-φ f (op `μ (t ∷ u ∷ []))
           = to (ψ (φ f)) (t ∙ u)
           ≡⟨ ≡.refl ⟩
               eval-T (map-T (φ f) (t ∙ u))
           ≡⟨ ≡.refl ⟩
               eval-T (map-T (φ f) t ∙ map-T (φ f) u)
           ≡⟨ ≡.refl ⟩
               eval-T (map-T (φ f) t) ∙Y eval-T (map-T (φ f) u)
           ≡⟨ ≡.refl ⟩
               to (ψ (φ f)) t ∙Y to (ψ (φ f)) u
           ≡⟨ ≡.ap₂ _∙Y_ (ψ-φ f t) (ψ-φ f u) ⟩
               to f t ∙Y to f u
           ≡⟨ ! (to-∙-cong f t u) ⟩
               to f (t ∙ u)
           ∎
           where open ≡-Reasoning

module FreeMonoid where
    data Op : ℕ → ★ where
       `ε : Op 0
       `μ : Op 2
    open Language.Simple.Abstract Op renaming (E to T)
    ε : ∀ {X} → T X
    ε = op `ε []
    _∙_ : ∀ {X} → T X → T X → T X
    t ∙ u = op `μ (t ∷ u ∷ [])

    infix 0 _⊢_≡_
    data _⊢_≡_ (X : ★) : T X → T X → ★ where
       ⊢-ε∙x : ∀ x → X ⊢ ε ∙ x ≡ x
       ⊢-x∙ε : ∀ x → X ⊢ x ∙ ε ≡ x
       ⊢-∙-assoc : ∀ x y z → X ⊢ ((x ∙ y) ∙ z) ≡ (x ∙ (y ∙ z))
       
    module _ (X : ★) where
        open ℛ (_⊢_≡_ X)

        {- TODO, share the proofs with FreeSemigroup above -}
        ∙-assoc : Associative _≈_ _∙_
        ∙-assoc x y z = η≡ (⊢-∙-assoc x y z)

        open Equivalence-Reasoning ≈-isEquivalence

        ∙-cong : _∙_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
        ∙-cong {x} {y} {u} {v} p q =
           x ∙ u
             ≈⟨ congCtx (op `μ (x ∷ []) hole []) q ⟩
           x ∙ v
             ≈⟨ congCtx (op `μ [] hole (v ∷ [])) p ⟩
           y ∙ v ∎

        monoid : Monoid ₀ ₀
        monoid = record { Carrier = T X ; _≈_ = _≈_ ; _∙_ = _∙_ ; ε = ε
                        ; isMonoid = record { isSemigroup = record { isEquivalence = ≈-isEquivalence
                                                                   ; assoc = ∙-assoc
                                                                   ; ∙-cong = ∙-cong }
                                            ; identity = (λ x → η≡ (⊢-ε∙x x))
                                                       , (λ x → η≡ (⊢-x∙ε x)) } }


   {-

   Free monoid as a functor F : Sets → Mon

   map-[]    : map f [] ≡ []
   map-++ : map f xs ++ map f ys = map f (xs ++ ys)

   F X = (List X , [] , _++_)
   F (f : Sets(X , Y))
      : Mon(F X , F Y)
      = (map f , map-[] , map-++)

   -}

module FreeGroup where
    data Op : ℕ → ★ where
       `ε : Op 0
       `i : Op 1
       `μ : Op 2
    open Language.Simple.Abstract Op renaming (E to T)
    ε : ∀ {X} → T X
    ε = op `ε []
    infix 9 −_
    −_ : ∀ {X} → T X → T X
    − t = op `i (t ∷ [])
    infixr 6 _∙_
    _∙_ : ∀ {X} → T X → T X → T X
    t ∙ u = op `μ (t ∷ u ∷ [])

    infix 0 _⊢_≡_
    data _⊢_≡_ (X : ★) : T X → T X → ★ where
       ε∙x : ∀ x → X ⊢ ε ∙ x ≡ x
       x∙ε : ∀ x → X ⊢ x ∙ ε ≡ x
       ∙-assoc : ∀ x y z → X ⊢ (x ∙ (y ∙ z)) ≡ ((x ∙ y) ∙ z)
       −∙-inv : ∀ x → X ⊢ − x ∙ x ≡ ε
       ∙−-inv : ∀ x → X ⊢ x ∙ − x ≡ ε

-- − (− t) ≡ t
-- − t ∙ − (− t) ≡ ε ≡ − t ∙ t

-- -}
-- -}
-- -}
-- -}
