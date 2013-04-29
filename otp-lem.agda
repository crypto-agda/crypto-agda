module otp-lem where

open import Level
open import Algebra.FunctionProperties
open import Data.Product

open import Function using (_∘_ ; flip)
open import Function.Inverse as Inv using (_↔_; module Inverse)
open import Relation.Binary.PropositionalEquality.NP
open import Search.Type
open import Search.Sum

record Group (G : Set) : Set where
  field
    _∙_ : G → G → G
    ε   : G
    -_  : G → G

  -- laws
  field
    assoc : Associative _≡_ _∙_
    identity : Identity _≡_ ε _∙_
    inverse  : Inverse _≡_ ε -_ _∙_


GroupHomomorphism : ∀ {A B : Set} → Group A → Group B →(A → B) → Set
GroupHomomorphism GA GB f = ∀ x y → f (x + y) ≡ f x * f y
  where
    open Group GA renaming (_∙_ to _+_)
    open Group GB renaming (_∙_ to _*_)

module _ {A B}(GA : Group A)(GB : Group B)(f : A → B)(searchA : Search zero A)(f-homo : GroupHomomorphism GA GB f)([f] : B → A)(f-sur : ∀ b → f ([f] b) ≡ b)
              (sui : ∀ k → StableUnder searchA (flip (Group._∙_ GA) k))(search-ext : SearchExt searchA) where
  open Group GA using (-_) renaming (_∙_ to _+_ ; ε to 0g)
  open Group GB using ()   renaming (_∙_ to _*_ ; ε to 1g ; -_ to 1/_)

  {- How all this is related to elgamal

  the Group GA is ℤq with modular addition as operation
  the Group GB is the cyclic group with order q

  f is g^, the proof only need that it is a group homomorphism
  and that it has a right inverse

  we require that the search (for type A) function (should work with only summation)
  is Stable under addition of GA (notice that we have flip in there that is so that
  we don't need commutativity

  finally we require that the search function respects extensionality
  -}
  
  {-
   I had some problems with using the standard library definiton of Groups
   so I rolled my own, therefor I need some boring proofs first

  -}
  
  help : ∀ x y → x ≡ (x * y) * 1/ y
  help x y = x
           ≡⟨ sym (proj₂ identity x) ⟩
             x * 1g
           ≡⟨ cong (_*_ x) (sym (proj₂ inverse y)) ⟩
             x * (y * 1/ y)
           ≡⟨ sym (assoc x y (1/ y)) ⟩
             (x * y) * (1/ y)
           ∎
    where open ≡-Reasoning
          open Group GB
    
  unique-1g : ∀ x y → x * y ≡ y → x ≡ 1g
  unique-1g x y eq = x
                   ≡⟨ help x y ⟩
                     (x * y) * 1/ y
                   ≡⟨ cong (flip _*_ (1/ y)) eq ⟩
                     y * 1/ y
                   ≡⟨ proj₂ inverse y ⟩
                     1g
                   ∎
    where open ≡-Reasoning
          open Group GB

  unique-/ : ∀ x y → x * y ≡ 1g → x ≡ 1/ y
  unique-/ x y eq = x
                  ≡⟨ help x y ⟩
                    (x * y) * 1/ y
                  ≡⟨ cong (flip _*_ (1/ y)) eq ⟩
                    1g * 1/ y
                  ≡⟨ proj₁ identity (1/ y) ⟩
                    1/ y
                  ∎
    where open ≡-Reasoning
          open Group GB
    
  f-pres-ε : f 0g ≡ 1g
  f-pres-ε = unique-1g (f 0g) (f 0g) part
    where open ≡-Reasoning
          open Group GA
          part = f 0g * f 0g
               ≡⟨ sym (f-homo 0g 0g) ⟩
                 f (0g + 0g)
               ≡⟨ cong f (proj₁ identity 0g) ⟩
                 f 0g
               ∎

  f-pres-inv : ∀ x → f (- x) ≡ 1/ f x
  f-pres-inv x = unique-/ (f (- x)) (f x) part
    where open ≡-Reasoning
          open Group GA hiding (-_)
          part = f (- x) * f x
               ≡⟨ sym (f-homo (- x) x) ⟩
                 f (- x + x)
               ≡⟨ cong f (proj₁ inverse x) ⟩
                 f 0g
               ≡⟨ f-pres-ε ⟩
                 1g
               ∎
  {-
    While this proof looks complicated it basically just adds inverse of m₀ and then adds m₁ (from image of f)
    we need the homomorphic property to pull out the values.

  -}

               
  -- this proof isn't actually any hard..
  thm : ∀ {X}(op : X → X → X)(O : B → X) m₀ m₁ → searchA op (λ x → O (f x * m₀)) ≡ searchA op (λ x → O (f x * m₁))
  thm op O m₀ m₁ = searchA op (λ x → O (f x * m₀))
                 ≡⟨ sui (- [f] m₀) op (λ x → O (f x * m₀)) ⟩
                   searchA op (λ x → O (f (x + - [f] m₀)  * m₀))
                 ≡⟨ search-ext op (λ x → cong O (lemma1 x)) ⟩
                   searchA op (λ x → O (f x ))
                 ≡⟨ sui ([f] m₁) op (λ x → O (f x)) ⟩
                   searchA op (λ x → O (f (x + [f] m₁)))
                 ≡⟨ search-ext op (λ x → cong O (lemma2 x)) ⟩
                   searchA op (λ x → O (f x * m₁))
                 ∎
    where
      open ≡-Reasoning

      lemma1 : ∀ x → f (x + - [f] m₀) * m₀ ≡ f x
      lemma1 x rewrite f-homo x (- [f] m₀)
                     | f-pres-inv ([f] m₀)
                     | f-sur m₀
                     | Group.assoc GB (f x) (1/ m₀) m₀
                     | proj₁ (Group.inverse GB) m₀
                     | proj₂ (Group.identity GB) (f x) = refl

      lemma2 : ∀ x → f (x + [f] m₁) ≡ f x * m₁
      lemma2 x rewrite f-homo x ([f] m₁)
                     | f-sur m₁ = refl
