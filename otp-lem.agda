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
  
  -- this proof isn't actually any hard..
  thm : ∀ {X}(op : X → X → X)(O : B → X) m₀ m₁ → searchA op (λ x → O (f x * m₀)) ≡ searchA op (λ x → O (f x * m₁))
  thm op O m₀ m₁ = searchA op (λ x → O (f x * m₀))
                 ≡⟨ sui (- [f] m₀) op (λ x → O (f x * m₀)) ⟩
                   searchA op (λ x → O (f (x + - [f] m₀)  * m₀))
                 ≡⟨ search-ext op (λ x → cong (λ p → O (p * m₀)) (f-homo x (- [f] m₀))) ⟩
                   searchA op (λ x → O ((f x * f(- [f] m₀))  * m₀))
                 ≡⟨ cong (λ p → searchA op (λ x → O ((f x * p) * m₀))) (f-pres-inv ([f] m₀)) ⟩
                   searchA op (λ x → O ((f x * 1/ f([f] m₀))  * m₀))
                 ≡⟨ search-ext op (λ x → cong O (Group.assoc GB (f x) (1/ f ([f] m₀)) m₀)) ⟩
                   searchA op (λ x → O (f x * (1/ f([f] m₀)  * m₀)))
                 ≡⟨ cong (λ p → searchA op (λ x → O (f x * (1/ p * m₀)))) (f-sur m₀) ⟩
                   searchA op (λ x → O (f x * (1/ m₀ * m₀)))
                 ≡⟨ cong (λ p → searchA op (λ x → O (f x * p))) (proj₁ (Group.inverse GB) m₀) ⟩
                   searchA op (λ x → O (f x * 1g))
                 ≡⟨ search-ext op (λ x → cong O (proj₂ (Group.identity GB) (f x))) ⟩
                   searchA op (λ x → O (f x ))
                 ≡⟨ sui ([f] m₁) op (λ x → O (f x)) ⟩
                   searchA op (λ x → O (f (x + [f] m₁)))
                 ≡⟨ search-ext op (λ x → cong O (f-homo x ([f] m₁))) ⟩
                   searchA op (λ x → O (f x * f ([f] m₁)))
                 ≡⟨ cong (λ p → searchA op (λ x → O (f x * p))) (f-sur m₁) ⟩
                   searchA op (λ x → O (f x * m₁))
                 ∎
    where
      open ≡-Reasoning
      
