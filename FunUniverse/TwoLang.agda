open import Type
open import Function
open import Data.Two
open import Data.Nat.NP using (_+_)
open import Data.Fin.NP using (Fin; inject+; raise)
open import Data.Vec.NP using (Vec; []; _∷_; lookup)
open import Data.Bits   using (Bits)

module FunUniverse.TwoLang where

data E (I : ★) : ★ where
  input : I → E I
  fork  : (c e₀ e₁ : E I) → E I
  0₂ 1₂ : E I

infixr 4 _>>=_
_>>=_ : ∀ {I J} → E I → (I → E J) → E J
input x      >>= f = f x
fork c e₀ e₁ >>= f = fork (c >>= f) (e₀ >>= f) (e₁ >>= f)
0₂           >>= f = 0₂
1₂           >>= f = 1₂

returnE : ∀ {I} → I → E I
returnE = input

mapE : ∀ {I J} (f : I → J) → E I → E J
mapE f e = e >>= input ∘ f

evalE : ∀ {I} → (I → 𝟚) → E I → 𝟚
evalE f (input x)      = f x
evalE f (fork c e₀ e₁) = cond (evalE f e₀) (evalE f e₁) (evalE f c) -- TODO test!
evalE f 0₂             = 0₂
evalE f 1₂             = 1₂

𝟚▹E : ∀ {I} → 𝟚 → E I
𝟚▹E 0₂ = 0₂
𝟚▹E 1₂ = 1₂

Eᶠ = E ∘ Fin

evalEᶠ : ∀ {i} → Eᶠ i → Bits i → 𝟚
evalEᶠ = flip (evalE ∘ flip lookup)

raiseEᶠ : ∀ i {j} → Eᶠ j → Eᶠ (i + j)
raiseEᶠ i = mapE (raise i)

injectEᶠ+ : ∀ {i} j → Eᶠ i → Eᶠ (i + j)
injectEᶠ+ j = mapE (inject+ j)

open import Relation.Binary.PropositionalEquality

input->>= : ∀ {I J} (f : I → E J) x → input x >>= f ≡ f x
input->>= _ _ = refl

>>=-input : ∀ {i} (e : E i) → e >>= input ≡ e
>>=-input (input x) = refl
>>=-input (fork e₀ e₁ e₂) rewrite >>=-input e₀ | >>=-input e₁ | >>=-input e₂ = refl
>>=-input 0₂ = refl
>>=-input 1₂ = refl

>>=-assoc : ∀ {A B C} (mx : E A) (my : A → E B) (k : B → E C)
      → (mx >>= λ x → my x >>= k) ≡ (mx >>= my) >>= k
>>=-assoc (input x) my k = refl
>>=-assoc (fork mx₀ mx₁ mx₂) my k rewrite >>=-assoc mx₀ my k
                                        | >>=-assoc mx₁ my k
                                        | >>=-assoc mx₂ my k
                                        = refl
>>=-assoc 0₂ my k = refl
>>=-assoc 1₂ my k = refl
