{-# OPTIONS --copatterns #-}

open import Type
open import Function
open import Data.Product hiding (map)

module cont (T : ★) where 

ContA : ★ → ★
ContA A = (A → T) → T 

record Cont (A : ★) : ★ where
  field
    runCont : (A → T) → T 

open Cont

return : ∀ {A} → A → Cont A
runCont (return x) k = k x

map : ∀ {A B} → (A → B) → (Cont A → Cont B)
runCont (map f mx) k = runCont mx λ x → k (f x)

_>>=_ : ∀ {A B} → Cont A → (A → Cont B) → Cont B
runCont (mx >>= f) k = runCont mx λ x → runCont (f x) k

join : ∀ {A} → Cont (Cont A) → Cont A
join mmx = mmx >>= id

_⊛_ : ∀ {A B} → Cont (A → B) → Cont A → Cont B
mf ⊛ mx = mf >>= λ f → map f mx

⟪_·_·_⟫ : ∀ {A B C} → (A → B → C) → Cont A → Cont B → Cont C
⟪ f · mx · my ⟫ = map f mx ⊛ my

_⟨,⟩_ : ∀ {A B} → Cont A → Cont B → Cont (A × B)
mx ⟨,⟩ my = ⟪ _,_ · mx · my ⟫
