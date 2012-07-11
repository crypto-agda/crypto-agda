module prg where

open import fun-universe

open import Function
open import Data.Nat.NP hiding (_==_)
open import Data.Bool.NP hiding (_==_)
open import Data.Nat.Properties
open import Data.Bool.Properties
open import Data.Bits
open import Data.Fin using (Fin; zero; suc)
open import Data.Product
open import Data.Empty
open import Data.Vec
open import Relation.Binary.PropositionalEquality.NP

PRGFun : (k n : ℕ) → Set
PRGFun k n = Bits k → Bits n

module PRG⅁₁ {k n} (PRG : PRGFun k n) where
  -- TODO: give the adv some rand
  Adv : Set
  Adv = Bits n → Bit

  chal : Bit → Bits (n + k) → Bits n
  chal b R = if b then take n R else PRG (drop n R)

  prg⅁ : Adv → Bit → Bits (n + k) → Bit
  prg⅁ adv b R = adv (chal b R)

  -- ``Looks pseudo-random if the message is the output of the PRG some key''
  brute′ : Adv
  brute′ m = search {k} _∨_ ((_==_ m) ∘ PRG)

  -- ``Looks random if the message is not a possible output of the PRG''
  brute : Adv
  brute m = search {k} _∧_ (not ∘ (_==_ m) ∘ PRG)

private
  brute-PRG-K≡0b-aux : ∀ {k n} (PRG : Bits k → Bits n) K
                           → PRG⅁₁.brute PRG (PRG K) ≡ 0b
  brute-PRG-K≡0b-aux {zero}  {n} PRG [] = cong not (==-refl (PRG []))
  brute-PRG-K≡0b-aux {suc k} {n} PRG (true ∷ K)
    rewrite brute-PRG-K≡0b-aux (PRG ∘ 1∷_) K
      = Bool°.+-comm (search _∧_ (not ∘ _==_ (PRG (1∷ K)) ∘ PRG ∘ 0∷_)) 0b
  brute-PRG-K≡0b-aux {suc k} {n} PRG (false ∷ K)
    rewrite brute-PRG-K≡0b-aux (PRG ∘ 0∷_) K = refl

  brute′-bound-aux : ∀ {k n} (PRG : Bits k → Bits n)
                       → let open PRG⅁₁ PRG in
                          #⟨ brute′ ⟩ ≤ 2^ k
  brute′-bound-aux {zero}  PRG = ℕ≤.reflexive #⟨ PRG [] ==⟩
  brute′-bound-aux {suc k} PRG = #∨ {f = λ x → search _∨_ (_==_ x ∘ PRG ∘ 0∷_)}
                                    (brute′-bound-aux (PRG ∘ 0∷_))
                                    (brute′-bound-aux (PRG ∘ 1∷_))

module PRG⅁ {k n} (PRG : PRGFun k n) where
  open PRG⅁₁ PRG public

  brute-PRG-K≡0b : ∀ K → brute (PRG K) ≡ 0b
  brute-PRG-K≡0b = brute-PRG-K≡0b-aux PRG

  prg⅁-brute-0 : prg⅁ brute 0b ≗ (const 0b)
  prg⅁-brute-0 R = brute-PRG-K≡0b (drop n R)

  brute′-bound : #⟨ brute′ ⟩ ≤ 2^ k
  brute′-bound = brute′-bound-aux PRG

  not∘brute′≗brute : not ∘ brute′ ≗ brute
  not∘brute′≗brute x = search-comm _∨_ _∧_ not (_==_ x ∘ PRG) de-morgan

  brute≗not∘brute′ : brute′ ≗ not ∘ brute
  brute≗not∘brute′ x = trans (sym (not-involutive _)) (cong not (not∘brute′≗brute x))
