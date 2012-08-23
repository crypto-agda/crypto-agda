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
  brute′ m = search _∨_ {k} ((_==_ m) ∘ PRG)

  -- ``Looks random if the message is not a possible output of the PRG''
  brute : Adv
  brute m = search _∧_ {k} (not ∘ (_==_ m) ∘ PRG)

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
  not∘brute′≗brute x = search-hom _∨_ _∧_ not (_==_ x ∘ PRG) de-morgan

  brute≗not∘brute′ : brute′ ≗ not ∘ brute
  brute≗not∘brute′ x = trans (sym (not-involutive _)) (cong not (not∘brute′≗brute x))

module PRG⅁₂ {k n |R|ᵃ : ℕ} (PRG : PRGFun k n) where

    module AbsAdv {t} {T : Set t} (funU : FunUniverse T) where
        open FunUniverse funU

        M   =  Bits n
        K   =  Bits k
        `M  = `Bits n
        `K  = `Bits k
        Rᵃ  =  Bits |R|ᵃ
        `Rᵃ = `Bits |R|ᵃ

        Adv : Set
        Adv = `Rᵃ `× `M `→ `Bit

        {-
    red : SemSecAdv |R|ᵃ → PRGAdv |R|ᵃ
    red (mk A₀ A₁ A₂ A₃) = λ (rᵃ , p) → let (m , s₁) = A₁ (A₀ rᵃ) in
                                       let (b , _) = A₂ (p ⊕ m 0b , s₁) in b
                                       -- if b ≡ 0b it means the adversary won
                                       -- so it's probably the case that p was "PRG ⁇"

  -- the semsec game, here adv A is playing against the Encrypt∘fst or Encrypt∘snd
  E⇄ A : ⅁?
  E⇄ A b = A(E(m b)) -- m comes from A as well

  -- the PRG game, here adv A is playing against ⁇ or PRG
  ⁇⇄ A : ⅁?
  ⁇⇄ A 0b = A PRG⁇
  ⁇⇄ A 1b = A ⁇

  E' p m = p ⊕ m
  redA p = ⟨E' p⟩⇄ A 0b

  _≡#_ -- same count
  f ≡# g = #f ≡ #g

  -- The one time pad cipher
  OTP m = ⁇ ⊕ m

  -- OTP has the same count than ⁇
  OTP m ≡# ??
  OTP⇄ A b ≡# ⁇
  OTP⇄ A 0b ≡# OTP⇄ A 1b

  -- adv A breaking encryption E implies adv redA breaking PRG
  E⇄ A ⇓ ⁇⇄ redA

  breaks (E⇄ A) ≡ E⇄ A 0b ]-[ E⇄ A 1b
  breaks (⁇⇄ redA) ≡ ⁇⇄ redA 0b ]-[ ⁇⇄ redA 1b
                     ≡ redA PRG⁇   ]-[ redA ⁇

  ⁇⇄ redA 0b ≡  redA PRG⁇
               ≡  ⟨E' PRG⁇⟩⇄ A 0b
               ≡  E⇄ A 0b
              ]-[ E⇄ A 1b

  ⁇⇄ redA 1b ≡  redA ⁇
               ≡  ⟨E' ⁇⟩⇄ A 0b
               ≡  OTP⇄ A 0b
               ≡# OTP⇄ A 1b
               ≡  ⟨E' ⁇⟩⇄ A 1b

  Goal:
    breaks (⁇⇄ redA) ⇔ ⁇⇄ redA 0b ]-[ ⁇⇄ redA 1b
    -}
