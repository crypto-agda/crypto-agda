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

==-refl : ∀ {n} (xs : Bits n) → (xs == xs) ≡ 1b
==-refl [] = refl
==-refl (true ∷ xs) = ==-refl xs
==-refl (false ∷ xs) = ==-refl xs

_|∨|_ : ∀ {n} → (f g : Bits n → Bit) → Bits n → Bit
_|∨|_ f g x = f x ∨ g x

_|∧|_ : ∀ {n} → (f g : Bits n → Bit) → Bits n → Bit
_|∧|_ f g x = f x ∧ g x

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


  always : ∀ n → Bits n → Bit
  always _ _ = 1b
  never  : ∀ n → Bits n → Bit
  never _ _ = 0b

  search-·-ε≡ε : ∀ {a} {A : Set a} ε (_·_ : A → A → A)
                   (ε·ε : ε · ε ≡ ε) n → search {n} _·_ (const ε) ≡ ε
  search-·-ε≡ε ε _·_ ε·ε = go
    where
      go : ∀ n → search {n} _·_ (const ε) ≡ ε
      go zero = refl
      go (suc n) rewrite go n = ε·ε

  #never≡0 : ∀ n → #⟨ never n ⟩ ≡ 0
  #never≡0 = search-·-ε≡ε _ _ refl

  #always≡2^_ : ∀ n → #⟨ always n ⟩ ≡ 2^ n
  #always≡2^_ zero = refl
  #always≡2^_ (suc n) = cong₂ _+_ pf pf where pf = #always≡2^ n

  ==-comm : ∀ {n} (xs ys : Bits n) → xs == ys ≡ ys == xs
  ==-comm [] [] = refl
  ==-comm (x ∷ xs) (x₁ ∷ ys) rewrite Xor°.+-comm x x₁ | ==-comm xs ys = refl

  countᵇ : Bit → ℕ
  countᵇ b = if b then 1 else 0

  #⟨==_⟩ : ∀ {n} (xs : Bits n) → #⟨ _==_ xs ⟩ ≡ 1
  #⟨== [] ⟩ = refl
  #⟨==_⟩ {suc n} (true ∷ xs)  rewrite #never≡0 n | #⟨== xs ⟩ = refl
  #⟨==_⟩ {suc n} (false ∷ xs) rewrite #never≡0 n | #⟨== xs ⟩ = refl

  ≗-cong-search : ∀ {n a} {A : Set a} op {f g : Bits n → A} → f ≗ g → search op f ≡ search op g
  ≗-cong-search {zero}  op f≗g = f≗g []
  ≗-cong-search {suc n} op f≗g = cong₂ op (≗-cong-search op (f≗g ∘ 0∷_))
                                          (≗-cong-search op (f≗g ∘ 1∷_))

  ≗-cong-# : ∀ {n} (f g : Bits n → Bit) → f ≗ g → #⟨ f ⟩ ≡ #⟨ g ⟩
  ≗-cong-# f g f≗g = ≗-cong-search _+_ (cong countᵇ ∘ f≗g)

  #-+ : ∀ {n a b} (f : Bits (suc n) → Bit) → #⟨ f ∘ 0∷_ ⟩ ≡ a → #⟨ f ∘ 1∷_ ⟩ ≡ b → #⟨ f ⟩ ≡ a + b
  #-+ f f0 f1 rewrite f0 | f1 = refl

  take-∷ : ∀ {m a} {A : Set a} n x (xs : Vec A (n + m)) → take (suc n) (x ∷ xs) ≡ x ∷ take n xs
  take-∷ n x xs with splitAt n xs
  take-∷ _ _ ._ | _ , _ , refl = refl
  
  drop-∷ : ∀ {m a} {A : Set a} n x (xs : Vec A (n + m)) → drop (suc n) (x ∷ xs) ≡ drop n xs
  drop-∷ n x xs with splitAt n xs
  drop-∷ _ _ ._ | _ , _ , refl = refl
  
  #-take-drop : ∀ m n (f : Bits m → Bit) (g : Bits n → Bit)
                  → #⟨ (f ∘ take m) |∧| (g ∘ drop m) ⟩ ≡ #⟨ f ⟩ * #⟨ g ⟩
  #-take-drop zero n f g with f []
  ... | true rewrite ℕ°.+-comm #⟨ g ⟩ 0 = refl
  ... | false = #never≡0 n
  #-take-drop (suc m) n f g = trans (#-+ {a = #⟨ f ∘ 0∷_ ⟩ * #⟨ g ⟩} ((f ∘ take (suc m)) |∧| (g ∘ drop (suc m)))
                                    (trans (≗-cong-# ((f ∘ take (suc m)) |∧| (g ∘ drop (suc m)) ∘ 0∷_)
                                                  ((f ∘ 0∷_ ∘ take m) |∧| (g ∘ drop m))
                                                  (λ x → cong₂ (λ x y → f x ∧ g y) (take-∷ m 0b x) (drop-∷ m 0b x)))
                                         (#-take-drop m n (f ∘ 0∷_) g))
                                    (trans (≗-cong-# ((f ∘ take (suc m)) |∧| (g ∘ drop (suc m)) ∘ 1∷_)
                                                  ((f ∘ 1∷_ ∘ take m) |∧| (g ∘ drop m))
                                                  (λ x → cong₂ (λ x y → f x ∧ g y) (take-∷ m 1b x) (drop-∷ m 1b x)))
                                         (#-take-drop m n (f ∘ 1∷_) g)))
                             (sym (proj₂ ℕ°.distrib #⟨ g ⟩ #⟨ f ∘ 0∷_ ⟩ #⟨ f ∘ 1∷_ ⟩))

  #-drop-take : ∀ m n (f : Bits n → Bit) (g : Bits m → Bit)
                  → #⟨ (f ∘ drop m) |∧| (g ∘ take m) ⟩ ≡ #⟨ f ⟩ * #⟨ g ⟩
  #-drop-take m n f g =
             #⟨ (f ∘ drop m) |∧| (g ∘ take m) ⟩
           ≡⟨ ≗-cong-# ((f ∘ drop m) |∧| (g ∘ take m)) ((g ∘ take m) |∧| (f ∘ drop m)) (λ x → Bool°.+-comm (f (drop m x)) _) ⟩
             #⟨ (g ∘ take m) |∧| (f ∘ drop m) ⟩
           ≡⟨ #-take-drop m n g f ⟩
             #⟨ g ⟩ * #⟨ f ⟩
           ≡⟨ ℕ°.*-comm #⟨ g ⟩ _ ⟩
             #⟨ f ⟩ * #⟨ g ⟩
           ∎
    where open ≡-Reasoning

  #-take : ∀ m n (f : Bits m → Bit) → #⟨ f ∘ take m {n} ⟩ ≡ 2^ n * #⟨ f ⟩
  #-take m n f = #⟨ f ∘ take m {n} ⟩
               ≡⟨ #-drop-take m n (always n) f ⟩
                 #⟨ always n ⟩ * #⟨ f ⟩
               ≡⟨ cong (flip _*_ #⟨ f ⟩) (#always≡2^ n) ⟩
                 2^ n * #⟨ f ⟩
               ∎
    where open ≡-Reasoning

  #-drop : ∀ m n (f : Bits m → Bit) → #⟨ f ∘ drop n ⟩ ≡ 2^ n * #⟨ f ⟩
  #-drop m n f = #⟨ f ∘ drop n ⟩
               ≡⟨ #-take-drop n m (always n) f ⟩
                 #⟨ always n ⟩ * #⟨ f ⟩
               ≡⟨ cong (flip _*_ #⟨ f ⟩) (#always≡2^ n) ⟩
                 2^ n * #⟨ f ⟩
               ∎
    where open ≡-Reasoning

  #⟨_==⟩ : ∀ {n} (xs : Bits n) → #⟨ flip _==_ xs ⟩ ≡ 1
  #⟨ xs ==⟩ = trans (≗-cong-# (flip _==_ xs) (_==_ xs) (flip ==-comm xs)) #⟨== xs ⟩

  #⇒ : ∀ {n} (f g : Bits n → Bit) → (∀ x → T (f x) → T (g x)) → #⟨ f ⟩ ≤ #⟨ g ⟩
  #⇒ {zero} f g f⇒g with f [] | g [] | f⇒g []
  ... | true  | true  | _ = s≤s z≤n
  ... | true  | false | p = ⊥-elim (p _)
  ... | false | _     | _ = z≤n
  #⇒ {suc n} f g f⇒g = #⇒ (f ∘ 0∷_) (g ∘ 0∷_) (f⇒g ∘ 0∷_)
                  +-mono #⇒ (f ∘ 1∷_) (g ∘ 1∷_) (f⇒g ∘ 1∷_)

  #-∧-∨ᵇ : ∀ x y → countᵇ (x ∧ y) + countᵇ (x ∨ y) ≡ countᵇ x + countᵇ y
  #-∧-∨ᵇ true y rewrite ℕ°.+-comm (countᵇ y) 1 = refl
  #-∧-∨ᵇ false y = refl

  #-∧-∨ : ∀ {n} (f g : Bits n → Bit) → #⟨ f |∧| g ⟩ + #⟨ f |∨| g ⟩ ≡ #⟨ f ⟩ + #⟨ g ⟩
  #-∧-∨ {zero} f g = #-∧-∨ᵇ (f []) (g [])
  #-∧-∨ {suc n} f g =
    trans
      (trans
         (helper #⟨ (f ∘ 0∷_) |∧| (g ∘ 0∷_) ⟩
                 #⟨ (f ∘ 1∷_) |∧| (g ∘ 1∷_) ⟩
                 #⟨ (f ∘ 0∷_) |∨| (g ∘ 0∷_) ⟩
                 #⟨ (f ∘ 1∷_) |∨| (g ∘ 1∷_) ⟩)
         (cong₂ _+_ (#-∧-∨ (f ∘ 0∷_) (g ∘ 0∷_))
                    (#-∧-∨ (f ∘ 1∷_) (g ∘ 1∷_))))
      (helper #⟨ f ∘ 0∷_ ⟩ #⟨ g ∘ 0∷_ ⟩ #⟨ f ∘ 1∷_ ⟩ #⟨ g ∘ 1∷_ ⟩)
      where open SemiringSolver
            helper : ∀ x y z t → x + y + (z + t) ≡ x + z + (y + t)
            helper = solve 4 (λ x y z t → x :+ y :+ (z :+ t) := x :+ z :+ (y :+ t)) refl

  #∨' : ∀ {n} (f g : Bits n → Bit) → #⟨ f |∨| g ⟩ ≤ #⟨ f ⟩ + #⟨ g ⟩
  #∨' {zero} f g with f []
  ... | true  = s≤s z≤n
  ... | false = ℕ≤.refl
  #∨' {suc _} f g = ℕ≤.trans (#∨' (f ∘ 0∷_) (g ∘ 0∷_) +-mono
                               #∨' (f ∘ 1∷_) (g ∘ 1∷_))
                      (ℕ≤.reflexive
                        (helper #⟨ f ∘ 0∷_ ⟩ #⟨ g ∘ 0∷_ ⟩ #⟨ f ∘ 1∷_ ⟩ #⟨ g ∘ 1∷_ ⟩))
      where open SemiringSolver
            helper : ∀ x y z t → x + y + (z + t) ≡ x + z + (y + t)
            helper = solve 4 (λ x y z t → x :+ y :+ (z :+ t) := x :+ z :+ (y :+ t)) refl

  #∨ : ∀ {m n o} {f g : Bits o → Bit} → #⟨ f ⟩ ≤ m → #⟨ g ⟩ ≤ n → #⟨ (λ x → f x ∨ g x) ⟩ ≤ (m + n)
  #∨ {m} {n} {o} {f} {g} pf pg = ℕ≤.trans (#∨' f g) (pf +-mono pg)

  ∧⇒∨ : ∀ x y → T (x ∧ y) → T (x ‌∨ y)
  ∧⇒∨ true y = _
  ∧⇒∨ false y = λ ()

  #∧ : ∀ {m n o} {f g : Bits o → Bit} → #⟨ f ⟩ ≤ m → #⟨ g ⟩ ≤ n → #⟨ f |∧| g ⟩ ≤ (m + n)
  #∧ {f = f} {g} pf pg = ℕ≤.trans (#⇒ (f |∧| g) (f |∨| g) (λ x → ∧⇒∨ (f x) (g x))) (#∨ {f = f} pf pg)

  lem' : ∀ {n} (f g : Bits n → Bit) → f |∨| g ≗ not ∘ ((not ∘ f) |∧| (not ∘ g))
  lem' f g x with f x
  ... | true = refl
  ... | false = sym (not-involutive _)

  lem : ∀ {n} op (f g : Bits n → Bit) → search op (f |∨| g) ≡ search op (not ∘ ((not ∘ f) |∧| (not ∘ g)))
  lem op f g = ≗-cong-search op {-(f |∨| g) (not ∘ ((not ∘ f) |∧| (not ∘ g)))-} (lem' f g) 

  lem'' :
    ∀ {n a b}
      {A : Set a} {B : Set b}
      (_+_ : A → A → A)
      (_*_ : B → B → B)
      (f : A → B)
      (p : Bits n → A)
      (hom : ∀ x y → f (x + y) ≡ f x * f y)
      → f (search _+_ p) ≡ search _*_ (f ∘ p)
  lem'' {zero} _+_ _*_ f p hom = refl
  lem'' {suc n} _+_ _*_ f p hom = trans (hom _ _) (cong₂ _*_ (lem'' {n} _+_ _*_ f (p ∘ 0∷_) hom) (lem'' _+_ _*_ f (p ∘ 1∷_) hom))

  [0↔_] : ∀ {n} → Fin n → Bits n → Bits n
  [0↔_] {zero}  i xs = xs
  [0↔_] {suc n} i xs = lookup i xs ∷ tail (xs [ i ]≔ head xs)

  [0↔1] : Bits 2 → Bits 2
  [0↔1] = [0↔ suc zero ]

  [0↔1]-spec : [0↔1] ≗ (λ { (x ∷ y ∷ []) → y ∷ x ∷ [] })
  [0↔1]-spec (x ∷ y ∷ []) = refl

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

  de-morgan : ∀ x y → not (x ∨ y) ≡ not x ∧ not y
  de-morgan true  _ = refl
  de-morgan false _ = refl

  not∘brute′≗brute : not ∘ brute′ ≗ brute
  not∘brute′≗brute x = lem'' _∨_ _∧_ not (_==_ x ∘ PRG) de-morgan

  brute≗not∘brute′ : brute′ ≗ not ∘ brute
  brute≗not∘brute′ x = trans (sym (not-involutive _)) (cong not (not∘brute′≗brute x))
