open import Level.NP
open import Type
open import Function
open import Algebra.FunctionProperties.Eq
open import Data.Zero
open import Data.Two hiding (_≟_)
open import Data.Nat.NP as ℕ hiding (_≟_)
open import Data.Product renaming (proj₁ to fst) hiding (map)
open import Data.Fin.NP as Fin
open import Data.Vec
open import Data.Vec.Properties
import Data.List as L
open L using (List; []; _∷_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.NP
import ZK.Sigma-Protocol
import ZK.Chaum-Pedersen

module ZK.Disjunctive
    (G ℤq : ★)
    (g    : G)
    (_^_  : G  → ℤq → G)
    (_·_  : G  → G  → G)
    (_/_  : G  → G  → G)
    (_+_  : ℤq → ℤq → ℤq)
    (_-_  : ℤq → ℤq → ℤq)
    (_*_  : ℤq → ℤq → ℤq)
    (_==_ : (x y : G) → 𝟚)
    (_==ℤq_ : (x y : ℤq) → 𝟚)
    (max  : ℕ)
    (Fin▹ℤq : Fin (suc max) → ℤq)
    where

  0q : ℤq
  0q = Fin▹ℤq zero

  record Structure : Set where
    field
      ✓-==ℤq : ∀ {x y} → x ≡ y → ✓ (x ==ℤq y)
      ✓-== : ∀ {x y} → x ≡ y → ✓ (x == y)
      ^-+  : ∀ {b x y} → b ^(x + y) ≡ (b ^ x) · (b ^ y)
      ^-*  : ∀ {b x y} → b ^(x * y) ≡ (b ^ x) ^ y
      ·-/  : ∀ {P Q} → P ≡ (P · Q) / Q
      /-·  : ∀ {P Q} → P ≡ (P / Q) · Q
      -+   : ∀ {x y} → (x - y) + y ≡ x
      +-comm     : Commutative _+_
      +-assoc    : Associative _+_
      0-+-identity : Identity 0q _+_

  _‼_ : ∀ {n} {A : ★} → Vec A n → Fin n → A
  v ‼ i = lookup i v

  tabulate′ : ∀ {A : ★} (n : ℕ) (f : ℕ → A) → Vec A n
  tabulate′ n f = tabulate {n = n} (f ∘ Fin▹ℕ)

  tabulateL : ∀ {A : ★} (n : ℕ) (f : ℕ → A) → List A
  tabulateL n f = toList (tabulate′ n f)

  tubulate :
    ∀ {A : ★} {n} (m : Fin n)
      (f≢m : Fin n → A)
      (f≡m : A)
    → Vec A n
  tubulate zero    f x = x  ∷ tabulate (f ∘ suc)
  tubulate (suc m) f x = fz ∷ tubulate m (f ∘ suc) x
     where fz = f zero

  tubulate-tabulate[]≔ :
      ∀ {n} {A : ★} (m : Fin n)
        {f≢m : Fin n → A}
        {f≡m : A}
      → tubulate m f≢m f≡m ≡ (tabulate f≢m)[ m ]≔ f≡m
  tubulate-tabulate[]≔ zero    = refl
  tubulate-tabulate[]≔ (suc m) = ap (_∷_ _) (tubulate-tabulate[]≔ m)

  tubulate‼m :
      ∀ {n} {A : ★} (m : Fin n)
        (f≢m : Fin n → A)
        (f≡m : A)
      → tubulate m f≢m f≡m ‼ m ≡ f≡m
  tubulate‼m zero    _ _ = refl
  tubulate‼m (suc m) _ _ = tubulate‼m m _ _

  tubulate‼≢m :
      ∀ {n} {A : ★} (m : Fin n)
        (f≢m : Fin n → A)
        (f≡m : A)
        i (m≢i : m ≢ i) →
        tubulate m f≢m f≡m ‼ i ≡ f≢m i
  tubulate‼≢m m f≢m f≡m i m≢i
    rewrite tubulate-tabulate[]≔ m {f≢m} {f≡m}
          | lookup∘update′ (m≢i ∘ !_) (tabulate f≢m) f≡m
          = lookup∘tabulate f≢m i
  {-
  tubulate‼≢m zero       zero    i≢m = 𝟘-elim (i≢m refl)
  tubulate‼≢m (suc m)    zero    i≢m = refl
  tubulate‼≢m zero {f≢m} (suc i) i≢m = lookup∘tabulate f≢m (suc i)
  tubulate‼≢m (suc m)    (suc i) i≢m = tubulate‼≢m m i (i≢m ∘ ap suc)
  -}

  module _ {A : ★} where
    _⟦_⟧≔_ : ∀ {n} (f : Fin n → A) (i : Fin n) (z : A) → Fin n → A
    (f ⟦ zero  ⟧≔ z) zero    = z
    (f ⟦ zero  ⟧≔ z) (suc j) = f (suc j)
    (f ⟦ suc i ⟧≔ z) zero    = f zero
    (f ⟦ suc i ⟧≔ z) (suc j) = ((f ∘ suc) ⟦ i ⟧≔ z) j

    tabulate-⟦⟧≔ : ∀ {n} (f : Fin n → A) (i : Fin n) (z : A) → tabulate (f ⟦ i ⟧≔ z) ≡ tabulate f [ i ]≔ z
    tabulate-⟦⟧≔ f zero z = refl
    tabulate-⟦⟧≔ f (suc i) z = ap (_∷_ _) (tabulate-⟦⟧≔ (f ∘ suc) i z)

  {-
  module _ {A : ★} where
    [_≔_]_ : ∀ {n} (m : Fin n) (z : A) (xs : Vec A n) → Vec A n
    [ zero  ≔ z ] (x ∷ xs) = z ∷ xs
    [ suc m ≔ z ] (x ∷ xs) = x ∷ [ m ≔ z ] xs

    [≔]-‼-m : ∀ {n} (m : Fin n) (z : A) (xs : Vec A n) → [ m ≔ z ] xs ‼ m ≡ z
    [≔]-‼-m m z xs = {!!}
    [≔]-‼-≢m : ∀ {n} (m : Fin n) (z : A) (xs : Vec A n) j (j≢m : j ≢ m) → [ m ≔ z ] xs ‼ j ≡ xs ‼ j
    -}

  -- split : ∀ {A : ★} {n} (m : Fin n) → 

  {-
  module _ {A : ★}
           (B : ℕ → ★)
           (_◅′_ _◅_ : ∀ {n} → A → B n → B (suc n))
           (ε   : B zero) where
    fuldr : ∀ {n} (m : Fin n) (f : Fin n → A) → B n
    fuldr zero    f = f zero ◅′ iterate B _◅_ ε (f ∘ suc)
    fuldr (suc m) f = f zero ◅ fuldr m (f ∘ suc)
  -}

  {-
  xs [ m ]≔ z ≡ take xs ++ z ∷ drop xs

  foldr B _◅_ ε (xs [ m ]≔ z)
  ≡
  (foldr B _◅_ ε (xs [ m ]≔ ε))
  -}

  module _ {A : ★}
           (_+_ : A → A → A)
           (+-comm     : Commutative _+_)
           (+-assoc    : Associative _+_)
           (z z' : A)
           where
     +-exch-top : ∀ {a b c} → a + (b + c) ≡ b + (a + c)
     +-exch-top = ! +-assoc ∙ ap₂ _+_ +-comm refl ∙ +-assoc
     +-exch : ∀ {a b c d e} → a + c ≡ d + e → a + (b + c) ≡ d + (b + e)
     +-exch p = +-exch-top ∙ ap (_+_ _) p ∙ ! +-exch-top
     foldr-exch : ∀ {n} (xs : Vec A n) → z + foldr _ _+_ z' xs ≡ z' + foldr _ _+_ z xs 
     foldr-exch [] = +-comm
     foldr-exch (x ∷ xs) = +-exch (foldr-exch xs)
     foldr-[]≔-exch : ∀ {n} (xs : Vec A n) (m : Fin n)
                         → foldr _ _+_ z' (xs [ m ]≔ z)
                         ≡  foldr _ _+_ z  (xs [ m ]≔ z')
     foldr-[]≔-exch (x ∷ xs) zero    = foldr-exch xs
     foldr-[]≔-exch (x ∷ xs) (suc m) = ap (_+_ x) (foldr-[]≔-exch xs m)

     foldr-[]≔-exch′ : ∀ {n ε} (xs : Vec A n) (m : Fin n)
                         → z' + foldr _ _+_ ε (xs [ m ]≔ z)
                         ≡  z  + foldr _ _+_ ε (xs [ m ]≔ z')
     foldr-[]≔-exch′ (x ∷ xs) zero    = +-exch-top
     foldr-[]≔-exch′ (x ∷ xs) (suc m) = +-exch (foldr-[]≔-exch′ xs m)

     -- foldr _ _+_ z ≡ foldr _ _+_ ε + z


  {-
  fuldr-as-tubulate :
    ∀ {A : ★} {n} (m : Fin n) →
    fuldr (Vec A) ? _∷_ [] m xs
  -}
 --   x ◅′ (y ◅ z) ≡ y ◅′ 

 {-
  module _ {A : ★}
           (B : ℕ → ★)
           (_◅_ : ∀ {n} → A → B n → B (suc n))
           (ε   : B zero)
           where

    foldr-tubulate : ∀ {n} (m : Fin n)
                       {f≢m : Fin n → A}
                       {f≡m : A}
                  → foldr B _◅_ ε (tubulate m f≢m f≡m) ≡ foldr B (λ _ b → f≡m ◅ b) _◅_ ε m f≢m
    foldr-tubulate zero    = ap (_◅_ _) (! iterate-foldr∘tabulate B _◅_ ε _)
    foldr-tubulate (suc m) = ap (_◅_ _) (foldr-tubulate m) 

    foldr-tubulate : ∀ {n} (m : Fin n)
                       {f≢m : Fin n → A}
                       {f≡m : A}
                  → foldr B _◅_ ε (tubulate m f≢m f≡m) ≡ fuldr B (λ _ b → f≡m ◅ b) _◅_ ε m f≢m
    foldr-tubulate zero    = ap (_◅_ _) (! iterate-foldr∘tabulate B _◅_ ε _)
    foldr-tubulate (suc m) = ap (_◅_ _) (foldr-tubulate m) 
-}
{-
  module _ {A : ★}
           (B : ℕ → ★)
           (_◅_ : ∀ {n} → A → B n → B (suc n))
           (ε   : B zero) where
    tribulate :
        ∀ {n} (m : Fin n)
          (f≢m : Fin n → A) -- (f≢m : (i : Fin n) → i ≢ m → A)
          (f≡m : B (Fin▹ℕ m) → B (n ℕ-ℕ suc m) → A)
        → Vec A n
    tribulate zero f x = x ε (foldr B _◅_ ε tl) ∷ tl
         where tl = tabulate (f ∘ suc)
    tribulate (suc m) f x = fz ∷ tribulate m (f ∘ suc) (x ∘ _◅_ fz)
         where fz = f zero

    module _
        (P : A → ★)
        (Q : ∀ {n} → B n → ★)
        (Q[_◅_] : ∀ {n x} {y : B n} → P x → Q y → Q (x ◅ y))
        (Qε : Q ε) where
        tabulate-spec :
          ∀ {n} {f : Fin n → A}
            (Pf : ∀ i → P (f i))
          → Q (foldr B _◅_ ε (tabulate f))
        tabulate-spec {zero}  Pf = Qε
        tabulate-spec {suc n} Pf = Q[ Pf zero ◅ tabulate-spec (Pf ∘ suc) ]

        tribulate-spec :
          ∀ {n} (m : Fin n)
            {f≢m : Fin n → A}
            {f≡m : B (Fin▹ℕ m) → B (n ℕ-ℕ suc m) → A}
            (P≢m : ∀ i → i ≢ m → P (f≢m i))
            (P≡m : ∀ {pr po} → Q pr → Q po → P (f≡m pr po))
          → ∀ i → P (tribulate m f≢m f≡m ‼ i)
        tribulate-spec zero       P≢m P≡m zero
          = P≡m Qε (tabulate-spec (λ i → P≢m (suc i) (λ())))
        tribulate-spec (suc m)    P≢m P≡m zero
          = P≢m zero (λ())
        tribulate-spec zero {f≢m} P≢m P≡m (suc i)
          rewrite lookup∘tabulate (f≢m ∘ suc) i
          = P≢m (suc i) (λ())
        tribulate-spec (suc m) P≢m P≡m (suc i)
          = tribulate-spec m (λ j j≢m → P≢m (suc j) (j≢m ∘ Fin.suc-injective))
                             (λ Qpr Qpo → P≡m Q[ P≢m zero (λ()) ◅ Qpr ] Qpo) i

        tribulate≢m :
          ∀ {n} (m : Fin n)
            {f≢m : Fin n → A}
            {f≡m : B (Fin▹ℕ m) → B (n ℕ-ℕ suc m) → A}
            i (i≢m : i ≢ m) →
            tribulate m f≢m f≡m ‼ i ≡ f≢m i
        tribulate≢m = {!!}

    tribulate-naive :
      ∀ {n} (m : Fin n)
        (f≢m : ℕ → A)
        (f≡m : B (Fin▹ℕ m) → B (n ℕ-ℕ suc m) → A)
      → Vec A (Fin▹ℕ m ℕ.+ suc (n ℕ-ℕ suc m))
    tribulate-naive {n = n} m f≢m f≡m
       = prefix ++ f≡m fprefix fpostfix ∷ postfix
       where
         prefix   = tabulate′ (Fin▹ℕ m)      f≢m
         postfix  = tabulate′ (n ℕ-ℕ suc m) (f≢m ∘ ℕ._+_ (Fin▹ℕ (suc m)))
         fprefix  = foldr B _◅_ ε prefix
         fpostfix = foldr B _◅_ ε postfix

    tribulate-correct :
      ∀ {n} (m : Fin n)
        (f≢m : ℕ → A)
        (f≡m : B (Fin▹ℕ m) → B (n ℕ-ℕ suc m) → A)
      → toList (tribulate m (f≢m ∘ Fin▹ℕ) f≡m)
       ≡ toList (tribulate-naive m f≢m f≡m)
    tribulate-correct zero    f≢m f≡m = refl
    tribulate-correct (suc m) f≢m f≡m =
      ap (_∷_ (f≢m 0)) (tribulate-correct m (f≢m ∘ suc) (f≡m ∘ _◅_ (f≢m 0)))

  test-tribulate1 :
    tribulate (Vec ℕ) _∷_ [] (# 4) Fin▹ℕ (λ _ _ → 42) ≡ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 42 ∷ 5 ∷ [])
  test-tribulate1 = refl

  test-tribulate2 :
    tribulate _ L._++_ L.[]
              (# 4) (L.[_] ∘ Fin▹ℕ)
              (λ xs ys → xs L.++ 42 ∷ ys)
      ≡
    (0 ∷ []) ∷ (1 ∷ []) ∷ (2 ∷ []) ∷ (3 ∷ []) ∷ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 42 ∷ 5 ∷ []) ∷ (5 ∷ []) ∷ []
  test-tribulate2 = refl

  test-tribulate3 :
    tribulate (Vec ℕ) _∷_ [] (# 3) Fin▹ℕ (λ _ _ → 42) ≡ (0 ∷ 1 ∷ 2 ∷ 42 ∷ [])
  test-tribulate3 = refl

  test-tribulate4 :
    tribulate (const ℕ) ℕ._+_ 0 (# 3) Fin▹ℕ (λ x y → (x ℕ.∸ 1) ℕ.+ 10 ℕ.* y) ≡ (0 ∷ 1 ∷ 2 ∷ 42 ∷ 4 ∷ [])
  test-tribulate4 = refl

     {-
  tribulate :
    ∀ {A : ★} {n} (m : Fin n)
      (f≢m : Fin n → A)
      (f≡m : Vec A (Fin▹ℕ m) → Vec A (n ℕ-ℕ suc m) → A)
    → Vec A n
  tribulate zero f x = x [] tl ∷ tl
     where tl = tabulate (f ∘ suc)
  tribulate (suc m) f x = fz ∷ tribulate m (f ∘ suc) (x ∘ _∷_ fz)
     where fz = f zero

  test-tribulate1 :
    tribulate (# 4) Fin▹ℕ (λ _ _ → 42) ≡ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 42 ∷ 5 ∷ [])
  test-tribulate1 = refl

  test-tribulate2 :
    tribulate (# 4) (L.[_] ∘ Fin▹ℕ)
              (λ xs ys → L.concat (toList (xs ++ L.[ 42 ] ∷ ys)))
      ≡
    (0 ∷ []) ∷ (1 ∷ []) ∷ (2 ∷ []) ∷ (3 ∷ []) ∷ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 42 ∷ 5 ∷ []) ∷ (5 ∷ []) ∷ []
  test-tribulate2 = refl

  test-tribulate3 :
    tribulate (# 3) Fin▹ℕ (λ _ _ → 42) ≡ (0 ∷ 1 ∷ 2 ∷ 42 ∷ [])
  test-tribulate3 = refl

  tribulate-naive :
    ∀ {A : ★} {n} (m : Fin n)
      (f≢m : ℕ → A)
      (f≡m : List A → List A → A)
    → List A
  tribulate-naive {n = n} m f≢m f≡m
     = prefix L.++ f≡m prefix postfix ∷ postfix
     where
       prefix  = tabulateL (Fin▹ℕ m)      f≢m
       postfix = tabulateL (n ℕ-ℕ suc m) (f≢m ∘ ℕ._+_ (Fin▹ℕ (suc m)))

  tribulate-correct :
    ∀ {A : ★} {n} (m : Fin n)
      (f≢m : ℕ → A)
      (f≡m : List A → List A → A)
    → toList (tribulate m (f≢m ∘ Fin▹ℕ) (λ xs ys → f≡m (toList xs) (toList ys)))
     ≡ tribulate-naive m f≢m f≡m
  tribulate-correct zero    f≢m f≡m = refl
  tribulate-correct (suc m) f≢m f≡m =
    ap (_∷_ (f≢m 0)) (tribulate-correct m (f≢m ∘ suc) (f≡m ∘ _∷_ (f≢m 0)))
    -}
-}
  and : ∀ {n} → Vec 𝟚 n → 𝟚
  and = foldr _ _∧_ 1₂

  ✓-and : ∀ {n} {v : Vec 𝟚 n} (✓p : ∀ i → ✓(v ‼ i)) → ✓(and v)
  ✓-and {v = []}     ✓p = _
  ✓-and {v = x ∷ xs} ✓p = ✓∧ (✓p zero) (✓-and (✓p ∘ suc))

  module _ {A B C D : ★} {n}
           (f : Fin n → A → B → C → D)
           (va : Vec A n) (vb : Vec B n) (vc : Vec C n) where
    mapi3 : Vec D n
    mapi3 = replicate f ⊛ allFin _ ⊛ va ⊛ vb ⊛ vc

  open import Category.Applicative.Indexed -- .Morphism
  module _ {A B C D : ★} {n}
           {f : Fin n → A → B → C → D}
           {va : Vec A n} {vb : Vec B n} {vc : Vec C n}
           i where
    -- Surely this could be done better...
    open Morphism (lookup-morphism {₀} {n} i)
    mapi3‼ : mapi3 f va vb vc ‼ i ≡ f i (va ‼ i) (vb ‼ i) (vc ‼ i)
    mapi3‼ = op-⊛ (replicate f ⊛ allFin _ ⊛ va ⊛ vb) vc
           ∙ ap (λ g → g (vc ‼ i))
                (op-⊛ (replicate f ⊛ allFin _ ⊛ va) vb)
           ∙ ap (λ g → g (vb ‼ i) (vc ‼ i)) (op-⊛ (replicate f ⊛ allFin _) va)
           ∙ ap (λ g → g (va ‼ i) (vb ‼ i) (vc ‼ i)) (op-⊛ (replicate f) (allFin _))
           ∙ ap (λ g → g (allFin _ ‼ i) (va ‼ i) (vb ‼ i) (vc ‼ i)) (op-pure f)
           ∙ ap (λ x → f x (va ‼ i) (vb ‼ i) (vc ‼ i)) (lookup∘tabulate id i)

  module _ {A B C : ★} {n}
           (p : Fin n → A → B → C → 𝟚)
           (va : Vec A n) (vb : Vec B n) (vc : Vec C n) where
    all3 : 𝟚
    all3 = and (mapi3 p va vb vc)

  module _ {A B C : ★} where
    ✓-all3 : ∀ {n}
           {p  : Fin n → A → B → C → 𝟚}
           {va : Vec A n} {vb : Vec B n} {vc : Vec C n}
           (✓p : ∀ i → ✓(p i (va ‼ i) (vb ‼ i) (vc ‼ i)))
           → ✓(all3 p va vb vc)
    ✓-all3 {p = p} {va} {vb} {vc} ✓p = ✓-and {v = mapi3 p va vb vc} (λ i → tr ✓ (! mapi3‼ i) (✓p i))

  sumℤq : ∀ {n} → Vec ℤq n → ℤq
  sumℤq = foldr _ _+_ 0q

  sumℤq-fun : ∀ {n} (f : Fin n → ℤq) → ℤq
  sumℤq-fun = iterate _ _+_ 0q

  module CP = ZK.Chaum-Pedersen G ℤq g _^_ _·_ _/_ _+_ _*_ _==_
  open CP using (PubKey; CipherText; EncRnd; enc)

  VecCommitments = Vec CP.Commitment (suc max)
  VecChallenges  = Vec CP.Challenge  (suc max)
  VecResponses   = Vec CP.Response   (suc max)

  module Interactive (y : PubKey) where
    Response   = VecChallenges × VecResponses

    open ZK.Sigma-Protocol VecCommitments ℤq Response public

    private
      M = λ i → g ^ Fin▹ℤq i

    module _ (ct : CipherText) where
      verifier1 = λ i A c s → CP.verifier y (M i) ct (CP.mk A c s)

      -- H-commitments is the actual challenge for this Σ-protocol
      verifier : Verifier
      verifier (mk commitments H-commitments (challenges , responses))
          = all3 verifier1 commitments challenges responses
          ∧ sumℤq challenges ==ℤq H-commitments

    module Prover-and-correctness
             (i : Fin (suc max))
             (rnd-challenge  : Fin (suc max) → CP.Challenge) -- the iᵗʰ slot is not used
             (rnd-response   : Fin (suc max) → CP.Response)  -- the iᵗʰ slot is not used
             (r : EncRnd) (w : ℤq)
             where

      ct = enc y r (M i)

      commitment-i = CP.prover-commitment y r w

      simulated-commitment-j : (j : Fin (suc max)) → CP.Commitment
      simulated-commitment-j j
        = CP.simulate-commitment y (M j) ct (rnd-challenge j) (rnd-response j)

      commitments = tubulate i simulated-commitment-j commitment-i

      sum≢i = sumℤq-fun (rnd-challenge ⟦ i ⟧≔ 0q)

      prover-response : ℤq → Response
      prover-response Hcommitments = (challenges , responses)
        module Prover-response where
          challenge-i = Hcommitments - sum≢i

          challenges = tubulate i rnd-challenge challenge-i

          response-i = CP.prover-response y r w (challenges ‼ i)

          responses = tubulate i rnd-response response-i

      prover : Prover
      prover = commitments , prover-response

      module Correctness-proof (structure : Structure) where
        open Structure structure
        CPcs = λ M c s → CP.Correct-simulation.correct-simulation y M ct c s ✓-== /-·
        CPcp = CP.Correctness-proof.correctness ✓-== ^-+ ^-* ·-/ y r w
        correctness : Correctness prover (verifier ct)
        correctness Hcommitments = ✓∧ (✓-all3 {p = verifier1 ct} helper) helper'
          where
            open Prover-response Hcommitments
            open ≡-Reasoning
            c-i-e : challenges ‼ i ≡ challenge-i
            c-i-e = tubulate‼m i _ _
            W-i-e : commitments ‼ i ≡ commitment-i
            W-i-e = tubulate‼m i _ _
            s-i-e : responses ‼ i ≡ response-i
            s-i-e = tubulate‼m i _ _
            s-j-e : ∀ j → i ≢ j → responses ‼ j ≡ rnd-response j
            s-j-e = tubulate‼≢m i _ _
            W-j-e : ∀ j → i ≢ j → commitments ‼ j ≡ simulated-commitment-j j
            W-j-e = tubulate‼≢m i _ _
            c-j-e : ∀ j → i ≢ j → challenges ‼ j ≡ rnd-challenge j
            c-j-e = tubulate‼≢m i _ _
            helper : ∀ j → ✓(verifier1 ct j (commitments ‼ j) (challenges ‼ j) (responses ‼ j))
            helper j with Fin._≟_ i j
            helper .i | yes refl
              rewrite s-i-e | W-i-e | tubulate‼m i rnd-challenge challenge-i
                    = CPcp (M i) challenge-i
            helper  j | no ¬p rewrite s-j-e j ¬p | W-j-e j ¬p | c-j-e j ¬p = CPcs _ _ _
            sum≢i-def : sum≢i ≡ sumℤq (tabulate rnd-challenge [ i ]≔ 0q)
            sum≢i-def = iterate-foldr∘tabulate _ _+_ 0q (rnd-challenge ⟦ i ⟧≔ 0q)
                      ∙ ap sumℤq (tabulate-⟦⟧≔ rnd-challenge i 0q)
            helper' : ✓(sumℤq challenges ==ℤq Hcommitments)
            helper' = ✓-==ℤq (sumℤq challenges
                             ≡⟨ ap sumℤq (tubulate-tabulate[]≔ i) ⟩
                              sumℤq (tabulate rnd-challenge [ i ]≔ challenge-i)
                             ≡⟨ ! fst 0-+-identity ⟩
                              0q + sumℤq (tabulate rnd-challenge [ i ]≔ challenge-i)
                             ≡⟨ foldr-[]≔-exch′ _+_ +-comm +-assoc challenge-i 0q (tabulate rnd-challenge) i ⟩
                              challenge-i + sumℤq (tabulate rnd-challenge [ i ]≔ 0q)
                             ≡⟨  ap (_+_ challenge-i) (! sum≢i-def)  ⟩
                              challenge-i + sum≢i
                             ≡⟨  -+  ⟩
                              Hcommitments
                             ∎)

    -- Like Prover-and-correctness but avoids wasting randomness for r and w
    -- This is maybe not a good idea as this is rather brittle
    module Prover-and-correctness′
             (i : Fin (suc max))
             (rnd-challenge  : Fin (suc max) → CP.Challenge)
             (rnd-response   : Fin (suc max) → CP.Response)
      = Prover-and-correctness i rnd-challenge rnd-response (rnd-challenge i) (rnd-response i)

  module Non-interactive
    (y : PubKey)
    (H : VecCommitments → ℤq)
    where
    module I = Interactive y

    open ZK.Sigma-Protocol VecCommitments VecChallenges VecResponses public
      using (Transcript; mk; Verifier)

    module _ (ct : CipherText) where
        verifier : Verifier
        verifier (mk commitments challenges responses)
          = I.verifier ct (I.mk commitments (H commitments) (challenges , responses))

    module Prover-and-correctness
             (i : Fin (suc max))
             (rnd-challenge  : Fin (suc max) → CP.Challenge) -- the iᵗʰ slot is not used
             (rnd-response   : Fin (suc max) → CP.Response)  -- the iᵗʰ slot is not used
             (r : EncRnd) (w : ℤq)
             where
      module IPC = I.Prover-and-correctness i rnd-challenge rnd-response r w
      open IPC using (commitments; ct)
      open IPC.Prover-response (H commitments)
      transcript : Transcript
      transcript = mk commitments challenges responses
      module Correctness-proof (structure : Structure) where
        correctness : ✓ (verifier ct transcript)
        correctness = IPC.Correctness-proof.correctness structure (H commitments)

-- -}
-- -}
-- -}
-- -}
