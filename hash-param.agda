module hash-param where

open import Type using (★_)
open import Function
open import Reflection.Param
open import Data.List.NP as L renaming (dup to dupL)
open import Data.List.Properties.NP
open import Data.Zero
open import Data.Two
open import Data.One
open import Data.Product.NP
open import Data.Sum.NP
open import Data.Nat.NP hiding (_==_)
open import Data.Fin hiding (_+_; pred)
import Data.Vec.NP as V
open V using (Vec; []; _∷_)
import Algebra.FunctionProperties.Eq
open Algebra.FunctionProperties.Eq.Implicits
open import Relation.Binary.PropositionalEquality.NP
open import Relation.Binary
open import Relation.Nullary
open import Coinduction

module _ {A : Set} where
    tabulate : ∀ {n} → (Fin n → A) → List A
    tabulate = V.toList ∘ V.tabulate

Injective₂ : {A B C : Set}(f : A → B → C) → Set
Injective₂ f = ∀ {x} → Injective (f x)

module PRNG where
    module PRNG {B D : Set} (H : B → D) {n} (mkB : Fin n → B) where
      prng : List D
      prng = tabulate (H ∘ mkB)

    data DPRNG (B : Set) : Set where
      dH : B → DPRNG B

    dprng : ∀ {B : Set} {n} (mkB : Fin n → B) → List (DPRNG B)
    dprng = PRNG.prng dH

    fprng : ∀ {n} → List (Fin n)
    fprng = PRNG.prng id id

    fprng-allFin : ∀ {n} → fprng {n} ≡ V.toList (V.allFin n)
    fprng-allFin = refl

    module PRNG-Key {Key B D : Set} (H : Key → B → D) {n} (mkB : Fin n → B) where
      prng : Key → List D
      prng k = PRNG.prng (H k) mkB

-- Remark that the HMAC specification requires to pad the key in the following
-- way:
--   key size <= block size: pad to the right with zeros
--   key size >  block size: hash the key
module HMAC where
  module HMAC-mono
    {B : Set}
    (opad⊕_ ipad⊕_ : B → B)
    (H : List B → B)
    where
    hmac : B → List B → B
    hmac key msg = H (opad⊕ key ∷ H (ipad⊕ key ∷ msg) ∷ [])

  module HMAC
    {Key B D : Set}
    (opad⊕_ ipad⊕_ : Key → B)
    (H : List B → D)
    (E : D → List B) -- E as in "embed"
    where
    hmac : Key → List B → D
    hmac key msg = H (opad⊕ key ∷ E (H (ipad⊕ key ∷ msg)))

  module HMAC-id
    {B : Set}
    where
    hmac-id : B → List B → List B
    hmac-id = HMAC.hmac id id id id
    hmac-id-code : hmac-id ≡ λ key msg → key ∷ key ∷ msg
    hmac-id-code = refl

module Signing
  {VerifKey SignKey : Set}
  (verifkey : SignKey → VerifKey)
  {D Sig Rsign : Set}
  (sign     : Rsign → SignKey → D → Sig)
  (Verify   : VerifKey → D → Sig → Set)
  (correct  : ∀ r sk d → Verify (verifkey sk) d (sign r sk d))

  
  -- beware
  (extractor : VerifKey → (D → Sig) → D → SignKey)
  (extractor-prop
            : ∀ sk (f : D → Sig) d
               (let vk = verifkey sk)
             → Verify vk d (f d) → extractor vk f d ≡ sk)

  where

  module SigH
    (Msg : Set) (H : Msg → D) (E : D → Msg) where
    signH     : Rsign → SignKey → Msg → Sig
    signH r sk msg = sign r sk (H msg)
    VerifyH   : VerifKey → Msg → Sig → Set
    VerifyH vk msg sig = Verify vk (H msg) sig 
    correctH  : ∀ r sk msg → VerifyH (verifkey sk) msg (signH r sk msg)
    correctH r sk msg = correct r sk (H msg)

    extractorH : VerifKey → (Msg → Sig) → Msg → SignKey
    extractorH vk f msg = extractor vk (λ d → f (E d)) (H msg)

    module TrivialH (EH : ∀ m → E (H m) ≡ m) where
        extractorH-prop
                : ∀ sk (f : Msg → Sig) d
                   (let vk = verifkey sk)
                 → VerifyH vk d (f d) → extractorH vk f d ≡ sk
        extractorH-prop sk f d vok = extractor-prop sk (f ∘ E) (H d) (tr (λ z → Verify (verifkey sk) (H d) (f z)) (! EH d) vok)

  module Sig-id where
    open SigH D id id
    open TrivialH (λ _ → refl)

module Signing-data
  (VerifKey SignKey Rsign : Set)
  (verifkey : SignKey → VerifKey)
  where

  module Sig-abs (D : Set) where

    record Sig : Set where
      constructor sign
      field
        rsign   : Rsign
        signkey : SignKey
        d       : D

    Verify : VerifKey → D → Sig → Set
    Verify vk d (sign r sk d') = vk ≡ verifkey sk × d ≡ d'

    correct  : ∀ r sk d → Verify (verifkey sk) d (sign r sk d)
    correct r sk d = refl , refl

    extractor : VerifKey → (D → Sig) → D → SignKey
    extractor vk f d = Sig.signkey (f d)

    module _
      (verifkey-inj : Injective verifkey)
      where
      extractor-prop
                : ∀ sk (f : D → Sig) d
                   (let vk = verifkey sk)
                 → Verify vk d (f d) → extractor vk f d ≡ sk
      extractor-prop sk f d (proj₁ , proj₂) = ! verifkey-inj proj₁

      open Signing verifkey sign Verify correct extractor extractor-prop public

  module SigH-data
    {Msg : Set}
    where

    data D : Set where
      h : Msg → D

    e : D → Msg
    e (h msg) = msg

    open Sig-abs D

    module _
        (verifkey-inj : Injective verifkey)
        where
        open SigH verifkey-inj Msg h e
        open TrivialH (λ m → refl)

module _ {A B C D : Set} (f : A → B) (g : C → D)
         (conflict-pres : Conflict f → Conflict g)
         (_≟_ : Decidable {A = A} _≡_)
         (inj-g : Injective g)
  where
  inj-pres : Injective f
  inj-pres {x} {y} e with x ≟ y
  ... | yes x≡y = x≡y
  ... | no  x≢y = 𝟘-elim (Conflict-¬Injective (conflict-pres (x , y , x≢y , e)) inj-g)

module _ {A B C : Set} (g : B → C) (f : A → B)
         (_≟_ : Decidable {A = B} _≡_) where
  private
    h : A → C
    h = g ∘ f

  conflict-composition : Conflict h → Conflict g ⊎ Conflict f
  conflict-composition (x , y , x≢y , e) with f x ≟ f y
  ... | yes fx≡fy = inr (x , y , x≢y , fx≡fy)
  ... | no  fx≢fy = inl (f x , f y , fx≢fy , e)

  post-inj-pres-conflict : Injective f → Conflict h → Conflict g
  post-inj-pres-conflict f-inj (x , y , x≢y , e) = f x , f y , x≢y ∘ f-inj , e

  -- Therefore all of these constructions preserves conflicts on g:
  --   h(x) = g(k , x)
  --   h(x) = g(k ∷ x)
  --   h(x) = g(k ++ x)
  --   h(x) = g(k ++ x ++ k')
  --   h(x) = g(k ⊕ x)
  --   h(x) = g(x ++ x)
  --   h(x) = g(x , x)

  pre-inj-pres-conflict : Injective g → Conflict h → Conflict f
  pre-inj-pres-conflict g-inj (x , y , x≢y , e) = x , y , x≢y , g-inj e

  -- Therefore all of these constructions preserves conflicts on g:
  --   h(x) = k , g(x)
  --   h(x) = k ∷ g(x)
  --   h(x) = k ++ g(x)
  --   h(x) = k ++ g(x) ++ k'
  --   h(x) = k ⊕ g(x)

-- A construct such as H(H(x)) is a particular case of the conflict-composition
module Self-composition
          {A : Set}
          (h : A → A)
          (_≟_ : Decidable {A = A} _≡_) where
  self-comp-pres-conflict : Conflict (h ∘ h) → Conflict h
  self-comp-pres-conflict c = untag (conflict-composition h h _≟_ c)

module _ {A B : Set} (h : A × A → B) where
  dupP : A → A × A
  dupP x = x , x

  dupP-inj : Injective dupP
  dupP-inj = ap fst

  dupL-inj = dup-inj
  dupV-inj = dup-inj

-- WRONG
{-
module _ {A B C : Set} (f : A → B × C) where
  h = fst ∘ f

  foo : Conflict h → Conflict f
  foo (x , y , i , e) = x , y , i , {!e!}
  -}

record I (B D : Set) : Set where
  field
    h   : List D → D
    i   : B → D
    _⊕_ : D → D → D

data S (B : Set) : Set where
  hˢ   : List (S B) → S B
  iˢ   : B → S B
  _⊕ˢ_ : S B → S B → S B

module TinyEnc {B D : Set} (imp : I B D) where
  open I imp
  enc : (key msg : D) → D
  enc key msg = h (key ∷ []) ⊕ msg
  dec : (key ct : D) → D
  dec = enc

  module _ (⊕-ok : ∀ {x y} → x ⊕ (x ⊕ y) ≡ y) where
    dec-enc : ∀ {key msg} → dec key (enc key msg) ≡ msg
    dec-enc = ⊕-ok

  Msg = D
  CT  = D
  Key = D

  module _ (Rₐ : Set) where 
    Adv = Rₐ → Msg ² × (CT → 𝟚)

    run : 𝟚 → Adv → (Rₐ × Key) → 𝟚
    run β adv (ra , key) = let msgs , k = adv ra in k (enc key (msgs β))

    run' : Adv → (Rₐ × Key × 𝟚) → 𝟚
    run' adv (r , key , β) = run β adv (r , key) == β

    -- Pr[ run 0 adv ] ≈ Pr[ run 1 adv ]

-- Sigma protocol
module _ (Commit ChalQuery ChalResp Res : Set) where
  Verifier = Commit →
            (ChalQuery ×
             ChalResp →
            (Res × 𝟙))

  {-

data Adv (Msg CT : Set) : Set where
  query : (msg : Msg) (k : (ct : CT) → Adv Msg CT) → Adv Msg CT
  chal  : (msgs : Msg ²) (k : (ct : CT) → 𝟚) → Adv Msg CT
open import Data.Tree.Binary
-}

data T (A : Set) : Set where
  empty : T A
  fork  : T A → T A → T A
  leaf  : A → T A

H : Set₁
H = {B : Set} (c : B → B → B)(ε : B) → List B → B

H✓ : H → Set₁
H✓ h = ∀ {B : Set} (c : B → B → B) ε
     → Injective₂ c
     → Conflict (h c ε)
     → Conflict (uncurry c)

module _ {A : Set} {x y : A} {xs ys : List A} where
  ≢∷ : x List.∷ xs ≢ y ∷ ys → x ≢ y ⊎ (x ≡ y × xs ≢ ys)
  ≢∷ = {!!}

  {-
c-inj₂ : ∀ {t u v} → c t u ≡ c t v → u ≡ v
c-inj₂ refl = refl
-}

module Fold where
  h : H
  h = foldr

  module _ {B : Set} (c : B → B → B) ε
           (c-inj : ∀ {x y z} → c x y ≡ c x z → y ≡ z) where
    h✓' : ∀ xs ys(is : xs ≢ ys)(es : h c ε xs ≡ h c ε ys)
          → Conflict (uncurry c)

    h✓' [] [] is es = 𝟘-elim (is refl)
    h✓' [] (x ∷ ys) is es = {!!}
    h✓' (x ∷ xs) [] is es = {!!}
    h✓' (x ∷ xs) (y ∷ ys) is es with ≢∷ is
    ... | inl i = (x , h c ε xs) , (y , h c ε ys) , (λ p → i (ap fst p)) , es
    ... | inr (e , is') = h✓' xs ys is' (c-inj (tr (λ z → c z (h c ε xs) ≡ c y (h c ε ys)) e es))

  h✓ : H✓ h
  h✓ c ε c-inj (xs , ys , is , es) = h✓' c ε c-inj xs ys is es

  {-
_⊕_ : H → H → H
(h₀ ⊕ h₁) c xs = c (h₀ c xs) (h₁ c xs)

Hₚ : H → Set₁
Hₚ h = (Bₚ : H → Set)
       (cₚ : ∀ {h₀ h₁ : H} → Bₚ h₀ → Bₚ h₁ → Bₚ (h₀ ⊕ h₁))
     → Bₚ h

module _ (h : H) (hₚ : Hₚ h) {B : Set} (c : B → B → B)(ε : B) where

  P⊕ : ∀ {h₀ h₁ : H} → P h₀ → P h₁ → P (h₀ ⊕ h₁)
  P⊕ h₀ₚ h₁ₚ ([] , [] , is , es) = 𝟘-elim (is refl)
  P⊕ h₀ₚ h₁ₚ ([] , x ∷ ys , is , es) = {!!}
  P⊕ h₀ₚ h₁ₚ (x ∷ xs , [] , is , es) = {!!}
  P⊕ h₀ₚ h₁ₚ (x ∷ xs , y ∷ ys , is , es) with ≢∷ is
  ... | inl i = x , y , i , {!es!}
  ... | inr i = {!!}

  ph : P h
  ph = hₚ P (λ {x}{y} → P⊕ {x} {y})
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
