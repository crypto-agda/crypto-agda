open import Type
open import Function
open import Data.Vec hiding (sum)
import Data.Fin as Fin
open Fin using (Fin; zero; suc)
open import Data.Nat.NP hiding (_≥_)
open import Data.Two hiding (_²; _==_)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Relation.Binary.PropositionalEquality.NP
open import HoTT

module rewind-on-success where

module _ {a} {A : ★_ a} where
    infixr 4 _♦_
    _♦_ : ∀ {n} → Vec A n → (ℕ → A) → (ℕ → A)
    ([]     ♦ f) i = f i
    (x ∷ xs ♦ f) zero    = x
    (x ∷ xs ♦ f) (suc i) = (xs ♦ f) i

    ♦-spec1 : ∀ {n} (xs : Vec A n) (f : ℕ → A) i → (xs ♦ f) (Fin.toℕ i) ≡ lookup i xs
    ♦-spec1 [] f ()
    ♦-spec1 (x ∷ xs) f zero    = refl
    ♦-spec1 (x ∷ xs) f (suc i) = ♦-spec1 xs f i

    ♦-spec2 : ∀ {n} (xs : Vec A n) (f : ℕ → A) i → (xs ♦ f) (n + i) ≡ f i
    ♦-spec2 []       f i = refl
    ♦-spec2 (x ∷ xs) f i = ♦-spec2 xs f i

    takeS : ∀ n (f : ℕ → A) → Vec A n
    takeS zero    f = []
    takeS (suc n) f = f 0 ∷ takeS n (f ∘ suc)

    lookup-takeS : ∀ {n} (f : ℕ → A) i → f (Fin.toℕ i) ≡ lookup i (takeS n f)
    lookup-takeS f zero    = refl
    lookup-takeS f (suc i) = lookup-takeS (f ∘ suc) i

module _
  (Symbol Output : ★)
  (success? : Output → 𝟚)

  (adversaryS : (r : ℕ → Symbol) → ℕ)
  (adversaryO : (r : ℕ → Symbol) → Output)
  where

  Transcript = Vec Symbol

  transcript : (r : ℕ → Symbol) → Transcript (adversaryS r)
  transcript r = takeS (adversaryS r) r

  adversary : (r : ℕ → Symbol) → ℕ × Output
  adversary r = adversaryS r , adversaryO r

  Adversary-spec = ∀ (r s : ℕ → Symbol) → adversary r ≡ adversary (transcript r ♦ s)

  _∧°_ : ∀ {Ω : ★} (f g : Ω → 𝟚) → Ω → 𝟚
  (f ∧° g) x = f x ∧ g x

  infix 2 _↔_
  _↔_ : (A B : ★) → ★
  A ↔ B = (A → B) × (B → A)

  record PartitionV1 (Ω : ★) : ★ where
    field
      B : ℕ → Ω → 𝟚
      B-∃ : ∀ w → ∃ λ i → ✓ (B i w)
      B-! : ∀ i j w → ✓ (B i w) → ✓ (B j w) → i ≡ j

  record Partition (Ω : ★) : ★₁ where
    field
      F      : ℕ → ★
      F-part : Ω ≡ Σ ℕ F

    v1 : PartitionV1 Ω
    v1 = record {B = B; B-∃ = B-∃; B-! = B-!} where
        g : Ω → ℕ
        g = fst ∘ coe F-part

        B : ℕ → Ω → 𝟚
        B i w = i == g w

        B-∃ : ∀ w → ∃ λ i → ✓ (B i w)
        B-∃ w = g w , ==.refl {g w}

        B-! : ∀ i j w → ✓ (B i w) → ✓ (B j w) → i ≡ j
        B-! i j w Biw Bjw = ==.sound i _ Biw ∙ ! ==.sound j _ Bjw

    open PartitionV1 v1 public

  module _ {A : ★}{B : ★}{C : A → B → ★} where
    pair='' : ∀ {x y : Σ A (Σ B ∘ C)}
                (p : fst x ≡ fst y)
                (q : fst (snd x) ≡ fst (snd y))
              → tr (λ x₁ → C x₁ (fst (snd y))) p (tr (C (fst x)) q (snd (snd x))) ≡ snd (snd y) → x ≡ y
    pair='' refl refl = ap (λ x → _ , _ , x)

  ✓-prop : (b : 𝟚)(x y : ✓ b) → x ≡ y
  ✓-prop 1₂ pf pf' = refl
  ✓-prop 0₂ () pf'

  module V1→ {Ω} (v1 : PartitionV1 Ω) {{_ : UA}} where
    open PartitionV1 v1
    open Equivalences
    part : Partition Ω
    part = record { F = F ; F-part = F-part }
      where
        F : ℕ → ★
        F i = Σ Ω λ w → ✓ (B i w)

        Ω→ : Ω → Σ ℕ F
        Ω→ w = fst (B-∃ w) , w , snd (B-∃ w)

        →Ω : Σ ℕ F → Ω
        →Ω (i , w , pf) = w

        Ω→Ω : ∀ w → →Ω (Ω→ w) ≡ w
        Ω→Ω w = refl

        →Ω→ : ∀ x → Ω→ (→Ω x) ≡ x
        →Ω→ (i , w , pf) = pair='' (B-! (fst (B-∃ w)) i w (snd (B-∃ w)) pf) refl (✓-prop (B i w) _ pf)

        F-part : Ω ≡ Σ ℕ F
        F-part = ua (equiv Ω→ →Ω →Ω→ Ω→Ω)

  record ProbTheory : ★₁ where
    field
      ℝ : ★
      0ᵣ 1ᵣ : ℝ
      _·_ _/_ : ℝ → ℝ → ℝ
    _² : ℝ → ℝ
    _² = λ x → x · x
    field
      _≥_ : ℝ → ℝ → ★
      Pr[_] : {Ω : ★}(f : Ω → 𝟚) → ℝ
      Pr≥0 : ∀ {Ω} (f : Ω → 𝟚) → Pr[ f ] ≥ 0ᵣ
      PrΩ≡1 : ∀ {Ω} → Pr[ (λ (_ : Ω) → 1₂) ] ≡ 1ᵣ
      Pr[_∥_] : {Ω : ★}(f g : Ω → 𝟚) → ℝ
      Pr[_∥_]-spec : ∀ {Ω} (f g : Ω → 𝟚) → Pr[ f ∥ g ] ≡ (Pr[ f ∧° g ] / Pr[ g ])
      sum : {A : ★} → (A → ℝ) → ℝ
      {-
      ttt : ∀ {Ω}(f : Ω → 𝟚)
                         (p : Partition Ω)
                       → Pr[ (λ o → {!sum (λ (n : ℕ) → {!Partition.B p n!})!}) ] ≡ sum λ (n : ℕ) → Pr[ Partition.B p n ]
     -}
      law-total-prob : ∀ {Ω}(f : Ω → 𝟚)
                         (p : Partition Ω)
                       → Pr[ f ] ≡ sum λ (n : ℕ) → Pr[ Partition.B p n ] · Pr[ f ∥ Partition.B p n ]
      E[_] : {Ω : ★}(f : Ω → ℝ) → ℝ
    _²' : {Ω : ★}(f : Ω → ℝ) → Ω → ℝ
    _²' = λ f x → (f x)²
    field
      E² : ∀ {Ω} (X : Ω → ℝ) → E[ X ²' ] ≥ E[ X ] ²

  module _
    (adversary-spec : Adversary-spec)

    (process : ∀ {n}(t : Transcript n){n′}(t′ : Transcript n′) → {!!})
    where

    M : (r s : ℕ → Symbol) → {!!}
    M r s = case success? o
              0: {!!}
              1: process t t′
      where
        n = adversaryS r
        o = adversaryO r
        t = transcript r
        #h = {!!}
        h  = takeS #h r
        r′ = h ♦ s
        n′ = adversaryS r′
        o′ = adversaryO r′
        t′ = transcript r′

-- -}
-- -}
-- -}
-- -}
