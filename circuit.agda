module circuit where

open import Function
open import Data.Nat.NP hiding (_≟_; compare)
open import Data.Bits
open import Data.Bool hiding (_≟_)
open import Data.Product hiding (swap; map)
import Data.Fin.NP as Fin
open Fin using (Fin; zero; suc; inject+; raise; #_)
open import Data.List using (List; []; _∷_)
open import Data.Vec using (Vec; []; _∷_; foldr; _[_]≔_; lookup; _++_; splitAt; tabulate; allFin) renaming (map to vmap)
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Binary.PropositionalEquality

CircuitType : Set₁
CircuitType = (i o : ℕ) → Set

module Rewire where
  RewireFun : CircuitType
  RewireFun i o = Fin o → Fin i

  RewireTbl : CircuitType
  RewireTbl i o = Vec (Fin i) o

  rewire : ∀ {a i o} {A : Set a} → (Fin o → Fin i) → Vec A i → Vec A o
  rewire f v = tabulate (flip lookup v ∘ f)

  rewireTbl : ∀ {a i o} {A : Set a} → RewireTbl i o → Vec A i → Vec A o
  rewireTbl tbl v = vmap (flip lookup v) tbl

  runRewireFun : ∀ {i o} → RewireFun i o → Bits i → Bits o
  runRewireFun = rewire

  runRewireTbl : ∀ {i o} → RewireTbl i o → Bits i → Bits o
  runRewireTbl = rewireTbl

open Rewire using (RewireTbl; RewireFun)

record RewiringBuilder (C : CircuitType) : Set where
  constructor mk

  infixr 1 _>>>_
  infixr 3 _***_

  field
    rewire : ∀ {i o} → RewireFun i o → C i o

    _>>>_  : ∀ {i m o} → C i m → C m o → C i o

    _***_  : ∀ {i₀ i₁ o₀ o₁} → C i₀ o₀ → C i₁ o₁ → C (i₀ + i₁) (o₀ + o₁)

  rewireWithTbl : ∀ {i o} → RewireTbl i o → C i o
  rewireWithTbl = rewire ∘ flip lookup

  idC : ∀ {i} → C i i
  idC = rewire id

  sink : ∀ i → C i 0
  sink _ = rewire (λ())

  dup : ∀ o → C 1 o
  dup _ = rewire (const zero)

  dup₂ : C 1 2
  dup₂ = dup 2

  vcat : ∀ {i o n} → Vec (C i o) n → C (n * i) (n * o)
  vcat []       = idC
  vcat (x ∷ xs) = x *** vcat xs

  coerce : ∀ {i₀ i₁ o₀ o₁} → i₀ ≡ i₁ → o₀ ≡ o₁ → C i₀ o₀ → C i₁ o₁
  coerce refl refl = id

  dupⁿ : ∀ {n} k → C n (k * n)
  dupⁿ {n} k = coerce (proj₂ ℕ°.*-identity n) (ℕ°.*-comm n k) (vcat {n = n} (replicate (dup _)))

  ext-before : ∀ {k i o} → C i o → C (k + i) (k + o)
  ext-before {k} c = idC {k} *** c

  ext-after : ∀ {k i o} → C i o → C (i + k) (o + k)
  ext-after c = c *** idC

  dropC : ∀ {k i o} → C i o → C (k + i) o
  dropC {k} c = sink k *** c

  dropC' : ∀ {k i} → C (k + i) i
  dropC' {k} = dropC {k} idC

  swap : ∀ {i} (x y : Fin i) → C i i
  -- swap x y = arr (λ xs → (xs [ x ]≔ (lookup y xs)) [ y ]≔ (lookup x xs))
  swap x y = rewire (Fin.swap x y)

  rev : ∀ {i} → C i i
  rev = rewire Fin.reverse

  swap₂ : C 2 2
  swap₂ = rev
  -- swap₂ = swap (# 0) (# 1)

  Perm : ℕ → Set
  Perm n = List (Fin n × Fin n)

  perm : ∀ {i} → Perm i → C i i
  perm [] = idC
  perm ((x , y) ∷ π) = swap x y >>> perm π

record CircuitBuilder (C : CircuitType) : Set where
  constructor mk
  field
    isRewiringBuilder : RewiringBuilder C
    arr : ∀ {i o} → (Bits i → Bits o) → C i o

  open RewiringBuilder isRewiringBuilder public

  bit : Bit → C 0 1
  bit b = arr (const (b ∷ []))

  0ʷ : C 0 1
  0ʷ = bit 0b

  1ʷ : C 0 1
  1ʷ = bit 1b

  unOp : (Bit → Bit) → C 1 1
  unOp op = arr (λ { (x ∷ []) → (op x) ∷ [] })

  notC : C 1 1
  notC = unOp not

  binOp : (Bit → Bit → Bit) → C 2 1
  binOp op = arr (λ { (x ∷ y ∷ []) → (op x y) ∷ [] })

  xorC : C 2 1
  xorC = binOp _xor_

  eqC : C 2 1
  eqC = binOp _==ᵇ_

  orC : C 2 1
  orC = binOp _∨_

  andC : C 2 1
  andC = binOp _∧_

  norC : C 2 1
  norC = binOp (λ x y → not (x ∨ y))

  nandC : C 2 1
  nandC = binOp (λ x y → not (x ∧ y))

_→ᵇ_ : CircuitType
i →ᵇ o = Bits i → Bits o

_→ᶠ_ : CircuitType
i →ᶠ o = Fin o → Fin i

finFunRewiringBuilder : RewiringBuilder _→ᶠ_
finFunRewiringBuilder = mk id _∘′_ _***_
  where
    C = _→ᶠ_

    _***_ : ∀ {i₀ i₁ o₀ o₁} → C i₀ o₀ → C i₁ o₁ → C (i₀ + i₁) (o₀ + o₁)
    _***_ {o₀ = o₀} f g x with Fin.cmp o₀ _ x
    _***_      f _ ._ | Fin.bound x = inject+ _ (f x)
    _***_ {i₀} _ g ._ | Fin.free  x = raise i₀ (g x)

tblRewiringBuilder : RewiringBuilder RewireTbl
tblRewiringBuilder = mk tabulate _>>>_ _***_
  where
    open Rewire
    C = RewireTbl

    _>>>_ : ∀ {i m o} → C i m → C m o → C i o
    c₀ >>> c₁ = rewireTbl c₁ c₀
    -- c₀ >>> c₁ = tabulate (flip lookup c₀ ∘ flip lookup c₁)
    -- c₀ >>> c₁ = vmap (flip lookup c₀) c₁

    _***_ : ∀ {i₀ i₁ o₀ o₁} → C i₀ o₀ → C i₁ o₁ → C (i₀ + i₁) (o₀ + o₁)
    _***_ {i₀} c₀ c₁ = vmap (inject+ _) c₀ ++ vmap (raise i₀) c₁

bitsFunRewiringBuilder : RewiringBuilder _→ᵇ_
bitsFunRewiringBuilder = mk Rewire.rewire _>>>_ _***_
  where
    C = _→ᵇ_

    _>>>_ : ∀ {i m o} → C i m → C m o → C i o
    f >>> g = g ∘ f

    _***_ : ∀ {i₀ i₁ o₀ o₁} → C i₀ o₀ → C i₁ o₁ → C (i₀ + i₁) (o₀ + o₁)
    (f *** g) xs with splitAt _ xs
    ... | ys , zs , _ = f ys ++ g zs

bitsFunCircuitBuilder : CircuitBuilder _→ᵇ_
bitsFunCircuitBuilder = mk bitsFunRewiringBuilder id

open import bintree
open import flipbased-tree

TreeBits : CircuitType
TreeBits i o = Tree (Bits o) i

module moretree where
  _>>>_ : ∀ {m n a} {A : Set a} → Tree (Bits m) n → Tree A m → Tree A n
  f >>> g = map (flip bintree.lookup g) f

treeBitsRewiringBuilder : RewiringBuilder TreeBits
treeBitsRewiringBuilder = mk rewire moretree._>>>_ _***_
  where
    C = TreeBits

    rewire : ∀ {i o} → RewireFun i o → C i o
    rewire f = fromFun (Rewire.rewire f)

    _***_ : ∀ {i₀ i₁ o₀ o₁} → C i₀ o₀ → C i₁ o₁ → C (i₀ + i₁) (o₀ + o₁)
    (f *** g) = f >>= λ xs → map (_++_ xs) g

treeBitsCircuitBuilder : CircuitBuilder TreeBits
treeBitsCircuitBuilder = mk treeBitsRewiringBuilder arr
  where
    C = TreeBits

    arr : ∀ {i o} → (Bits i → Bits o) → C i o
    arr = fromFun

RewiringTree : CircuitType
RewiringTree i o = Tree (Fin i) o

module RewiringWith2^Outputs where
    C_⟨2^_⟩ = RewiringTree

    rewire : ∀ {i o} → RewireFun i (2 ^ o) → C i ⟨2^ o ⟩
    rewire f = fromFun (f ∘ toFin)

    lookupFin : ∀ {i o} → C i ⟨2^ o ⟩ → Fin (2 ^ o) → Fin i
    lookupFin c x = bintree.lookup (fromFin x) c

    _>>>_ : ∀ {i m o} → C i ⟨2^ m ⟩ → C (2 ^ m) ⟨2^ o ⟩ → C i ⟨2^ o ⟩
    f >>> g = rewire (lookupFin f ∘ lookupFin g)

    _***_ : ∀ {i₀ i₁ o₀ o₁} → C i₀ ⟨2^ o₀ ⟩ → C i₁ ⟨2^ o₁ ⟩ → C (i₀ + i₁) ⟨2^ (o₀ + o₁) ⟩
    f *** g = f >>= λ x → map (Fin._+′_ x) g

module Test where
  open import Data.Bits.Bits4

  tbl : RewireTbl 4 4
  tbl = # 1 ∷ # 0 ∷ # 2 ∷ # 2 ∷ []

  fun : RewireFun 4 4
  fun zero = # 1
  fun (suc zero) = # 0
  fun (suc (suc zero)) = # 2
  fun (suc (suc (suc x))) = # 2

-- swap x y ≈ swap y x
-- reverse ∘ reverse ≈ id

  abs : ∀ {C} → RewiringBuilder C → C 4 4
  abs builder = swap₂ *** dup₂ *** sink 1
    where open RewiringBuilder builder

  tinytree : Tree (Fin 4) 2
  tinytree = fork (fork (leaf (# 1)) (leaf (# 0))) (fork (leaf (# 2)) (leaf (# 2)))

  bigtree : Tree (Bits 4) 4
  bigtree = fork (fork (fork (same 0000b) (same 0011b)) (fork (same 1000b) (same 1011b)))
                 (fork (fork (same 0100b) (same 0111b)) (fork (same 1100b) (same 1111b)))
    where same : ∀ {n} {A : Set} → A → Tree A (suc n)
          same x = fork (leaf x) (leaf x)

  test₁ : tbl ≡ tabulate fun
  test₁ = refl

  test₂ : tbl ≡ abs tblRewiringBuilder
  test₂ = refl

  test₃ : tabulate fun ≡ tabulate (abs finFunRewiringBuilder)
  test₃ = refl

  test₄ : bigtree ≡ abs treeBitsRewiringBuilder
  test₄ = refl

  open RewiringWith2^Outputs
  test₅ : tabulate (lookupFin tinytree) ≡ tbl
  test₅ = refl
