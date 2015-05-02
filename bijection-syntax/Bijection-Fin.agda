-- NOTE with-K
module bijection-syntax.Bijection-Fin where

  open import Type

  open import bijection-syntax.Bijection
  open import Function.NP hiding (Cmp)
  open import Relation.Binary.PropositionalEquality.NP

  open import Data.Empty
  open import Data.Nat.NP hiding (suc-injective)
  open import Data.Two
  open import Data.Fin.NP
    using ( Fin ; zero ; suc ; ℕ▹Fin ; inject₁; suc-injective; _≤F_; z≤i; s≤s
          ; module From-mono-inj )
  open import Data.Vec hiding ([_])
  open import Data.Sum

  data `Syn : ℕ → Type where
    `id   : ∀ {n} → `Syn n
    `swap : ∀ {n} → `Syn (2 + n)
    `tail : ∀ {n} → `Syn n → `Syn (1 + n)
    _`∘_  : ∀ {n} → `Syn n → `Syn n → `Syn n

  `Rep = Fin

  `Ix = ℕ

  `Tree : Type → `Ix → Type
  `Tree X = Vec X

  `fromFun : ∀ {i X} → (`Rep i → X) → `Tree X i
  `fromFun = tabulate

  `toFun : ∀ {i X} → `Tree X i → (`Rep i → X)
  `toFun T zero    = head T
  `toFun T (suc i) = `toFun (tail T) i

  `toFun∘fromFun : ∀ {i X}(f : `Rep i → X) → f ≗ `toFun (`fromFun f)
  `toFun∘fromFun f zero = refl
  `toFun∘fromFun f (suc i) = `toFun∘fromFun (f ∘ suc) i

  fin-swap : ∀ {n} → Endo (Fin (2 + n))
  fin-swap zero = suc zero
  fin-swap (suc zero) = zero
  fin-swap (suc (suc i)) = suc (suc i)

  fin-tail : ∀ {n} → Endo (Fin n) → Endo (Fin (1 + n))
  fin-tail f zero = zero
  fin-tail f (suc i) = suc (f i)

  `evalArg : ∀ {i} → `Syn i → Endo (`Rep i)
  `evalArg `id       = id
  `evalArg `swap     = fin-swap
  `evalArg (`tail f) = fin-tail (`evalArg f)
  `evalArg (S `∘ S₁) = `evalArg S ∘ `evalArg S₁

  vec-swap : ∀ {n}{X : Type} → Endo (Vec X (2 + n))
  vec-swap xs = head (tail xs) ∷ head xs ∷ tail (tail xs)

  vec-tail : ∀ {n}{X : Type} → Endo (Vec X n) → Endo (Vec X (1 + n))
  vec-tail f xs = head xs ∷ f (tail xs)

  `evalTree : ∀ {i X} → `Syn i → Endo (`Tree X i)
  `evalTree `id       = id
  `evalTree `swap     = vec-swap
  `evalTree (`tail f) = vec-tail (`evalTree f)
  `evalTree (S `∘ S₁) = `evalTree S ∘ `evalTree S₁

  `eval-proof : ∀ {i X} S (T : `Tree X i) → `toFun T ≗ `toFun (`evalTree S T) ∘ `evalArg S
  `eval-proof `id       T i = refl
  `eval-proof `swap T zero = refl
  `eval-proof `swap T (suc zero) = refl
  `eval-proof `swap T (suc (suc i)) = refl
  `eval-proof (`tail S) T zero = refl
  `eval-proof (`tail S) T (suc i) = `eval-proof S (tail T) i
  `eval-proof (S `∘ S₁) T i rewrite
    `eval-proof S₁ T i |
    `eval-proof S (`evalTree S₁ T) (`evalArg S₁ i) = refl

  `inv : ∀ {i} → Endo (`Syn i)
  `inv `id       = `id
  `inv `swap     = `swap
  `inv (`tail S) = `tail (`inv S)
  `inv (S `∘ S₁) = `inv S₁ `∘ `inv S

  `inv-proof : ∀ {i} → (S : `Syn i) → `evalArg S ∘ `evalArg (`inv S) ≗ id
  `inv-proof `id x       = refl
  `inv-proof `swap zero          = refl
  `inv-proof `swap (suc zero)    = refl
  `inv-proof `swap (suc (suc x)) = refl
  `inv-proof (`tail S) zero = refl
  `inv-proof (`tail S) (suc x) rewrite `inv-proof S x = refl
  `inv-proof (S `∘ S₁) x rewrite 
    `inv-proof S₁ (`evalArg (`inv S) x) |
    `inv-proof S x = refl

  `RC : ∀ {i} → Cmp (`Rep i)
  `RC zero zero = eq
  `RC zero (suc j) = lt
  `RC (suc i) zero = gt
  `RC (suc i) (suc j) = `RC i j

  insert : ∀ {n X} → Cmp X → X → Vec X n → Vec X (1 + n)
  insert X-cmp x [] = x ∷ []
  insert X-cmp x (x₁ ∷ xs) with X-cmp x x₁
  insert X-cmp x (x₁ ∷ xs) | lt = x ∷ x₁ ∷ xs
  insert X-cmp x (x₁ ∷ xs) | eq = x ∷ x₁ ∷ xs
  insert X-cmp x (x₁ ∷ xs) | gt = x₁ ∷ insert X-cmp x xs

  `sort : ∀ {i X} → Cmp X → Endo (`Tree X i)
  `sort X-cmp [] = []
  `sort X-cmp (x ∷ xs) = insert X-cmp x (`sort X-cmp xs)

  insert-syn : ∀ {n X} → Cmp X → X → Vec X n → `Syn (1 + n)
  insert-syn X-cmp x [] = `id
  insert-syn X-cmp x (x₁ ∷ xs) with X-cmp x x₁
  insert-syn X-cmp x (x₁ ∷ xs) | lt = `id
  insert-syn X-cmp x (x₁ ∷ xs) | eq = `id
  insert-syn X-cmp x (x₁ ∷ xs) | gt = `tail (insert-syn X-cmp x xs) `∘ `swap

  `sort-syn : ∀ {i X} → Cmp X → `Tree X i → `Syn i
  `sort-syn X-cmp []       = `id
  `sort-syn X-cmp (x ∷ xs) = insert-syn X-cmp x (`sort X-cmp xs) `∘ `tail (`sort-syn X-cmp xs)

  insert-proof : ∀ {n X}(X-cmp : Cmp X) x (T : Vec X n) → insert X-cmp x T ≡ `evalTree (insert-syn X-cmp x T) (x ∷ T)
  insert-proof X-cmp x [] = refl
  insert-proof X-cmp x (x₁ ∷ T) with X-cmp x x₁
  insert-proof X-cmp x (x₁ ∷ T) | lt = refl
  insert-proof X-cmp x (x₁ ∷ T) | eq = refl
  insert-proof X-cmp x (x₁ ∷ T) | gt rewrite insert-proof X-cmp x T = refl

  `sort-proof : ∀ {i X}(X-cmp : Cmp X)(T : `Tree X i) → `sort X-cmp T ≡ `evalTree (`sort-syn X-cmp T) T
  `sort-proof X-cmp [] = refl
  `sort-proof X-cmp (x ∷ T) rewrite 
    ! `sort-proof X-cmp T = insert-proof X-cmp x (`sort X-cmp T)

  module Alt-Syn where

    data ``Syn : ℕ → Type where
      `id : ∀ {n} → ``Syn n
      _`∘_ : ∀ {n} → ``Syn n → ``Syn n → ``Syn n
      `swap : ∀ {n} m → ``Syn (m + 2 + n)

    swap-fin : ∀ {n} m → Endo (Fin (m + 2 + n))
    swap-fin zero zero = suc zero
    swap-fin zero (suc zero) = zero
    swap-fin zero (suc (suc i)) = suc (suc i)
    swap-fin (suc m) zero = zero
    swap-fin (suc m) (suc i) = suc (swap-fin m i)

    ``evalArg : ∀ {n} → ``Syn n → Endo (`Rep n)
    ``evalArg `id       = id
    ``evalArg (S `∘ S₁) = ``evalArg S ∘ ``evalArg S₁
    ``evalArg (`swap m) = swap-fin m

    _``∘_ : ∀ {n} → ``Syn n → ``Syn n → ``Syn n
    `id ``∘ y = y
    (x `∘ x₁) ``∘ `id = x `∘ x₁
    (x `∘ x₁) ``∘ (y `∘ y₁) = x `∘ (x₁ `∘ (y `∘ y₁))
    (x `∘ x₁) ``∘ `swap m = x `∘ (x₁ ``∘ `swap m)
    `swap m ``∘ y = `swap m `∘ y

    ``tail : ∀ {n} → ``Syn n → ``Syn (suc n)
    ``tail `id = `id
    ``tail (S `∘ S₁) = ``tail S ``∘ ``tail S₁
    ``tail (`swap m) = `swap (suc m)

    translate : ∀ {n} → `Syn n → ``Syn n
    translate `id = `id
    translate `swap = `swap 0
    translate (`tail S) = ``tail (translate S)
    translate (S `∘ S₁) = translate S ``∘ translate S₁

    ``∘-p : ∀ {n}(A B : ``Syn n) → ``evalArg (A ``∘ B) ≗ ``evalArg (A `∘ B)
    ``∘-p `id B x = refl
    ``∘-p (A `∘ A₁) `id x = refl
    ``∘-p (A `∘ A₁) (B `∘ B₁) x = refl
    ``∘-p (A `∘ A₁) (`swap m) x rewrite ``∘-p A₁ (`swap m) x = refl
    ``∘-p (`swap m) B x = refl

    ``tail-p : ∀ {n} (S : ``Syn n) → fin-tail (``evalArg S) ≗ ``evalArg (``tail S)
    ``tail-p `id zero = refl
    ``tail-p `id (suc x) = refl
    ``tail-p (S `∘ S₁) zero rewrite ``∘-p (``tail S) (``tail S₁) zero
                                  | ! ``tail-p S₁ zero = ``tail-p S zero
    ``tail-p (S `∘ S₁) (suc x) rewrite ``∘-p (``tail S) (``tail S₁) (suc x)
                                     | ! ``tail-p S₁ (suc x) = ``tail-p S (suc (``evalArg S₁ x))
    ``tail-p (`swap m) zero = refl
    ``tail-p (`swap m) (suc x) = refl

    `eval`` : ∀ {n} (S : `Syn n) → `evalArg S ≗ ``evalArg (translate S)
    `eval`` `id       x = refl
    `eval`` `swap zero = refl
    `eval`` `swap (suc zero) = refl
    `eval`` `swap (suc (suc x)) = refl
    `eval`` (`tail S) zero = ``tail-p (translate S) zero
    `eval`` (`tail S) (suc x) rewrite `eval`` S x = ``tail-p (translate S) (suc x)
    `eval`` (S `∘ S₁) x rewrite ``∘-p (translate S) (translate S₁) x | ! `eval`` S₁ x | `eval`` S (`evalArg S₁ x) = refl


  data Fin-View : ∀ {n} → Fin n → Type where
    max : ∀ {n} → Fin-View (ℕ▹Fin n)
    inject : ∀ {n} → (i : Fin n) → Fin-View (inject₁ i)

  data Sorted {X}(XC : Cmp X) : ∀ {l} → Vec X l  → Type where
    []  : Sorted XC []
    sing : ∀ x → Sorted XC (x ∷ [])
    dbl-lt  : ∀ {l} x y {xs : Vec X l} → lt ≡ XC x y → Sorted XC (y ∷ xs) → Sorted XC (x ∷ y ∷ xs)
    dbl-eq  : ∀ {l} x {xs : Vec X l} → Sorted XC (x ∷ xs) → Sorted XC (x ∷ x ∷ xs)

  opposite : Ord → Ord
  opposite lt = gt
  opposite eq = eq
  opposite gt = lt

  flip-RC : ∀ {n}(x y : Fin n) → opposite (`RC x y) ≡ `RC y x
  flip-RC zero zero = refl
  flip-RC zero (suc y) = refl
  flip-RC (suc x) zero = refl
  flip-RC (suc x) (suc y) = flip-RC x y

  eq=>≡ : ∀ {i} (x y : Fin i) → eq ≡ `RC x y → x ≡ y
  eq=>≡ zero zero p = refl
  eq=>≡ zero (suc y) ()
  eq=>≡ (suc x) zero ()
  eq=>≡ (suc x) (suc y) p rewrite eq=>≡ x y p = refl

  insert-Sorted : ∀ {n l}{V : Vec (Fin n) l}(x : Fin n) → Sorted {Fin n} `RC V → Sorted {Fin n} `RC (insert `RC x V)
  insert-Sorted x [] = sing x
  insert-Sorted x (sing x₁) with `RC x x₁ | dbl-lt {XC = `RC} x x₁ {[]} | eq=>≡ x x₁ | flip-RC x x₁
  insert-Sorted x (sing x₁) | lt | b | _ | _ = b refl (sing x₁)
  insert-Sorted x (sing x₁) | eq | _ | p | _ rewrite p refl = dbl-eq x₁ (sing x₁)
  insert-Sorted x (sing x₁) | gt | b | _ | l = dbl-lt x₁ x l (sing x)
  insert-Sorted x (dbl-lt y y' {xs} prf xs₁) with `RC x y | dbl-lt {XC = `RC} x y {y' ∷ xs} | eq=>≡ x y | flip-RC x y
  insert-Sorted x (dbl-lt y y' prf xs₁) | lt | b | p | l₁ = b refl (dbl-lt y y' prf xs₁)
  insert-Sorted x (dbl-lt y y' prf xs₁) | eq | b | p | l₁ rewrite p refl = dbl-eq y (dbl-lt y y' prf xs₁)
  insert-Sorted x (dbl-lt y y' {xs} prf xs₁) | gt | b | p | l₁ with `RC x y' | insert-Sorted x xs₁
  insert-Sorted x (dbl-lt y y' prf xs₁) | gt | b | p | l₁ | lt | xs' = dbl-lt y x l₁ xs'
  insert-Sorted x (dbl-lt y y' prf xs₁) | gt | b | p | l₁ | eq | xs' = dbl-lt y x l₁ xs'
  insert-Sorted x (dbl-lt y y' prf xs₁) | gt | b | p | l₁ | gt | xs' = dbl-lt y y' prf xs'
  insert-Sorted x (dbl-eq y {xs} xs₁) with `RC x y | inspect (`RC x) y | dbl-lt {XC = `RC} x y {y ∷ xs} | eq=>≡ x y | flip-RC x y | insert-Sorted x xs₁
  insert-Sorted x (dbl-eq y xs₁) | lt | _ | b | p | l | _ = b refl (dbl-eq y xs₁)
  insert-Sorted x (dbl-eq y xs₁) | eq | _ | b | p | l | _ rewrite p refl = dbl-eq y (dbl-eq y xs₁)
  insert-Sorted x (dbl-eq y xs₁) | gt | [ prf ] | b | p | l | ss  rewrite prf = dbl-eq y ss 

  sort-Sorted : ∀ {n l}(V : Vec (Fin n) l) → Sorted `RC (`sort `RC V)
  sort-Sorted [] = []
  sort-Sorted (x ∷ V) = insert-Sorted x (sort-Sorted V)

  RC-refl : ∀ {i}(x : Fin i) → `RC x x ≡ eq
  RC-refl zero = refl
  RC-refl (suc x) = RC-refl x

  STail : ∀ {X l}{XC : Cmp X}{xs : Vec X (suc l)} → Sorted XC xs → Sorted XC (tail xs)
  STail (sing x) = []
  STail (dbl-lt x y x₁ T) = T
  STail (dbl-eq x T) = T

  module sproof {X}(XC : Cmp X)(XC-refl : ∀ x → XC x x ≡ eq)
     (eq≡ : ∀ x y → XC x y ≡ eq → x ≡ y)
     (lt-trans : ∀ x y z → XC x y ≡ lt → XC y z ≡ lt → XC x z ≡ lt)
     (XC-flip : ∀ x y → opposite (XC x y) ≡ XC y x)
     where

    open import Data.Sum

    _≤X_ : X → X → Type
    x ≤X y = XC x y ≡ lt ⊎ XC x y ≡ eq

    ≤X-trans : ∀ {x y z} → x ≤X y → y ≤X z → x ≤X z
    ≤X-trans (inj₁ x₁) (inj₁ x₂) = inj₁ (lt-trans _ _ _ x₁ x₂)
    ≤X-trans {_}{y}{z}(inj₁ x₁) (inj₂ y₁) rewrite eq≡ y z y₁ = inj₁ x₁
    ≤X-trans {x}{y} (inj₂ y₁) y≤z rewrite eq≡ x y y₁ = y≤z

    h≤t : ∀ {n}{T : `Tree X (2 + n)} → Sorted XC T → head T ≤X head (tail T)
    h≤t (dbl-lt x y x₁ ST) = inj₁ (! x₁)
    h≤t (dbl-eq x ST) rewrite XC-refl x = inj₂ refl

    head-p : ∀ {n}{T : `Tree X (suc n)} i → Sorted XC T → head T ≤X `toFun T i
    head-p {T = T} zero ST rewrite XC-refl (head T) = inj₂ refl
    head-p {zero} (suc ()) ST
    head-p {suc n} (suc i) ST = ≤X-trans (h≤t ST) (head-p i (STail ST))

    toFun-p : ∀ {n}{T : `Tree X n}{i j : Fin n} → i ≤F j → Sorted XC T → `toFun T i ≤X `toFun T j
    toFun-p {j = j} z≤i ST = head-p j ST
    toFun-p (s≤s i≤Fj) ST = toFun-p i≤Fj (STail ST)

    sort-proof : ∀ {i}{T : `Tree X i} → Sorted XC T → Is-Mono `RC XC (`toFun T)
    sort-proof {T = T} T₁ zero zero rewrite XC-refl (head T) = _
    sort-proof T₁ zero (suc y) with toFun-p (z≤i {i = suc y}) T₁
    sort-proof T zero (suc y) | inj₁ x rewrite x = _
    sort-proof T zero (suc y) | inj₂ y₁ rewrite y₁ = _
    sort-proof {T = T} T₁ (suc x) zero with toFun-p (z≤i {i = suc x}) T₁ | XC-flip (head T) (`toFun (tail T) x)
    sort-proof T (suc x) zero | inj₁ x₁ | l rewrite x₁ | ! l = _
    sort-proof T (suc x) zero | inj₂ y | l rewrite y | ! l = _
    sort-proof T₁ (suc x) (suc y) = sort-proof (STail T₁) x y

  lt-trans-RC : ∀ {i} (x y z : Fin i) → `RC x y ≡ lt → `RC y z ≡ lt → `RC x z ≡ lt
  lt-trans-RC zero zero zero x<y y<z = y<z
  lt-trans-RC zero zero (suc z) x<y y<z = refl
  lt-trans-RC zero (suc y) zero x<y ()
  lt-trans-RC zero (suc y) (suc z) x<y y<z = refl
  lt-trans-RC (suc x) zero zero x<y y<z = x<y
  lt-trans-RC (suc x) zero (suc z) () y<z
  lt-trans-RC (suc x) (suc y) zero x<y y<z = y<z
  lt-trans-RC (suc x) (suc y) (suc z) x<y y<z = lt-trans-RC x y z x<y y<z

  `sort-mono : ∀ {i}(T : `Tree (`Rep i) i) → Is-Mono `RC `RC (`toFun (`sort `RC T))
  `sort-mono T x y = sproof.sort-proof `RC RC-refl (λ x₁ y₁ x₂ → eq=>≡ x₁ y₁ (! x₂)) lt-trans-RC flip-RC (sort-Sorted T) x y

  move-to-RC : ∀ {n}{x y : Fin n} → x ≤F y → `RC x y ≡ lt ⊎ `RC x y ≡ eq
  move-to-RC {y = zero} z≤i = inj₂ refl
  move-to-RC {y = suc y} z≤i = inj₁ refl
  move-to-RC (s≤s x≤Fy) = move-to-RC x≤Fy

  move-from-RC : ∀ {n}(x y : Fin n) → lt ≡ `RC x y ⊎ eq ≡ `RC x y → x ≤F y
  move-from-RC zero zero prf = z≤i
  move-from-RC zero (suc y) prf = z≤i
  move-from-RC (suc x) zero (inj₁ ())
  move-from-RC (suc x) zero (inj₂ ())
  move-from-RC (suc x) (suc y) prf = s≤s (move-from-RC x y prf)

  module toNatRC n (f : Endo (Fin (suc n)))(f-inj : Is-Inj f)(f-mono : Is-Mono `RC `RC f) where
    proper-mono : ∀ {x y} → x ≤F y → f x ≤F f y
    proper-mono {x} {y} x≤Fy with `RC x y | `RC (f x) (f y) | move-to-RC x≤Fy | f-mono x y | move-from-RC (f x) (f y)
    proper-mono x≤Fy | .lt | lt | inj₁ refl | r4 | r5 = r5 (inj₁ refl)
    proper-mono x≤Fy | .lt | eq | inj₁ refl | r4 | r5 = r5 (inj₂ refl)
    proper-mono x≤Fy | .lt | gt | inj₁ refl | () | r5
    proper-mono x≤Fy | .eq | lt | inj₂ refl | () | r5
    proper-mono x≤Fy | .eq | eq | inj₂ refl | r4 | r5 = r5 (inj₂ refl)
    proper-mono x≤Fy | .eq | gt | inj₂ refl | () | r5
    open From-mono-inj f f-inj proper-mono public

  fin-view : ∀ {n} → (i : Fin (suc n)) → Fin-View i
  fin-view {zero} zero = max
  fin-view {zero} (suc ())
  fin-view {suc n} zero = inject _
  fin-view {suc n} (suc i) with fin-view i
  fin-view {suc n} (suc .(ℕ▹Fin n)) | max = max
  fin-view {suc n} (suc .(inject₁ i)) | inject i = inject _

  absurd : {X : Type} → .⊥ → X
  absurd ()

  drop₁ : ∀ {n} → (i : Fin (suc n)) → .(i ≢ ℕ▹Fin n) → Fin n
  drop₁ i neq with fin-view i
  drop₁ {n} .(ℕ▹Fin n) neq | max = absurd (neq refl)
  drop₁ .(inject₁ i) neq | inject i = i

  drop₁→inject₁ : ∀ {n}(i : Fin (suc n))(j : Fin n).(p : i ≢ ℕ▹Fin n) → drop₁ i p ≡ j → i ≡ inject₁ j
  drop₁→inject₁ i j p q with fin-view i
  drop₁→inject₁ {n} .(ℕ▹Fin n) j p q | max = absurd (p refl)
  drop₁→inject₁ .(inject₁ i) j p q | inject i = ap inject₁ q


  `mono-inj→id : ∀{i}(f : Endo (`Rep i)) → Is-Inj f → Is-Mono `RC `RC f → f ≗ id
  `mono-inj→id {zero}  = λ f x x₁ ()
  `mono-inj→id {suc i} = toNatRC.f≗id i


  interface : Interface
  interface = record 
    { Ix            = `Ix
    ; Rep           = `Rep
    ; Syn           = `Syn
    ; Tree          = `Tree
    ; fromFun       = `fromFun
    ; toFun         = `toFun
    ; toFun∘fromFun = `toFun∘fromFun
    ; evalArg       = `evalArg
    ; evalTree      = `evalTree
    ; eval-proof    = `eval-proof
    ; inv           = `inv
    ; inv-proof     = `inv-proof
    ; RC            = `RC
    ; sort          = `sort
    ; sort-syn      = `sort-syn
    ; sort-proof    = `sort-proof
    ; sort-mono     = `sort-mono
    ; mono-inj→id   = `mono-inj→id
    }

  count : ∀ {n} → (Fin n → ℕ) → ℕ
  count {n} f = sum (tabulate f)

  count-ext : ∀ {n} → (f g : Fin n → ℕ) → f ≗ g → count f ≡ count g
  count-ext {zero} f g f≗g = refl
  count-ext {suc n} f g f≗g rewrite f≗g zero | count-ext (f ∘ suc) (g ∘ suc) (f≗g ∘ suc) = refl

  #⟨_⟩ : ∀ {n} → (Fin n → 𝟚) → ℕ
  #⟨ f ⟩ = count (𝟚▹ℕ ∘ f)

  #-ext : ∀ {n} → (f g : Fin n → 𝟚) → f ≗ g → #⟨ f ⟩ ≡ #⟨ g ⟩
  #-ext f g f≗g = count-ext (𝟚▹ℕ ∘ f) (𝟚▹ℕ ∘ g) (ap 𝟚▹ℕ ∘ f≗g)

  com-assoc : ∀ x y z → x + (y + z) ≡ y + (x + z)
  com-assoc x y z rewrite 
    ! ℕ°.+-assoc x y z |
    ℕ°.+-comm x y      |
    ℕ°.+-assoc y x z   = refl
    
  syn-pres : ∀ {n}(f : Fin n → ℕ)(S : `Syn n)
           → count f ≡ count (f ∘ `evalArg S)
  syn-pres f `id = refl
  syn-pres f `swap = com-assoc (f zero) (f (suc zero)) (count (λ i → f (suc (suc i))))
  syn-pres f (`tail S) rewrite syn-pres (f ∘ suc) S = refl
  syn-pres f (S `∘ S₁) rewrite syn-pres f S = syn-pres (f ∘ `evalArg S) S₁

  count-perm : ∀ {n}(f : Fin n → ℕ)(p : Endo (Fin n)) → Is-Inj p
         → count f ≡ count (f ∘ p)
  count-perm f p p-inj = trans (syn-pres f (sort-bij p)) (count-ext _ _ f∘eval≗f∘p)
   where
     open abs interface
     f∘eval≗f∘p : f ∘ `evalArg (sort-bij p) ≗ f ∘ p
     f∘eval≗f∘p x rewrite thm p p-inj x = refl


  #-perm : ∀ {n}(f : Fin n → 𝟚)(p : Endo (Fin n)) → Is-Inj p
         → #⟨ f ⟩ ≡ #⟨ f ∘ p ⟩
  #-perm f p p-inj = count-perm (𝟚▹ℕ ∘ f) p p-inj

  test : `Syn 8
  test = abs.sort-bij interface (λ x → `evalArg (`tail `swap) x)
-- -}
