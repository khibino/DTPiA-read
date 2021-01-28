
-- Exercise 3.1. Natural numbers

open import Tutorial.Nat
open import Tutorial.Bool

data Compare : Nat -> Nat -> Set where
  less : forall {n} k -> Compare n (n + suc k)
  more : forall {n} k -> Compare (n + suc k) n
  same : forall {n} -> Compare n n

-- (a)

compare : (n m : Nat) -> Compare n m
compare zero zero = same
compare (suc n) zero = more n
compare zero (suc m) = less m
compare (suc n) (suc m) with compare n m
... | less k = less k
... | more k = more k
... | same   = same

-- (b)

difference : Nat -> Nat -> Nat
difference n m with compare n m
... | less k = suc k
... | more k = suc k
... | same   = zero

-- Exercise 3.2. Type checking λ-calculus

-- (a)
open import Tutorial.List

data _∈_ {A : Set}(x : A) : List A -> Set where
  hd : forall {xs}   -> x ∈ x :: xs
  tl : forall {y xs} -> x ∈ xs -> x ∈ y :: xs

index : forall {A}{x : A}{xs} -> x ∈ xs -> Nat
index hd     = zero
index (tl p) = suc (index p)

data Lookup {A : Set}(xs : List A) : Nat -> Set where
  inside  : (x : A)(p : x ∈ xs) -> Lookup xs (index p)
  outside : (m : Nat) -> Lookup xs (length xs + m)

_!_ : {A : Set}(xs : List A)(n : Nat) -> Lookup xs n
[] ! n = outside n
(x :: xs) ! zero = inside x hd
(x :: xs) ! suc n with xs ! n
((x :: xs) ! suc .(index p))       | inside y p = inside y (tl p)
((x :: xs) ! suc .(length xs + n)) | outside n  = outside n

infixr 30 _⇒_
data Type : Set where
  ı : Type
  _⇒_ : Type -> Type -> Type

data _≠_ : Type -> Type -> Set where
  neqIA : forall {σ τ} -> ı ≠ (σ ⇒ τ)
  neqAI : forall {σ τ} -> (σ ⇒ τ) ≠ ı
  neqAD : forall {σ₁ τ₁ σ₂ τ₂} -> σ₁ ≠ σ₂ -> (σ₁ ⇒ τ₁) ≠ (σ₂ ⇒ τ₂)
  neqAC : forall {σ₁ τ₁ σ₂ τ₂} -> τ₁ ≠ τ₂ -> (σ₁ ⇒ τ₁) ≠ (σ₂ ⇒ τ₂)

data Equal? : Type -> Type -> Set where
  yes : forall {τ} -> Equal? τ τ
  no  : forall {σ τ} -> σ ≠ τ -> Equal? σ τ

_=?=_ : (σ τ : Type) -> Equal? σ τ
ı =?= ı = yes
ı =?= (τ₁ ⇒ τ₂) = no neqIA
(σ₁ ⇒ σ₂) =?= ı = no neqAI
(σ₁ ⇒ σ₂) =?= (τ₁ ⇒ τ₂) with σ₁ =?= τ₁
(σ₁ ⇒ σ₂) =?= (τ₁ ⇒ τ₂) | no n = no (neqAD n)
(σ₁ ⇒ σ₂) =?= (τ₁ ⇒ τ₂) | yes with σ₂ =?= τ₂
... | no n = no (neqAC n)
... | yes  = yes

-- (b)

infixl 80 _$_
data Raw : Set where
  var : Nat -> Raw
  _$_ : Raw -> Raw -> Raw
  lam : Type -> Raw -> Raw

Cxt = List Type

data Term (Γ : Cxt) : Type -> Set where
  var : forall {τ} -> τ ∈ Γ -> Term Γ τ
  _$_ : forall {σ τ} -> Term Γ (σ ⇒ τ) -> Term Γ σ -> Term Γ τ
  lam : forall σ {τ} -> Term (σ :: Γ) τ -> Term Γ (σ ⇒ τ)

erase : forall {Γ τ} -> Term Γ τ -> Raw
erase (var x)    = var (index x)
erase (t $ u)    = erase t $ erase u
erase (lam σ t) = lam σ (erase t)

data BadTerm (Γ : Cxt) : Set where
  var : Nat -> BadTerm Γ
  _$₁_ : BadTerm Γ -> Raw -> BadTerm Γ
  _$ı_ : Term Γ ı -> Raw -> BadTerm Γ
  _$₂_ : forall {σ τ} -> Term Γ (σ ⇒ τ) -> BadTerm Γ -> BadTerm Γ
  _$_  : forall {σ τ σ'} -> Term Γ (σ ⇒ τ) -> Term Γ σ' -> BadTerm Γ
  lam : forall σ -> BadTerm (σ :: Γ) -> BadTerm Γ

eraseBad : {Γ : Cxt} -> BadTerm Γ -> Raw
eraseBad (var n) = var n
eraseBad (b₁ $₁ r₂) = eraseBad b₁ $ r₂
eraseBad (tı $ı r₂) = erase tı $ r₂
eraseBad (t₁ $₂ b₂) = erase t₁ $ eraseBad b₂
eraseBad (t₁ $ t₂)  = erase t₁ $ erase t₂
eraseBad (lam σ b) = lam σ (eraseBad b)

data Infer (Γ : Cxt) : Raw -> Set where
  ok  : (τ : Type)(t : Term Γ τ) -> Infer Γ (erase t)
  bad : (b : BadTerm Γ) -> Infer Γ (eraseBad b)

infer : (Γ : Cxt)(e : Raw) -> Infer Γ e
--
infer Γ (var n) with Γ ! n
infer Γ (var .(length Γ + n)) | outside n = bad (var (length Γ + n))
infer Γ (var .(index p)) | inside σ p = ok σ (var p)
--
infer Γ (e₁ $ e₂) with infer Γ e₁
infer Γ (.(eraseBad b₁) $ e₂) | bad b₁ = bad (b₁ $₁ e₂)
infer Γ (.(erase t₁) $ e₂) | ok ı t₁ = bad (t₁ $ı e₂)
infer Γ (.(erase t₁) $ e₂) | ok (σ ⇒ τ) t₁ with infer Γ e₂
infer Γ (.(erase t₁) $ .(eraseBad b₂)) | ok (σ ⇒ τ) t₁ | bad b₂ = bad (t₁ $₂ b₂)
infer Γ (.(erase t₁) $ .(erase t₂)) | ok (σ ⇒ τ) t₁ | ok σ' t₂ with σ =?= σ'
infer Γ (.(erase t₁) $ .(erase t₂)) | ok (σ ⇒ τ) t₁ | ok .σ t₂ | yes   = ok τ (t₁ $ t₂)
infer Γ (.(erase t₁) $ .(erase t₂)) | ok (σ ⇒ τ) t₁ | ok σ' t₂ | no ne = bad (t₁ $ t₂)
--
infer Γ (lam σ e) with infer (σ :: Γ) e
infer Γ (lam σ .(erase t))    | ok τ t = ok (σ ⇒ τ) (lam σ t)
infer Γ (lam σ .(eraseBad b)) | bad b   = bad (lam σ b)

-- Exercise 3.3. Properties of list functions

infixr 30 _::_
data All {A : Set}(P : A -> Set) : List A -> Set where
  []   : All P []
  _::_ : forall {x xs} -> P x -> All P xs -> All P (x :: xs)

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

data Inspect {A : Set}(x : A) : Set where
  it : (y : A) -> x == y -> Inspect x

inspect : {A : Set}(x : A) -> Inspect x
inspect x = it x refl

trueIsTrue : {x : Bool} -> x == true -> isTrue x
trueIsTrue refl = _

-- (a)

lemma-All-∈ : forall {A x xs}{P : A -> Set} ->
               All P xs -> x ∈ xs -> P x
lemma-All-∈ (px :: pxs) hd     = px
lemma-All-∈ (px :: pxs) (tl e) = lemma-All-∈ pxs e

-- (b)

lem-filter-sound : {A : Set}(p : A -> Bool)(xs : List A) ->
                   All (satisfies p) (filter p xs)
lem-filter-sound p []        = []
lem-filter-sound p (x :: xs) with inspect (p x)
lem-filter-sound p (x :: xs) | it y prf with p x | prf
lem-filter-sound p (x :: xs) | it .true prf  | true  | refl =
  trueIsTrue prf :: lem-filter-sound p xs
lem-filter-sound p (x :: xs) | it .false prf | false | refl =
  lem-filter-sound p xs

-- (c)

lem-filter-complete : {A : Set}(p : A -> Bool)(x : A){xs : List A} ->
                      x ∈ xs -> satisfies p x -> x ∈ filter p xs
lem-filter-complete p x hd px with p x
lem-filter-complete p x hd px | true = hd
lem-filter-complete p x (tl {y} el) px with p y
lem-filter-complete p x (tl {_} el) px | true  = tl (lem-filter-complete p x el px)
lem-filter-complete p x (tl {_} el) px | false = lem-filter-complete p x el px
