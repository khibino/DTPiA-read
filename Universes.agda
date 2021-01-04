-- 3.2 Universes

module Universes where

-- A familiar universe

data   False : Set where
record True  : Set where

data Bool : Set where
  true  : Bool
  false : Bool

isTrue : Bool -> Set
isTrue true  = True
isTrue false = False

infix  30 not_
infixr 25 _and_

not_ : Bool -> Bool
not true  = false
not false = true

_and_ : Bool -> Bool -> Bool
true  and x = x
false and _ = false

notNotId : (a : Bool) -> isTrue (not not a) -> isTrue a
notNotId true  p = p
notNotId false ()

andIntro : (a b : Bool) -> isTrue a -> isTrue b -> isTrue (a and b)
andIntro true  _ _  p = p
andIntro false _ () _

open import Tutorial.Nat

nonZero : Nat -> Bool
nonZero zero    = false
nonZero (suc _) = true

postulate _div_ : Nat -> (m : Nat){p : isTrue (nonZero m)} -> Nat

three = 16 div 5

-- Universes for generic programming

data Functor : Set1 where
  |Id|  : Functor
  |K|   : Set -> Functor
  _|+|_ : Functor -> Functor -> Functor
  _|x|_ : Functor -> Functor -> Functor

data _⨁_ (A B : Set) : Set where
  inl : A -> A ⨁ B
  inr : B -> A ⨁ B

data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B

infixr 50 _|+|_ _⨁_
infixr 60 _|x|_ _×_

[_] : Functor -> Set -> Set
[ |Id|    ] X = X
[ |K| A   ] X = A
[ F |+| G ] X = [ F ] X ⨁ [ G ] X
[ F |x| G ] X = [ F ] X × [ G ] X

map : (F : Functor){X Y : Set} -> (X -> Y) -> [ F ] X -> [ F ] Y
map |Id|      f x       = f x
map (|K| A)   f c       = c
map (F |+| G) f (inl x) = inl (map F f x)
map (F |+| G) f (inr y) = inr (map G f y)
map (F |x| G) f (x , y) = map F f x , map G f y

data μ_ (F : Functor) : Set where
  <_> : [ F ] (μ F) -> μ F

-- fold : (F : Functor){A : Set} -> ([ F ] A -> A) -> μ F -> A
-- fold F ϕ < x > = ϕ (map F (fold F ϕ) x)

mapFold : forall {X} F G -> ([ G ] X -> X) -> [ F ] (μ G) -> [ F ] X
mapFold |Id|        G ϕ < x >   = ϕ (mapFold G G ϕ x)
mapFold (|K| x)     G ϕ c       = c
mapFold (F₁ |+| F₂) G ϕ (inl x) = inl (mapFold F₁ G ϕ x)
mapFold (F₁ |+| F₂) G ϕ (inr x) = inr (mapFold F₂ G ϕ x)
mapFold (F₁ |x| F₂) G ϕ (x , y) = mapFold F₁ G ϕ x , mapFold F₂ G ϕ y

fold : {F : Functor}{A : Set} -> ([ F ] A -> A) -> μ F -> A
fold {F} ϕ < x > = ϕ (mapFold F F ϕ x)

NatF = |K| True |+| |Id|
NAT  = μ NatF

Z : NAT
Z = < inl _ >

S : NAT -> NAT
S n = < inr n >

ListF = \A -> |K| True |+| |K| A |x| |Id|
LIST  = \A -> μ (ListF A)

nil : {A : Set} -> LIST A
nil = < inl _ >

cons : {A : Set} -> A -> LIST A -> LIST A
cons x xs = < inr (x , xs) >

---

[_||_] : {A B C : Set} -> (A -> C) -> (B -> C) -> A ⨁ B -> C
[ f || g ] (inl x) = f x
[ f || g ] (inr y) = g y

uncurry : {A B C : Set} -> (A -> B -> C) -> A × B -> C
uncurry f (x , y) = f x y

const : {A B : Set} -> A -> B -> A
const x y = x

---

foldr : {A B : Set} -> (A -> B -> B) -> B -> LIST A -> B
foldr {A}{B} f z = fold [ const z || uncurry f ]

plus : NAT -> NAT -> NAT
plus n m = fold [ const m || S ] n

-- universes for overloading

open import Tutorial.List

data Type : Set where
  bool : Type
  nat  : Type
  list : Type -> Type
  pair : Type -> Type -> Type

El : Type -> Set
El nat        = Nat
El bool       = Bool
El (list a)   = List (El a)
El (pair a b) = El a × El b

infix 30 _==_
_==_ : {a : Type} -> El a -> El a -> Bool
--
_==_ {nat} zero    zero    = true
_==_ {nat} (suc _) zero    = false
_==_ {nat} zero    (suc _) = false
_==_ {nat} (suc n) (suc m) = n == m
--
_==_ {bool} true  x = x
_==_ {bool} false x = not x
--
_==_ {list a} [] []       = true
_==_ {list a} (_ :: _) [] = false
_==_ {list a} [] (_ :: _) = false
_==_ {list a} (x :: xs) (y :: ys) = x == y and xs == ys
--
_==_ {pair a b} (x₁ , y₁) (x₂ , y₂) = x₁ == x₂ and y₁ == y₂
