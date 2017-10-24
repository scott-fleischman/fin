module Fin where

open import Agda.Builtin.Nat
  using (Nat; zero; suc)
  renaming (_+_ to _+N_)
  renaming (_*_ to _*N_)
import Agda.Builtin.Nat as Nat

open import Agda.Builtin.Equality

data Fin : Nat -> Set where
  fzero : (n : Nat)          -> Fin (suc n)
  fsuc  : (n : Nat) -> Fin n -> Fin (suc n)

data Name : Set where
  name : Nat -> Name

data Type : Set where
  Empty : Type
  Unit : Type
  _+_ : (S T : Type) -> Type
  _*_ : (S T : Type) -> Type

data Add : (l m n : Nat) -> Set where
  zero+n : ∀ n -> Add zero n n
  n+zero : ∀ n -> Add n zero n
  suc-suc : ∀ l m n -> Add l m n -> Add (suc l) (suc m) (suc (suc n))

add-suc-left : ∀ l m n -> Add l m n -> Add (suc l) m (suc n)
add-suc-left .0        zero    .0             (zero+n .0)       = n+zero 1
add-suc-left .0        (suc m) .(suc m)       (zero+n .(suc m)) = suc-suc zero m m (zero+n m)
add-suc-left l        .0       .l             (n+zero .l)       = n+zero (suc l)
add-suc-left .(suc l) .(suc m) .(suc (suc n)) (suc-suc l m n p) = suc-suc (suc l) m (suc n) (add-suc-left l m n p)

add-plus : ∀ n m -> Add n m (n +N m)
add-plus zero m = zero+n m
add-plus (suc n) m = add-suc-left n m (n +N m) (add-plus n m)

plus-zero : ∀ n -> n +N 0 ≡ n
plus-zero zero = refl
plus-zero (suc n) rewrite plus-zero n = refl

suc-plus-suc : ∀ n m -> suc (n +N suc m) ≡ suc (suc (n +N m))
suc-plus-suc zero m = refl
suc-plus-suc (suc n) m rewrite suc-plus-suc n m = refl

add-plus-eq : ∀ l m n -> Add l m n -> l +N m ≡ n
add-plus-eq .0 m .m (zero+n .m) = refl
add-plus-eq l .0 .l (n+zero .l) rewrite plus-zero l = refl
add-plus-eq .(suc l) .(suc m) .(suc (suc n)) (suc-suc l m n p) rewrite suc-plus-suc l m | add-plus-eq l m n p = refl

sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

plus-eq-add : ∀ l m n -> l +N m ≡ n -> Add l m n
plus-eq-add zero m n p rewrite p = zero+n n
plus-eq-add (suc l) zero n p rewrite plus-zero l | p = n+zero n
plus-eq-add (suc l) (suc m) n p rewrite suc-plus-suc l m | sym p = suc-suc l m (l +N m) (plus-eq-add l m (l +N m) refl)


data Size : Type -> Nat -> Set where
  size-empty : Size Empty 0
  size-unit : Size Unit 1
  size+ : ∀ {ss st sst S T} -> Size S ss -> Size T st -> Add ss st sst -> Size (S + T) sst
  size* : ∀ {ss st S T} -> Size S ss -> Size T st -> Size (S * T) (ss *N st)

data Value : Type -> Set where
  unit : Value Unit
  inl : ∀ {S T} -> Value S -> Value (S + T)
  inr : ∀ {S T} -> Value T -> Value (S + T)
  pair : ∀ {S T} -> Value S -> Value T -> Value (S * T)

size-fin : (T : Type) -> (st : Nat) -> Size T (suc st) -> Value T -> Fin (suc st)
size-fin .Unit    st s unit = fzero st
size-fin .(S + T) st (size+ {ss'} ss st' x) (inl {S} {T} v) = {!!} -- size-fin S ss' ss 
size-fin .(_ + _) st s (inr v) = {!!}
size-fin .(_ * _) st s (pair v v₁) = {!!}
