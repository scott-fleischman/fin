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

fin-to-nat : ∀ n -> Fin n -> Nat
fin-to-nat .(suc n) (fzero n) = zero
fin-to-nat .(suc n) (fsuc n f) = suc (fin-to-nat n f)

data Name : Set where
  name : Nat -> Name

data Type : Set where
  Empty : Type
  Unit : Type
  _+_ : (S T : Type) -> Type

data Add : (l m n : Nat) -> Set where
  zero+n : ∀ n -> Add zero n n
  n+zero : ∀ n -> Add n zero n
  suc-suc : ∀ l m n -> Add l m n -> Add (suc l) (suc m) (suc (suc n))

add-suc-left : ∀ l m n -> Add l m n -> Add (suc l) m (suc n)
add-suc-left .0        zero    .0             (zero+n .0)       = n+zero 1
add-suc-left .0        (suc m) .(suc m)       (zero+n .(suc m)) = suc-suc zero m m (zero+n m)
add-suc-left l        .0       .l             (n+zero .l)       = n+zero (suc l)
add-suc-left .(suc l) .(suc m) .(suc (suc n)) (suc-suc l m n p) = suc-suc (suc l) m (suc n) (add-suc-left l m n p)

add-suc-right : ∀ l m n -> Add l m n -> Add l (suc m) (suc n)
add-suc-right .0        m       .m             (zero+n .m)       = zero+n (suc m)
add-suc-right zero     .0       .0             (n+zero .0)       = zero+n 1
add-suc-right (suc l)  .0       .(suc l)       (n+zero .(suc l)) = suc-suc l zero l (n+zero l)
add-suc-right .(suc l) .(suc m) .(suc (suc n)) (suc-suc l m n a) = suc-suc l (suc m) (suc n) (add-suc-right l m n a)

sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

add-plus : ∀ n m -> Add n m (n +N m)
add-plus zero m = zero+n m
add-plus (suc n) m = add-suc-left n m (n +N m) (add-plus n m)

module AddLemmas where
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

  plus-eq-add : ∀ l m n -> l +N m ≡ n -> Add l m n
  plus-eq-add zero m n p rewrite p = zero+n n
  plus-eq-add (suc l) zero n p rewrite plus-zero l | p = n+zero n
  plus-eq-add (suc l) (suc m) n p rewrite suc-plus-suc l m | sym p = suc-suc l m (l +N m) (plus-eq-add l m (l +N m) refl)


data Size : Type -> Nat -> Set where
  size-empty : Size Empty 0
  size-unit : Size Unit 1
  size+ : ∀ cS cT cST S T -> Size S cS -> Size T cT -> Add cS cT cST -> Size (S + T) cST

record SizedType (type : Type) : Set where
  constructor sized-type
  field
    cardinality : Nat
    size : Size type cardinality

make-size : (T : Type) -> SizedType T
make-size Empty = sized-type zero size-empty
make-size Unit = sized-type 1 size-unit
make-size (S + T) with make-size S | make-size T
... | sized-type cS sizeS | sized-type cT sizeT = sized-type (cS +N cT) (size+ cS cT (cS +N cT) S T sizeS sizeT (add-plus cS cT))

data Value : Type -> Set where
  unit : Value Unit
  inl : ∀ S T -> Value S -> Value (S + T)
  inr : ∀ S T -> Value T -> Value (S + T)

fill-left-suc : ∀ n -> Fin n -> Fin (suc n)
fill-left-suc .(suc n) (fzero n) = fzero (suc n)
fill-left-suc .(suc n) (fsuc n f) = fsuc (suc n) (fill-left-suc n f)

fill-left : ∀ l m n -> Add l m n -> Fin l -> Fin n
fill-left .0 m .m (zero+n .m) ()
fill-left l .0 .l (n+zero .l) f = f
fill-left .(suc l) .(suc m) .(suc (suc n)) (suc-suc l m n a) (fzero .l) = fzero (suc n)
fill-left .(suc l) .(suc m) .(suc (suc n)) (suc-suc l m n a) (fsuc .l f) = fsuc (suc n) (fill-left-suc n (fill-left l m n a f))

fin-to-nat-fill-left-suc : ∀ n -> (f : Fin n) -> fin-to-nat (suc n) (fill-left-suc n f) ≡ fin-to-nat n f
fin-to-nat-fill-left-suc .(suc n) (fzero n) = refl
fin-to-nat-fill-left-suc .(suc n) (fsuc n f) rewrite fin-to-nat-fill-left-suc n f = refl

fill-left-nat : ∀ l m n -> (a : Add l m n) -> (f : Fin l) -> fin-to-nat l f ≡ fin-to-nat n (fill-left l m n a f)
fill-left-nat .0 m .m (zero+n .m) ()
fill-left-nat l .0 .l (n+zero .l) f = refl
fill-left-nat .(suc l) .(suc m) .(suc (suc n)) (suc-suc l m n a) (fzero .l) = refl
fill-left-nat .(suc l) .(suc m) .(suc (suc n)) (suc-suc l m n a) (fsuc .l f) rewrite fin-to-nat-fill-left-suc n (fill-left l m n a f) | fill-left-nat l m n a f = refl

fill-right-suc : ∀ n -> Fin n -> Fin (suc n)
fill-right-suc .(suc n) (fzero n) = fsuc (suc n) (fzero n)
fill-right-suc .(suc n) (fsuc n f) = fsuc (suc n) (fsuc n f)

fin-to-nat-fill-right-suc : ∀ n -> (f : Fin n) -> fin-to-nat (suc n) (fill-right-suc n f) ≡ suc (fin-to-nat n f)
fin-to-nat-fill-right-suc .(suc n) (fzero n) = refl
fin-to-nat-fill-right-suc .(suc n) (fsuc n f) = refl

fill-right : ∀ l m n -> Add l m n -> Fin m -> Fin n
fill-right .0 m .m (zero+n .m) f = f
fill-right l .0 .l (n+zero .l) ()
fill-right .(suc l) .(suc m) .(suc (suc n)) (suc-suc l m n a) f = fill-right-suc (suc n) (fill-right l (suc m) (suc n) (add-suc-right l m n a) f)

encode : (T : Type) -> (cT : Nat) -> Size T cT -> Value T -> Fin cT
encode .Unit .1 size-unit unit = fzero zero
encode .(S + T) cST (size+ cS cT .cST .S .T sizeS sizeT x) (inl S T value) = fill-left cS cT cST x (encode S cS sizeS value)
encode .(S + T) cST (size+ cS cT .cST .S .T sizeS sizeT x) (inr S T value) = fill-right cS cT cST x (encode T cT sizeT value)

encode' : (T : Type) -> (s : SizedType T) -> Value T -> Fin (SizedType.cardinality s)
encode' T (sized-type cardinality size) v = encode T cardinality size v

encode-nat : (T : Type) -> Value T -> Nat
encode-nat T v with make-size T
encode-nat T v | sized-type cardinality size = fin-to-nat cardinality (encode' T (sized-type cardinality size) v)

module EncodeExamples where
  example-encoding1a : encode-nat (Unit + Unit) (inl _ _ unit) ≡ 0
  example-encoding1a = refl

  example-encoding1b : encode-nat (Unit + Unit) (inr _ _ unit) ≡ 1
  example-encoding1b = refl

  example-encoding2a : encode-nat ((Unit + Unit) + Unit) (inl _ _ (inl _ _ unit)) ≡ 0
  example-encoding2a = refl

  example-encoding2b : encode-nat ((Unit + Unit) + Unit) (inl _ _ (inr _ _ unit)) ≡ 1
  example-encoding2b = refl

  example-encoding2c : encode-nat ((Unit + Unit) + Unit) (inr _ _ unit) ≡ 2
  example-encoding2c = refl

  example-encoding3d : encode-nat ((Unit + (Unit + (Unit + Unit))) + Unit) (inr _ _ unit) ≡ 4
  example-encoding3d = refl

decode : (T : Type) -> (cT : Nat) -> Size T cT -> Fin cT -> Value T
decode Empty zero size-empty ()
decode Empty (suc cT) () fin
decode Unit zero () fin
decode Unit (suc .0) size-unit (fzero .0) = unit
decode Unit (suc .0) size-unit (fsuc .0 ())
decode (S + T) zero (size+ cS cT .0 .S .T sizeS sizeT x) ()
decode (S + T) (suc cST) (size+ cS cT .(suc cST) .S .T sizeS sizeT x) (fzero .cST) = {!!}
decode (S + T) (suc cST) (size+ cS cT .(suc cST) .S .T sizeS sizeT x) (fsuc .cST fin) = {!!}
