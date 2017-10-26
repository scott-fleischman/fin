module Fin where

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

_+N_ : Nat → Nat → Nat
zero  +N m = m
suc n +N m = suc (n +N m)

{-# BUILTIN NATPLUS _+N_ #-}

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  instance refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

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
  add-zero : ∀ n -> Add zero n n
  add-suc : ∀ l m n -> Add l m n -> Add (suc l) m (suc n)

add-zero-right : ∀ n -> Add n 0 n
add-zero-right zero = add-zero zero
add-zero-right (suc n) = add-suc n zero n (add-zero-right n)

add-suc-right : ∀ l m n -> Add l m n -> Add l (suc m) (suc n)
add-suc-right zero zero zero (add-zero .0) = add-zero 1
add-suc-right zero zero (suc n) ()
add-suc-right zero (suc m) zero ()
add-suc-right zero (suc m) (suc .m) (add-zero .(suc m)) = add-zero (suc (suc m))
add-suc-right (suc l) zero zero ()
add-suc-right (suc l) zero (suc n) (add-suc .l .0 .n a) = add-suc l 1 (suc n) (add-suc-right l zero n a)
add-suc-right (suc l) (suc m) zero ()
add-suc-right (suc l) (suc m) (suc n) (add-suc .l .(suc m) .n a) = add-suc l (suc (suc m)) (suc n) (add-suc-right l (suc m) n a)

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

add-plus : ∀ n m -> Add n m (n +N m)
add-plus zero m = add-zero m
add-plus (suc n) m = add-suc n m (n +N m) (add-plus n m)

module AddLemmas where
  plus-zero : ∀ n -> n +N 0 ≡ n
  plus-zero zero = refl
  plus-zero (suc n) rewrite plus-zero n = refl

  suc-plus-suc : ∀ n m -> suc (n +N suc m) ≡ suc (suc (n +N m))
  suc-plus-suc zero m = refl
  suc-plus-suc (suc n) m rewrite suc-plus-suc n m = refl

  plus-suc-eq-suc-plus : ∀ l m -> l +N suc m ≡ suc (l +N m)
  plus-suc-eq-suc-plus zero zero = refl
  plus-suc-eq-suc-plus zero (suc m) = refl
  plus-suc-eq-suc-plus (suc l) zero rewrite plus-suc-eq-suc-plus l 0 = refl
  plus-suc-eq-suc-plus (suc l) (suc m) rewrite plus-suc-eq-suc-plus l (suc m) | plus-suc-eq-suc-plus l m = refl

  add-plus-eq : ∀ l m n -> Add l m n -> l +N m ≡ n
  add-plus-eq .0 m .m (add-zero .m) = refl
  add-plus-eq .(suc l) m .(suc n) (add-suc l .m n a) rewrite add-plus-eq l m n a = refl

  plus-eq-add : ∀ l m n -> l +N m ≡ n -> Add l m n
  plus-eq-add zero zero zero refl = add-zero zero
  plus-eq-add zero zero (suc n) ()
  plus-eq-add zero (suc m) zero ()
  plus-eq-add zero (suc m) (suc .m) refl = add-zero (suc m)
  plus-eq-add (suc l) zero zero ()
  plus-eq-add (suc l) zero (suc .(l +N 0)) refl rewrite plus-zero l = add-suc l 0 l (add-zero-right l)
  plus-eq-add (suc l) (suc m) zero ()
  plus-eq-add (suc l) (suc m) (suc .(l +N suc m)) refl rewrite plus-suc-eq-suc-plus l m = add-suc l (suc m) (suc (l +N m)) (add-suc-right l m (l +N m) (plus-eq-add l m (l +N m) refl))

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
fill-left .0 m .m (add-zero .m) ()
fill-left .(suc l) m .(suc n) (add-suc l .m n a) (fzero .l) = fzero n
fill-left .(suc l) m .(suc n) (add-suc l .m n a) (fsuc .l f) = fsuc n (fill-left l m n a f)

fin-to-nat-fill-left-suc : ∀ n -> (f : Fin n) -> fin-to-nat (suc n) (fill-left-suc n f) ≡ fin-to-nat n f
fin-to-nat-fill-left-suc .(suc n) (fzero n) = refl
fin-to-nat-fill-left-suc .(suc n) (fsuc n f) rewrite fin-to-nat-fill-left-suc n f = refl

fill-left-nat : ∀ l m n -> (a : Add l m n) -> (f : Fin l) -> fin-to-nat l f ≡ fin-to-nat n (fill-left l m n a f)
fill-left-nat .0 m .m (add-zero .m) ()
fill-left-nat .(suc l) m .(suc n) (add-suc l .m n a) (fzero .l) = refl
fill-left-nat .(suc l) m .(suc n) (add-suc l .m n a) (fsuc .l fin) rewrite fill-left-nat l m n a fin = refl

fill-right-suc : ∀ n -> Fin n -> Fin (suc n)
fill-right-suc .(suc n) (fzero n) = fsuc (suc n) (fzero n)
fill-right-suc .(suc n) (fsuc n f) = fsuc (suc n) (fsuc n f)

fin-to-nat-fill-right-suc : ∀ n -> (f : Fin n) -> fin-to-nat (suc n) (fill-right-suc n f) ≡ suc (fin-to-nat n f)
fin-to-nat-fill-right-suc .(suc n) (fzero n) = refl
fin-to-nat-fill-right-suc .(suc n) (fsuc n f) = refl

fill-right : ∀ l m n -> Add l m n -> Fin m -> Fin n
fill-right .0 m .m (add-zero .m) fin = fin
fill-right .(suc l) m .(suc n) (add-suc l .m n a) fin = fsuc n (fill-right l m n a fin)

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

data _+'_ (A B : Set) : Set where
  inl' : A -> A +' B
  inr' : B -> A +' B

split : ∀ l m n -> Add l m n -> Fin n -> Fin l +' Fin m
split .0 m .m (add-zero .m) fin = inr' fin
split .(suc l) m .(suc n) (add-suc l .m n a) (fzero .n) = inl' (fzero l)
split .(suc l) m .(suc n) (add-suc l .m n a) (fsuc .n fin) with split l m n a fin
split .(suc l) m .(suc n) (add-suc l .m n a) (fsuc .n fin) | inl' x = inl' (fsuc l x)
split .(suc l) m .(suc n) (add-suc l .m n a) (fsuc .n fin) | inr' x = inr' x

decode : (T : Type) -> (cT : Nat) -> Size T cT -> Fin cT -> Value T
decode Empty .0 size-empty ()
decode Unit zero () fin
decode Unit (suc .0) size-unit (fzero .0) = unit
decode Unit (suc .0) size-unit (fsuc .0 ())
decode (S + T) cST (size+ cS cT .cST .S .T sizeS sizeT x) fin with split cS cT cST x fin
decode (S + T) cST (size+ cS cT .cST .S .T sizeS sizeT x) fin | inl' finS = inl S T (decode S cS sizeS finS)
decode (S + T) cST (size+ cS cT .cST .S .T sizeS sizeT x) fin | inr' finT = inr S T (decode T cT sizeT finT)

decode' : (T : Type) -> (s : SizedType T) -> Fin (SizedType.cardinality s) -> Value T
decode' T (sized-type cardinality size) fin = decode T cardinality size fin

module DecodeExamples where
  example-decode1a : let T = Unit + Unit in decode' T (make-size T) (fzero _) ≡ inl _ _ unit
  example-decode1a = refl
 
  example-decode1b : let T = Unit + Unit in decode' T (make-size T) (fsuc _ (fzero _)) ≡ inr _ _ unit
  example-decode1b = refl
 
  example-decode2a : let T = (Unit + Unit) + Unit in decode' T (make-size T) (fzero _) ≡ inl _ _ (inl _ _ unit)
  example-decode2a = refl
 
  example-decode2b : let T = (Unit + Unit) + Unit in decode' T (make-size T) (fsuc _ (fzero  _)) ≡ inl _ _ (inr _ _ unit)
  example-decode2b = refl
 
  example-decode2c : let T = (Unit + Unit) + Unit in decode' T (make-size T) (fsuc _ (fsuc _ (fzero _))) ≡ inr _ _ unit
  example-decode2c = refl
