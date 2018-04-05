module _ where

open import Agda.Builtin.Nat
  using (Nat; zero; suc)
  renaming (_+_ to _+N_)
  renaming (_*_ to _*N_)

open import Agda.Builtin.FromNat

open import Agda.Builtin.Equality

record Reveal {A : Set} {B : A → Set} (f : (x : A) → B x) (x : A) (y : B x) : Set where
  constructor [_]
  field eq : f x ≡ y

inspect : {A : Set} {B : A -> Set} (f : (x : A) -> B x) (x : A)
  -> Reveal f x (f x)
inspect f x = [ refl ]

sym : {A : Set} -> {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

cong : {A B : Set} -> (f : A -> B) -> {x y : A} -> x ≡ y -> f x ≡ f y
cong _ refl = refl

trans : {A : Set} -> {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl refl = refl

data False : Set where
record True : Set where
  constructor true

instance
  Number-Nat : Number Nat
  Number.Constraint Number-Nat _ = True
  Number.fromNat    Number-Nat n = n

nat-plus-zero : (n : Nat) -> n +N 0 ≡ n
nat-plus-zero zero = refl
nat-plus-zero (suc n) = cong suc (nat-plus-zero n)

plus-suc-right : (m n : Nat) -> m +N suc n ≡ suc (m +N n)
plus-suc-right zero _ = refl
plus-suc-right (suc m) n = cong suc (plus-suc-right m n)

nat-commutative : (m n : Nat) -> m +N n ≡ n +N m
nat-commutative zero n rewrite nat-plus-zero n = refl
nat-commutative (suc m) n rewrite plus-suc-right n m = cong suc (nat-commutative m n)

data Fin : Nat -> Set where
  fz : {n : Nat} -> Fin (suc n)
  fs : {n : Nat} -> Fin n -> Fin (suc n)

out-of : (n : Nat) -> Fin n -> Fin n
out-of _ x = x

_<Set_ : (n m : Nat) -> Set
zero <Set zero = False
zero <Set suc m = True
suc n <Set zero = False
suc n <Set suc m = n <Set m

nat-to-fin : (n : Nat) -> {m : Nat} -> {{p : n <Set m}} -> Fin m
nat-to-fin zero {zero} {{()}}
nat-to-fin zero {suc m} {{true}} = fz
nat-to-fin (suc n) {zero} {{()}}
nat-to-fin (suc n) {suc m} = fs (nat-to-fin n)

fin-to-nat : {n : Nat} -> Fin n -> Nat
fin-to-nat fz = zero
fin-to-nat (fs f) = suc (fin-to-nat f)

instance
  Number-Fin : {n : Nat} → Number (Fin n)
  Number.Constraint (Number-Fin {n}) m = m <Set n
  Number.fromNat    Number-Fin       m = nat-to-fin m

inc-fin-bound : {n : Nat} -> Fin n -> Fin (suc n)
inc-fin-bound fz = fz
inc-fin-bound (fs x) = fs (inc-fin-bound x)

expand-fin : {m : Nat} -> Fin m -> (n : Nat) -> Fin (m +N n)
expand-fin fz     n = fz
expand-fin (fs f) n = fs (expand-fin f n)

shift-fin : (m : Nat) -> {n : Nat} -> Fin n -> Fin (m +N n)
shift-fin zero    f = f
shift-fin (suc m) f = fs (shift-fin m f)

add-fin : {m : Nat} -> Fin m -> {n : Nat} -> Fin n -> Fin (m +N n)
add-fin fz fz = fz
add-fin (fz {m}) (fs {n} y) rewrite plus-suc-right m n = fs (add-fin (fz {m}) y)
add-fin (fs x) y = fs (add-fin x y)

add-fin-plus-nat : {m n : Nat} -> (x : Fin m) -> (y : Fin n)
  -> fin-to-nat x +N fin-to-nat y ≡ fin-to-nat (add-fin x y)
add-fin-plus-nat fz fz = refl
add-fin-plus-nat (fz {m}) (fs {n} y) rewrite plus-suc-right m n = cong suc (add-fin-plus-nat fz y)
add-fin-plus-nat (fs x) y = cong suc (add-fin-plus-nat x y)

module ExFin where
  f5 = out-of 10 5
  f3 = out-of 5 3
  _ : fin-to-nat f5 +N fin-to-nat f3 ≡ fin-to-nat (add-fin f5 f3)
  _ = refl


data _+T_ (S T : Set) : Set where
  inlT : S -> S +T T
  inrT : T -> S +T T

remove-inlT : {S T : Set} -> {x y : S} -> inlT {T = T} x ≡ inlT y -> x ≡ y
remove-inlT refl = refl

remove-inrT : {S T : Set} -> {x y : T} -> inrT {S = S} x ≡ inrT y -> x ≡ y
remove-inrT refl = refl

shift-fin-inlT : {m n : Nat} → Fin m +T Fin n → Fin (suc m) +T Fin n
shift-fin-inlT (inlT x) = inlT (fs x)
shift-fin-inlT (inrT y) = inrT y

split-fin : {m n : Nat} -> Fin (m +N n) -> Fin m +T Fin n
split-fin {zero} f = inrT f
split-fin {suc m} fz = inlT fz
split-fin {suc m} (fs f) = shift-fin-inlT (split-fin f)

split-fin-after-expand-fin : {m : Nat} -> (f : Fin m) -> (n : Nat) -> split-fin (expand-fin f n) ≡ inlT f
split-fin-after-expand-fin fz n = refl
split-fin-after-expand-fin (fs f) n rewrite split-fin-after-expand-fin f n = refl

split-fin-after-shift-fin : (m : Nat) -> {n : Nat} -> (f : Fin n) -> split-fin {m} (shift-fin m f) ≡ inrT f
split-fin-after-shift-fin zero f = refl
split-fin-after-shift-fin (suc m) f rewrite split-fin-after-shift-fin m f = refl

split-fin-left-expand-fin : {m n : Nat}
  -> (x : Fin (m +N n))
  -> (y : Fin m)
  -> split-fin x ≡ inlT y
  -> x ≡ expand-fin y n
split-fin-left-expand-fin {zero} x y ()
split-fin-left-expand-fin {suc m} fz .fz refl = refl
split-fin-left-expand-fin {suc m} (fs x) y p with split-fin {m} x | inspect (split-fin {m}) x
split-fin-left-expand-fin {suc m} (fs x) y p | inlT z | [ eq ] rewrite remove-inlT (sym p) = cong fs (split-fin-left-expand-fin x z eq)
split-fin-left-expand-fin {suc m} (fs x) y () | inrT _ | [ eq ]

split-fin-right-shift-fin : {m n : Nat}
  -> (x : Fin (m +N n))
  -> (y : Fin n)
  -> split-fin {m} x ≡ inrT y
  -> shift-fin m y ≡ x
split-fin-right-shift-fin {zero} x y p rewrite remove-inrT p = refl
split-fin-right-shift-fin {suc m} fz y ()
split-fin-right-shift-fin {suc m} (fs x) y p with split-fin {m} x | inspect (split-fin {m}) x
split-fin-right-shift-fin {suc m} (fs x) y () | inlT _ | [ eq ]
split-fin-right-shift-fin {suc m} (fs x) y p | inrT z | [ eq ] rewrite remove-inrT (sym p) = cong fs (split-fin-right-shift-fin x z eq)

module ExpectedExpandShift where
  _ : expand-fin (out-of 4 3) 3 ≡ out-of 7 3
  _ = refl

  _ : shift-fin 3 (out-of 4 3) ≡ out-of 7 6
  _ = refl


data Vec (A : Set) : Nat -> Set where
  nil : Vec A 0
  _::_ : A -> {n : Nat} -> Vec A n -> Vec A (suc n)
infixr 5 _::_

vec-map : {A B : Set} -> (A -> B) -> {n : Nat} -> Vec A n -> Vec B n
vec-map f nil = nil
vec-map f (x :: xs) = f x :: vec-map f xs

vec-append : {A : Set} -> {m n : Nat} -> Vec A m -> Vec A n -> Vec A (m +N n)
vec-append {m = zero} xs ys = ys
vec-append {m = suc n} (x :: xs) ys = x :: vec-append xs ys

vec-fold : {A B : Set} -> B -> (A -> B -> B) -> {n : Nat} -> Vec A n -> B
vec-fold b f nil = b
vec-fold b f (x :: xs) = f x (vec-fold b f xs)

index-at : {n : Nat} -> Fin n -> {A : Set} -> Vec A n -> A
index-at fz (x :: xs) = x
index-at (fs i) (x :: xs) = index-at i xs

fold-fin : {n : Nat} -> {A : Set} -> A -> (Fin n -> A -> A) -> Fin n -> A
fold-fin b f fz = b
fold-fin {suc n} b f (fs x) = f (fs x) (fold-fin b (\ g -> f (inc-fin-bound g)) x)


data Type : Set
data Value : Type -> Set
size : Type -> Nat

data Type where
  Empty : Type
  Unit : Type
  Sum : (S T : Type) -> Type

data Value where
  unit : Value Unit
  inl : {S T : Type} -> Value S -> Value (Sum S T)
  inr : {S T : Type} -> Value T -> Value (Sum S T)

size Empty = 0
size Unit = 1
size (Sum S T) = size S +N size T

encode : {T : Type} -> Value T -> Fin (size T)
encode unit = fz
encode (inl {T = T} s) = expand-fin (encode s) (size T)
encode (inr {S = S} t) = shift-fin (size S) (encode t)

decode : {T : Type} -> Fin (size T) -> Value T

finish-decode : {S T : Type}
  -> Fin (size S) +T Fin (size T)
  -> Value (Sum S T)
finish-decode (inlT x) = inl (decode x)
finish-decode (inrT x) = inr (decode x)

decode {Empty} ()
decode {Unit} f = unit
decode {Sum S T} f = finish-decode (split-fin {size S} {size T} f)

decode-after-encode : {T : Type} -> (v : Value T) -> decode (encode v) ≡ v
decode-after-encode unit = refl
decode-after-encode (inl {T = T} s) rewrite split-fin-after-expand-fin (encode s) (size T) | decode-after-encode s = refl
decode-after-encode (inr {S = S} t) rewrite split-fin-after-shift-fin (size S) (encode t) | decode-after-encode t = refl

encode-after-decode : {T : Type} -> (f : Fin (size T)) -> encode (decode {T} f) ≡ f
encode-after-decode {Empty} ()
encode-after-decode {Unit} fz = refl
encode-after-decode {Unit} (fs ())
encode-after-decode {Sum S T} f with split-fin {size S} {size T} f | inspect (split-fin {size S} {size T}) f
encode-after-decode {Sum S T} f | inlT x | [ eq ] rewrite encode-after-decode {S} x | split-fin-left-expand-fin f x eq = refl
encode-after-decode {Sum S T} f | inrT x | [ eq ] rewrite encode-after-decode {T} x | split-fin-right-shift-fin f x eq = refl

module _ where
  _ : encode unit ≡ out-of 1 0
  _ = refl

  sumv0 sumv2 : Value (Sum Unit (Sum Unit Unit))
  sumv0 = inl unit
  sumv2 = inr (inr unit)

  _ : encode sumv0 ≡ out-of 3 0
  _ = refl

  _ : encode sumv2 ≡ out-of 3 2
  _ = refl
 
  _ : decode (out-of 3 0) ≡ sumv0
  _ = refl

  _ : decode (out-of 3 2) ≡ sumv2
  _ = refl
