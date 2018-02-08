module _ where

open import Agda.Builtin.Nat
  using (Nat; zero; suc)
  renaming (_+_ to _+N_)
  renaming (_*_ to _*N_)

open import Agda.Builtin.FromNat

open import Agda.Builtin.Equality

data False : Set where
record True : Set where
  constructor true

instance
  Number-Nat : Number Nat
  Number.Constraint Number-Nat _ = True
  Number.fromNat    Number-Nat n = n

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

instance
  Number-Fin : {n : Nat} → Number (Fin n)
  Number.Constraint (Number-Fin {n}) m = m <Set n
  Number.fromNat    Number-Fin       m = nat-to-fin m

expand-fin : {m : Nat} -> Fin m -> (n : Nat) -> Fin (m +N n)
expand-fin fz     n = fz
expand-fin (fs f) n = fs (expand-fin f n)

shift-fin : (m : Nat) -> {n : Nat} -> Fin n -> Fin (m +N n)
shift-fin zero    f = f
shift-fin (suc m) f = fs (shift-fin m f)


data _+T_ (S T : Set) : Set where
  inlT : S -> S +T T
  inrT : T -> S +T T


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


module ExpectedExpandShift where
  expand3 : expand-fin (out-of 4 3) 3 ≡ (out-of 7 3)
  expand3 = refl

  shift3 : shift-fin 3 (out-of 4 3) ≡ (out-of 7 6)
  shift3 = refl

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

index-at : {n : Nat} -> Fin n -> {A : Set} -> Vec A n -> A
index-at fz (x :: xs) = x
index-at (fs i) (x :: xs) = index-at i xs

data Type : Set where
  Unit : Type
  Sum : (S T : Type) -> Type

data Value : Type -> Set where
  unit : Value Unit
  inl : {S T : Type} -> Value S -> Value (Sum S T)
  inr : {S T : Type} -> Value T -> Value (Sum S T)

as-inl : (T : Type) -> {S : Type} -> Value S -> Value (Sum S T)
as-inl _ v = inl v

as-inr : (S : Type) -> {T : Type} -> Value T -> Value (Sum S T)
as-inr _ v = inr v

size : Type -> Nat
size Unit = 1
size (Sum S T) = size S +N size T

encode : {T : Type} -> Value T -> Fin (size T)
encode unit = fz
encode (inl {T = T} s) = expand-fin (encode s) (size T)
encode (inr {S = S} t) = shift-fin (size S) (encode t)

enumerate : (T : Type) -> Vec (Value T) (size T)
enumerate Unit = unit :: nil
enumerate (Sum S T) = vec-append
  (vec-map (as-inl T) (enumerate S))
  (vec-map (as-inr S) (enumerate T))


decode decode'
  : {T : Type} -> Fin (size T) -> Value T
decode' {T} f = index-at f (enumerate T)

finish-decode : {S T : Type}
  -> Fin (size S) +T Fin (size T)
  -> Value (Sum S T)
finish-decode {T = T} (inlT x) = as-inl T (decode x)
finish-decode {S = S} (inrT x) = as-inr S (decode x)

decode {Unit} f = unit
decode {Sum S T} f = finish-decode (split-fin {size S} {size T} f)

decode-after-encode : {T : Type} -> (v : Value T) -> decode (encode v) ≡ v
decode-after-encode unit = refl
decode-after-encode (inl {T = T} s) rewrite split-fin-after-expand-fin (encode s) (size T) | decode-after-encode s = refl
decode-after-encode (inr {S = S} t) rewrite split-fin-after-shift-fin (size S) (encode t) | decode-after-encode t = refl

encode-after-decode : {T : Type} -> (f : Fin (size T)) -> encode (decode {T} f) ≡ f
encode-after-decode {Unit} fz = refl
encode-after-decode {Unit} (fs ())
encode-after-decode {Sum S T} f with split-fin {size S} {size T} f
encode-after-decode {Sum S T} f | inlT x rewrite encode-after-decode {S} x = {!!}
encode-after-decode {Sum S T} f | inrT x rewrite encode-after-decode {T} x = {!!}

module _ where
  enc1 : encode unit ≡ out-of 1 0
  enc1 = refl

  sumv0 sumv2 : Value (Sum Unit (Sum Unit Unit))
  sumv0 = inl unit
  sumv2 = inr (inr unit)

  enc-sv0 : encode sumv0 ≡ out-of 3 0
  enc-sv0 = refl

  enc-sv2 : encode sumv2 ≡ out-of 3 2
  enc-sv2 = refl
 
  dec-sv0 : decode (out-of 3 0) ≡ sumv0
  dec-sv0 = refl

  dec-sv2 : decode (out-of 3 2) ≡ sumv2
  dec-sv2 = refl
