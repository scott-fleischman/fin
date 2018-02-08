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
nat-to-fin zero {suc m} {{<>}} = fz
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
  Sum : {n : Nat} -> Vec Type n -> Type

data Value : Type -> Set where
  unit : Value Unit
  choose : {n : Nat} -> (f : Fin n) -> {v : Vec Type n} -> Value (index-at f v) -> Value (Sum v)

size : Type -> Nat
size-vec : {n : Nat} -> Vec Type n -> Nat

size Unit = 1
size (Sum ts) = size-vec ts

size-vec nil = 0
size-vec (x :: xs) = size x +N size-vec xs

add-type : (t : Type) -> {n : Nat} -> {ts : Vec Type n} -> Value (Sum ts) -> Value (Sum (t :: ts))
add-type t (choose f v) = choose (fs f) v

promote-to-sum : {n : Nat} -> (ts : Vec Type n) -> {t : Type} -> Value t -> Value (Sum (t :: ts))
promote-to-sum _ v = choose fz v

encode : {T : Type} -> Value T -> Fin (size T)

encode-choose : {n : Nat} -> (f : Fin n) -> {v : Vec Type n} -> Value (index-at f v) -> Fin (size-vec v)
encode-choose ()     {nil}     val
encode-choose fz     {t :: ts} val = expand-fin (encode val) (size-vec ts)
encode-choose (fs f) {t :: ts} val = shift-fin (size t) (encode-choose f {ts} val) 

encode unit = 0
encode (choose f v) = encode-choose f v

enumerate : (T : Type) -> Vec (Value T) (size T)

enumerate-sum : {n : Nat} -> (ts : Vec Type n) -> Vec (Value (Sum ts)) (size-vec ts)
enumerate-sum nil = nil
enumerate-sum (t :: ts) =
  vec-append
    (vec-map (promote-to-sum ts) (enumerate t))
    (vec-map (add-type t) (enumerate-sum ts))

enumerate Unit = unit :: nil
enumerate (Sum ts) = enumerate-sum ts

decode : {T : Type} -> Fin (size T) -> Value T
decode {T} f = index-at f (enumerate T)

module Ex where
  3-Unit : Type
  3-Unit = Sum (Unit :: Unit :: Unit :: nil)

  sum : Value 3-Unit
  sum = choose 0 unit

  sum2 : Value 3-Unit
  sum2 = choose 1 unit
  
  Nested : Type
  Nested = Sum
    (  Unit
    :: Sum
      (  Unit
      :: Unit
      :: Sum
        (  Unit
        :: Unit :: nil) :: nil)
    :: Unit :: nil)

  nested1 : Value Nested
  nested1 = choose 1 (choose 2 (choose 1 unit))

  nested-size : size Nested ≡ 6
  nested-size = refl

  encode1 : encode sum ≡ 0
  encode1 = refl

  encode2 : encode sum2 ≡ 1
  encode2 = refl

  encode-n1 : encode nested1 ≡ 4
  encode-n1 = refl

  decode1 : decode (out-of 3 0) ≡ sum
  decode1 = refl

  decode2 : decode (out-of 3 1) ≡ sum2
  decode2 = refl

  decode-n1 : decode (out-of 6 4) ≡ nested1
  decode-n1 = refl

