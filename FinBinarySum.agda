module _ where

open import Agda.Builtin.Nat
  using (Nat; zero; suc)
  renaming (_+_ to _+N_)
  renaming (_*_ to _*N_)

open import Agda.Builtin.FromNat

open import Agda.Builtin.Equality

open import Agda.Primitive using (Level; _⊔_)
record Reveal
  {a b : Level}
  {A : Set a}
  {B : A → Set b}
  (f : (x : A) → B x)
  (x : A)
  (y : B x)
  : Set (a ⊔ b)
  where
  constructor [_]
  field eq : f x ≡ y

inspect : {a b : Level}
  -> {A : Set a}
  -> {B : A -> Set b}
  -> (f : (x : A) -> B x)
  -> (x : A)
  -> Reveal f x (f x)
inspect f x = [ refl ]

sym : {A : Set} -> {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

cong : {A B : Set} -> (f : A -> B) -> {x y : A} -> x ≡ y -> f x ≡ f y
cong _ refl = refl

trans : {a : Level} {A : Set a} -> {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl refl = refl

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
  expand3 : expand-fin (out-of 4 3) 3 ≡ (out-of 7 3)
  expand3 = refl

  shift3 : shift-fin 3 (out-of 4 3) ≡ (out-of 7 6)
  shift3 = refl

data Type : Set where
  Empty : Type
  Unit : Type
  Sum : (S T : Type) -> Type

data Value : Type -> Set where
  unit : Value Unit
  inl : {S T : Type} -> Value S -> Value (Sum S T)
  inr : {S T : Type} -> Value T -> Value (Sum S T)

size : Type -> Nat
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
