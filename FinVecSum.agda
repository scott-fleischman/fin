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

vec-foldr : {A B : Set} (b : B) (f : A -> B -> B) {n : Nat} (v : Vec A n) -> B
vec-foldr b f nil = b
vec-foldr b f (x :: xs) = f x (vec-foldr b f xs)

data Type : Set where
  Unit : Type
  Sum : {n : Nat} (Ts : Vec Type n) -> Type

data Value : Type -> Set where
  unit : Value Unit
  choose : {n : Nat} (i : Fin n) (Ts : Vec Type n) (T : Type) (p : T ≡ index-at i Ts) (v : Value T) -> Value (Sum Ts)

cardinality : Type -> Nat
cardinality Unit = 1
cardinality (Sum nil) = 0
cardinality (Sum (T :: Ts)) = cardinality T +N cardinality (Sum Ts)

encode : {T : Type} (v : Value T) -> Fin (cardinality T)
encode unit = fz
encode (choose fz (T :: Ts) .T refl v) = expand-fin (encode v) (cardinality (Sum Ts)) 
encode (choose (fs i) (T :: Ts) T' p v) = shift-fin (cardinality T) (encode (choose i Ts T' p v))

decode : {T : Type} -> Fin (cardinality T) -> Value T
decode {Unit} fz = unit
decode {Unit} (fs ())
decode {Sum nil} ()
decode {Sum (T :: Ts)} f with split-fin {cardinality T} {cardinality (Sum Ts)} f
decode {Sum (T :: Ts)} f | inlT f' = choose fz (T :: Ts) T refl (decode {T} f')
decode {Sum (T :: Ts)} f | inrT f' with decode {Sum Ts} f'
decode {Sum (T :: Ts)} f | inrT f' | choose i .Ts T' p v = choose (fs i) (T :: Ts) T' p v 

encode-decode-id : {T : Type} (f : Fin (cardinality T)) -> encode {T} (decode f) ≡ f
encode-decode-id {Unit} fz = refl
encode-decode-id {Unit} (fs ())
encode-decode-id {Sum nil} ()
encode-decode-id {Sum (T :: Ts)} f with split-fin {cardinality T} {cardinality (Sum Ts)} f | inspect (split-fin {cardinality T} {cardinality (Sum Ts)}) f
encode-decode-id {Sum (T :: Ts)} f | inlT f' | [ eq ] rewrite encode-decode-id {T} f' = {!!}
encode-decode-id {Sum (T :: Ts)} f | inrT f' | eq with decode {Sum Ts} f'
encode-decode-id {Sum (T :: Ts)} f | inrT f' | eq | choose i .Ts T' p r = {!!}

decode-encode-id : {T : Type} (v : Value T) -> decode (encode v) ≡ v
decode-encode-id unit = refl
decode-encode-id (choose () nil T p v)
decode-encode-id (choose i (T :: Ts) T' p v)
  with split-fin {cardinality T} {cardinality (Sum Ts)} (encode (choose i (T :: Ts) T' p v))
  | inspect (split-fin {cardinality T} {cardinality (Sum Ts)}) (encode (choose i (T :: Ts) T' p v))
decode-encode-id (choose i (T :: Ts) T' p v) | inlT x | [ eq ] = {!!}
decode-encode-id (choose i (T :: Ts) T' p v) | inrT x | [ eq ] = {!!}
