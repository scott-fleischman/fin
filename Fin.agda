module Fin where

data Zero : Set where

elim-zero : {A : Set} -> Zero -> A
elim-zero ()

record One : Set where
  constructor <>

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

sym : {A : Set} -> {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

cong : {A B : Set} -> (f : A -> B) -> {x y : A} -> x ≡ y -> f x ≡ f y
cong f refl = refl

_=$=_ : {A B : Set} -> {f g : A -> B} -> f ≡ g -> {x y : A} -> x ≡ y -> f x ≡ g y
refl =$= refl = refl

data Singleton {A : Set} (x : A) : Set where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : {A : Set} (x : A) → Singleton x
inspect x = x with≡ refl


data _+'_ (A B : Set) : Set where
  inl' : A -> A +' B
  inr' : B -> A +' B

inl'-inj : ∀ {A B} {x y : A} -> _≡_ {A +' B} (inl' x) (inl' y) -> x ≡ y
inl'-inj refl = refl

data _×'_ (A B : Set) : Set where
  pair : A -> B -> A ×' B


data Add : (l m n : Nat) -> Set where
  add-zero : ∀ n -> Add zero n n
  add-suc : ∀ l m n -> Add l m n -> Add (suc l) m (suc n)

add-zero-right : ∀ n -> Add n 0 n
add-zero-right zero = add-zero zero
add-zero-right (suc n) = add-suc n zero n (add-zero-right n)

add-suc-left : ∀ {l m n} -> Add l m n -> Add (suc l) m (suc n)
add-suc-left (add-zero n) = add-suc zero n n (add-zero n)
add-suc-left (add-suc l m n a) = add-suc (suc l) m (suc n) (add-suc l m n a)

add-suc-right : ∀ {l m n} -> Add l m n -> Add l (suc m) (suc n)
add-suc-right (add-zero n) = add-zero (suc n)
add-suc-right (add-suc l m n a) = add-suc l (suc m) (suc n) (add-suc-right a)

shift-suc-left : ∀ {l m n} -> Add l (suc m) (suc n) -> Add (suc l) m (suc n)
shift-suc-left {m = m} (add-zero .(suc _)) = add-suc zero m m (add-zero m)
shift-suc-left (add-suc l .(suc _) zero ())
shift-suc-left (add-suc l .(suc _) (suc n) a) = add-suc-left (shift-suc-left a)

shift-suc-right : ∀ {l m n} -> Add (suc l) m (suc n) -> Add l (suc m) (suc n)
shift-suc-right (add-suc l m n a) = add-suc-right a

undo-add-suc-left : ∀ {l m n} -> Add (suc l) m (suc n) -> Add l m n
undo-add-suc-left (add-suc l m n a) = a

undo-add-suc-right : ∀ {l m n} -> Add l (suc m) (suc n) -> Add l m n
undo-add-suc-right {m = m} (add-zero .(suc _)) = add-zero m
undo-add-suc-right (add-suc l .(suc _) zero ())
undo-add-suc-right (add-suc l .(suc _) (suc n) a) = shift-suc-left a

add-plus : ∀ n m -> Add n m (n +N m)
add-plus zero m = add-zero m
add-plus (suc n) m = add-suc n m (n +N m) (add-plus n m)

add-commute : ∀ {l m n} -> Add l m n -> Add m l n
add-commute (add-zero zero) = add-zero zero
add-commute (add-zero (suc n)) = add-suc n zero n (add-commute (add-zero n))
add-commute (add-suc l m n a) = add-suc-right (add-commute a)

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
  plus-eq-add zero m .m refl = add-zero m
  plus-eq-add (suc l) zero n refl rewrite plus-zero l = add-suc-left (add-zero-right l)
  plus-eq-add (suc l) (suc m) n p rewrite plus-suc-eq-suc-plus l m | sym p = add-suc l (suc m) (suc (l +N m)) (add-suc-right (plus-eq-add l m (l +N m) refl))

  add-zero-right-eq : ∀ l m -> Add l 0 m -> l ≡ m
  add-zero-right-eq .0 .0 (add-zero .0) = refl
  add-zero-right-eq .(suc l) .(suc n) (add-suc l .0 n a) rewrite add-zero-right-eq l n a = refl



data _<=_ : (m n : Nat) -> Set where
  zero<=n : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

refl<= : {n : Nat} -> n <= n
refl<= {zero} = zero<=n
refl<= {suc n} = suc<=suc refl<=

suc-right<= : {m n : Nat} -> m <= n -> m <= suc n
suc-right<= zero<=n = zero<=n
suc-right<= (suc<=suc r) = suc<=suc (suc-right<= r)

add-left<= : {l m n : Nat} -> Add l m n -> l <= n
add-left<= (add-zero n) = zero<=n
add-left<= (add-suc l m n a) = suc<=suc (add-left<= a)

add-right<= : {l m n : Nat} -> Add l m n -> m <= n
add-right<= (add-zero n) = refl<=
add-right<= (add-suc l zero n a) = zero<=n
add-right<= (add-suc l (suc m) zero ())
add-right<= (add-suc l (suc m) (suc n) a) = suc-right<= (add-right<= a)



data Fin : Nat -> Set where
  fzero : (n : Nat)          -> Fin (suc n)
  fsuc  : (n : Nat) -> Fin n -> Fin (suc n)

fsuc-inj : ∀ {n f g} -> fsuc n f ≡ fsuc n g -> f ≡ g
fsuc-inj refl = refl

fin-to-nat : ∀ {n} -> Fin n -> Nat
fin-to-nat (fzero n) = zero
fin-to-nat (fsuc n f) = suc (fin-to-nat f)

inl-fin-fsuc : ∀ {l m} -> Fin l +' Fin m -> Fin (suc l) +' Fin m
inl-fin-fsuc (inl' x) = inl' (fsuc _ x)
inl-fin-fsuc (inr' x) = inr' x

split-fin : ∀ {l m n} -> Add l m n -> Fin n -> Fin l +' Fin m
split-fin (add-zero n) f = inr' f
split-fin (add-suc l m n a) (fzero .n) = inl' (fzero l)
split-fin (add-suc l m n a) (fsuc .n f) = inl-fin-fsuc (split-fin a f)

max : ∀ {n} -> Fin (suc n)
max {zero} = fzero zero
max {suc n} = fsuc (suc n) max

min : ∀ {n} -> Fin (suc n)
min {n} = fzero n





data Name : Set where
  name : Nat -> Name

data Type : Set where
  Empty : Type
  Unit : Type
  _+_ : (S T : Type) -> Type

data Size : Type -> Nat -> Set where
  size-empty : Size Empty 0
  size-unit : Size Unit 1
  size+ : ∀ {cS cT cST S T} -> Size S cS -> Size T cT -> Add cS cT cST -> Size (S + T) cST

record SizedType (type : Type) : Set where
  constructor sized-type
  field
    cardinality : Nat
    size : Size type cardinality

make-size : (T : Type) -> SizedType T
make-size Empty = sized-type zero size-empty
make-size Unit = sized-type 1 size-unit
make-size (S + T) with make-size S | make-size T
... | sized-type cS sizeS | sized-type cT sizeT = sized-type (cS +N cT) (size+ sizeS sizeT (add-plus cS cT))

data Value : Type -> Set where
  unit : Value Unit
  inl : ∀ {S T} -> Value S -> Value (S + T)
  inr : ∀ {S T} -> Value T -> Value (S + T)

data InhabitedType : Type -> Set where
  InhabitedUnit : InhabitedType Unit
  _+I_ : {S T : Type} -> InhabitedType S -> InhabitedType T -> InhabitedType (S + T)

data NormalType : Type -> Set where
  normal-empty : NormalType Empty
  normal-inhabited : {T : Type} -> InhabitedType T -> NormalType T

record NormalTypeR : Set where
  constructor normal-type
  field
    {type} : Type
    normal : NormalType type

data InhabitedSize : {T : Type} -> InhabitedType T -> Nat -> Set where
  inhabited-size-unit : InhabitedSize InhabitedUnit 1
  inhabited-size-sum : {S T : Type} {cs ct cst : Nat} {IS : InhabitedType S} {IT : InhabitedType T}
    -> (sis : InhabitedSize IS cs) -> (sit : InhabitedSize IT ct) -> Add cs ct cst -> InhabitedSize (IS +I IT) cst

inhabited-size-zero : {T : Type} {IT : InhabitedType T} -> InhabitedSize IT 0 -> Zero
inhabited-size-zero (inhabited-size-sum s t (add-zero .0)) = inhabited-size-zero s

data NormalSize : {T : Type} -> NormalType T -> Nat -> Set where
  normal-size-empty : NormalSize normal-empty 0
  normal-size-inhabited : {T : Type} {ct : Nat} {IT : InhabitedType T} -> InhabitedSize IT ct -> NormalSize (normal-inhabited IT) ct


data InhabitedValue : {T : Type} {IT : InhabitedType T} -> Value T -> Set where
  inhabited-unit : InhabitedValue {IT = InhabitedUnit} unit
  inhabited-inl : {S T : Type} {IS : InhabitedType S} {IT : InhabitedType T} {vs : Value S} -> InhabitedValue {IT = IS} vs -> InhabitedValue {IT = IS +I IT} (inl vs)
  inhabited-inr : {S T : Type} {IS : InhabitedType S} {IT : InhabitedType T} {vt : Value T} -> InhabitedValue {IT = IT} vt -> InhabitedValue {IT = IS +I IT} (inr vt)

normalize-type : Type -> Type
normalize-type Empty = Empty
normalize-type Unit = Unit
normalize-type (S + T) with normalize-type S | normalize-type T
normalize-type (S + T) | Empty | T' = T'
normalize-type (S + T) | Unit | T' = Unit + T'
normalize-type (S + T) | S1 + S2 | Empty = S1 + S2
normalize-type (S + T) | S1 + S2 | Unit = (S1 + S2) + Unit
normalize-type (S + T) | S1 + S2 | T1 + T2 = (S1 + S2) + (T1 + T2)

normalize-typeR : Type -> NormalTypeR
normalize-typeR Empty = normal-type normal-empty
normalize-typeR Unit = normal-type (normal-inhabited InhabitedUnit)
normalize-typeR (S + T) with normalize-typeR S | normalize-typeR T
normalize-typeR (S + T) | normal-type normal-empty         | normal-type normal-empty         = normal-type normal-empty
normalize-typeR (S + T) | normal-type normal-empty         | normal-type (normal-inhabited t) = normal-type (normal-inhabited t)
normalize-typeR (S + T) | normal-type (normal-inhabited s) | normal-type normal-empty         = normal-type (normal-inhabited s)
normalize-typeR (S + T) | normal-type (normal-inhabited s) | normal-type (normal-inhabited t) = normal-type (normal-inhabited (s +I t))

type-normal-size : {T : Type} {ct : Nat} -> Size T ct -> NormalSize (NormalTypeR.normal (normalize-typeR T)) ct
type-normal-size size-empty = normal-size-empty
type-normal-size size-unit = normal-size-inhabited inhabited-size-unit
type-normal-size (size+ {S = S} {T = T} s t x) = {!!}

inl-map : {S1 S2 T : Type} -> (f : Value S1 -> Value S2) -> Value (S1 + T) -> Value (S2 + T)
inl-map f (inl v) = inl (f v)
inl-map f (inr v) = inr v

inr-map : {S T1 T2 : Type} -> (f : Value T1 -> Value T2) -> Value (S + T1) -> Value (S + T2)
inr-map f (inl v) = inl v
inr-map f (inr v) = inr (f v)

fill-left-suc : ∀ n -> Fin n -> Fin (suc n)
fill-left-suc .(suc n) (fzero n) = fzero (suc n)
fill-left-suc .(suc n) (fsuc n f) = fsuc (suc n) (fill-left-suc n f)

fill-left : ∀ {l m n} -> Add l m n -> Fin l -> Fin n
fill-left (add-zero m) ()
fill-left (add-suc l m n a) (fzero .l) = fzero n
fill-left (add-suc l m n a) (fsuc .l f) = fsuc n (fill-left a f)



split-fin-fill-left : ∀ {l m n} v -> (a : Add l m n) -> split-fin a (fill-left a v) ≡ inl' v
split-fin-fill-left () (add-zero m)
split-fin-fill-left (fzero .l) (add-suc l m n a) = refl
split-fin-fill-left (fsuc .l v) (add-suc l m n a) rewrite split-fin-fill-left v a = refl


-- given: l + m = n
-- if:    split-fin (Fin n) = inl' (Fin l)
-- then:  fill-left (Fin l) = Fin n
split-fin-fill-left' : ∀ {l m n} -> (a : Add l m n) -> (finN : Fin n) -> (finL : Fin l) -> split-fin a finN ≡ inl' finL -> fill-left a finL ≡ finN
split-fin-fill-left' (add-zero n) f g ()
split-fin-fill-left' (add-suc l m n a) (fzero .n) g p rewrite sym (inl'-inj p) = refl

-- l + m = n
-- if:   inl-fin-fsuc (split-fin (Fin n)) = inl' (Fin (suc l))
-- then: fill-left (Fin (suc l)) = fsuc (Fin (suc n))
split-fin-fill-left' (add-suc l m n a) (fsuc .n f) (fzero .l) p = {!!}
split-fin-fill-left' (add-suc l m n a) (fsuc .n f) (fsuc .l g) p = {!!} -- with inspect (split-fin-fill-left' a f g p)

fin-to-nat-fill-left-suc : ∀ n -> (f : Fin n) -> fin-to-nat (fill-left-suc n f) ≡ fin-to-nat f
fin-to-nat-fill-left-suc .(suc n) (fzero n) = refl
fin-to-nat-fill-left-suc .(suc n) (fsuc n f) rewrite fin-to-nat-fill-left-suc n f = refl

fill-left-nat : ∀ {l m n} -> (a : Add l m n) -> (f : Fin l) -> fin-to-nat f ≡ fin-to-nat (fill-left a f)
fill-left-nat (add-zero m) ()
fill-left-nat (add-suc l m n a) (fzero .l) = refl
fill-left-nat (add-suc l m n a) (fsuc .l fin) rewrite fill-left-nat a fin = refl

fill-right-suc : ∀ n -> Fin n -> Fin (suc n)
fill-right-suc .(suc n) (fzero n) = fsuc (suc n) (fzero n)
fill-right-suc .(suc n) (fsuc n f) = fsuc (suc n) (fsuc n f)

fin-to-nat-fill-right-suc : ∀ n -> (f : Fin n) -> fin-to-nat (fill-right-suc n f) ≡ suc (fin-to-nat f)
fin-to-nat-fill-right-suc .(suc n) (fzero n) = refl
fin-to-nat-fill-right-suc .(suc n) (fsuc n f) = refl

fill-right : ∀ {l m n} -> Add l m n -> Fin m -> Fin n
fill-right (add-zero m) fin = fin
fill-right (add-suc l m n a) fin = fsuc n (fill-right a fin)

split-fin-fill-right : ∀ {l m n} v -> (a : Add l m n) -> split-fin a (fill-right a v) ≡ inr' v
split-fin-fill-right v (add-zero n) = refl
split-fin-fill-right v (add-suc l m n a) rewrite split-fin-fill-right v a = refl

size-left-empty : (T : Type) -> (cT : Nat) -> Size (Empty + T) cT -> Size T cT
size-left-empty T cT (size+ size-empty sizeT (add-zero .cT)) = sizeT

size-right-empty : (T : Type) -> (cT : Nat) -> Size (T + Empty) cT -> Size T cT
size-right-empty T .0 (size+ s size-empty (add-zero .0)) = s
size-right-empty T .(suc n) (size+ s size-empty (add-suc l .0 n x)) rewrite AddLemmas.add-zero-right-eq l n x = s


encodei : {T : Type} {ct : Nat} {IT : InhabitedType T} {v : Value T} -> InhabitedSize IT ct -> InhabitedValue {IT = IT} v -> Fin ct
encodei inhabited-size-unit inhabited-unit = fzero zero
encodei (inhabited-size-sum s t (add-zero n)) (inhabited-inl v) = elim-zero (inhabited-size-zero s) 
encodei (inhabited-size-sum inhabited-size-unit t (add-suc .0 m n x)) (inhabited-inl v) = {!!}
encodei (inhabited-size-sum (inhabited-size-sum s s₁ x₁) t (add-suc l m n x)) (inhabited-inl v) = {!!}
encodei (inhabited-size-sum s t x) (inhabited-inr v) = {!!}


encode : {T : Type} -> {cT : Nat} -> Size T cT -> Value T -> Fin cT
encode size-unit unit = fzero zero
encode (size+ sizeS sizeT x) (inl value) = fill-left x (encode sizeS value)
encode (size+ sizeS sizeT x) (inr value) = fill-right x (encode sizeT value)

encode' : {T : Type} -> (s : SizedType T) -> Value T -> Fin (SizedType.cardinality s)
encode' (sized-type cardinality size) v = encode size v

encode-nat : (T : Type) -> Value T -> Nat
encode-nat T v with make-size T
encode-nat T v | sized-type cardinality size = fin-to-nat (encode' (sized-type cardinality size) v)

module EncodeExamples where
  example-encoding1a : encode-nat (Unit + Unit) (inl unit) ≡ 0
  example-encoding1a = refl

  example-encoding1b : encode-nat (Unit + Unit) (inr unit) ≡ 1
  example-encoding1b = refl

  example-encoding2a : encode-nat ((Unit + Unit) + Unit) (inl (inl unit)) ≡ 0
  example-encoding2a = refl

  example-encoding2b : encode-nat ((Unit + Unit) + Unit) (inl (inr unit)) ≡ 1
  example-encoding2b = refl

  example-encoding2c : encode-nat ((Unit + Unit) + Unit) (inr unit) ≡ 2
  example-encoding2c = refl

  example-encoding3d : encode-nat ((Unit + (Unit + (Unit + Unit))) + Unit) (inr unit) ≡ 4
  example-encoding3d = refl

decode : {T : Type} -> {cT : Nat} -> Size T cT -> Fin cT -> Value T
decode-aux : ∀ {cS cT S T} -> Size S cS -> Size T cT -> Fin cS +' Fin cT -> Value (S + T)

decode size-empty ()
decode size-unit (fzero .0) = unit
decode size-unit (fsuc .0 ())
decode (size+ sizeS sizeT x) fin = decode-aux sizeS sizeT (split-fin x fin)

decode-aux {S = S} sizeS sizeT (inl' finS) = inl (decode sizeS finS)
decode-aux {T = T} sizeS sizeT (inr' finT) = inr (decode sizeT finT)


decode2 : {T : Type} -> {cT : Nat} -> Size T cT -> Fin cT -> Value T
decode2 size-empty ()
decode2 size-unit (fzero .0) = unit
decode2 size-unit (fsuc .0 ())
decode2 (size+ s t (add-zero n)) f = inr (decode2 t f)
decode2 (size+ s t (add-suc l m n x)) (fzero .n) = inl (decode2 s (fzero l))
decode2 (size+ size-unit t (add-suc .0 .n n (add-zero .n))) (fsuc .n f) = inr (decode2 t f)
decode2 (size+ (size+ s1 s2 (add-zero .(suc l))) t (add-suc l m n x)) (fsuc .n f) = inl-map inr (decode2 (size+ s2 t (add-suc l m n x)) (fsuc n f))
decode2 (size+ (size+ size-unit s2 (add-suc .0 ss2 .ss xs)) t (add-suc ss m n x)) (fsuc .n f) = {!!}
decode2 (size+ (size+ (size+ s1 s3 x₁) s2 (add-suc ss1 ss2 .ss xs)) t (add-suc ss m n x)) (fsuc .n f) = {!!}


decode' : {T : Type} -> (s : SizedType T) -> Fin (SizedType.cardinality s) -> Value T
decode' (sized-type cardinality size) fin = decode size fin


-- decode-fill-left : (S T : Type) -> (cS cT cST : Nat) -> (sizeS : Size S cS) -> (sizeT : Size T cT) -> (d : Fin cS) -> decode


module DecodeExamples where
  example-decode1a : let T = Unit + Unit in decode' (make-size T) (fzero _) ≡ inl unit
  example-decode1a = refl

  example-decode1b : let T = Unit + Unit in decode' (make-size T) (fsuc _ (fzero _)) ≡ inr unit
  example-decode1b = refl

  example-decode2a : let T = (Unit + Unit) + Unit in decode' (make-size T) (fzero _) ≡ inl (inl unit)
  example-decode2a = refl

  example-decode2b : let T = (Unit + Unit) + Unit in decode' (make-size T) (fsuc _ (fzero  _)) ≡ inl (inr unit)
  example-decode2b = refl

  example-decode2c : let T = (Unit + Unit) + Unit in decode' (make-size T) (fsuc _ (fsuc _ (fzero _))) ≡ inr unit
  example-decode2c = refl

decode-encode : {T : Type} -> {cT : Nat} -> (s : Size T cT) -> (v : Value T) -> decode s (encode s v) ≡ v
decode-encode size-unit unit = refl
decode-encode (size+ s t x) (inl v) rewrite split-fin-fill-left (encode s v) x | decode-encode s v = refl
decode-encode (size+ s t x) (inr v) rewrite split-fin-fill-right (encode t v) x | decode-encode t v = refl


encode-decode : {T : Type} -> {cT : Nat} -> (s : Size T cT) -> (f : Fin cT) -> encode s (decode s f) ≡ f
encode-decode size-unit (fzero .0) = refl
encode-decode size-unit (fsuc .0 ())
encode-decode (size+ s t (add-zero n)) f rewrite encode-decode t f = refl
encode-decode (size+ s t (add-suc l m n x)) (fzero .n) rewrite encode-decode s (fzero l) = refl
encode-decode (size+ s t (add-suc l m n x)) (fsuc .n f) with inspect (split-fin x f)
encode-decode (size+ s t (add-suc l m n x)) (fsuc .n f) | inl' finL with≡ p rewrite p | encode-decode s (fsuc l finL) = cong (fsuc n) (split-fin-fill-left' x f finL p)
encode-decode (size+ s t (add-suc l m n x)) (fsuc .n f) | inr' finM with≡ p rewrite p | encode-decode t finM = cong (fsuc n) {!!}
