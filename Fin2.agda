module Fin2 where

data Zero : Set where

elim-zero : {A : Set} -> Zero -> A
elim-zero ()

record One : Set where
  constructor <>

infix 4 _≡_
data _≡_ {A : Set} (a : A) : A -> Set where
  refl : a ≡ a
{-# BUILTIN EQUALITY _≡_ #-}

cong : {A B : Set} -> (f : A -> B) -> {x y : A} -> x ≡ y -> f x ≡ f y
cong f refl = refl


record Iso (A B : Set) : Set where
  constructor iso
  field
    to : A -> B
    from : B -> A
    to-from-id : (b : B) -> to (from b) ≡ b
    from-to-id : (a : A) -> from (to a) ≡ a

lift : {A B : Set} -> Iso A B -> (A -> A) -> (B -> B)
lift (iso to from _ _) f b = to (f (from b))

lift2 : {A B : Set} -> Iso A B -> (A -> A -> A) -> (B -> B -> B)
lift2 (iso to from _ _) f b1 b2 = to (f (from b1) (from b2))

data _+'_ (A B : Set) : Set where
  inl' : A -> A +' B
  inr' : B -> A +' B

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

_+N_ : (m n : Nat) -> Nat
zero +N n = n
suc m +N n = suc (m +N n)
{-# BUILTIN NATPLUS _+N_ #-}

plus-zero : (n : Nat) -> n +N 0 ≡ n
plus-zero zero = refl
plus-zero (suc n) = cong suc (plus-zero n)

data Add : (l m n : Nat) -> Set where
  add-zero : (n : Nat) -> Add zero n n
  add-suc-left : {l m n : Nat} -> Add l m n -> Add (suc l) m (suc n)

add-suc-right : {l m n : Nat} -> Add l m n -> Add l (suc m) (suc n)
add-suc-right (add-zero n) = add-zero (suc n)
add-suc-right (add-suc-left a) = add-suc-left (add-suc-right a)

add-commute : {l m n : Nat} -> Add l m n -> Add m l n
add-commute (add-zero zero) = add-zero zero
add-commute (add-zero (suc n)) = add-suc-left (add-commute (add-zero n))
add-commute (add-suc-left a) = add-suc-right (add-commute a)

add-plus : (m n : Nat) -> Add m n (m +N n)
add-plus zero n = add-zero n
add-plus (suc m) n = add-suc-left (add-plus m n)


data Pos : Set where
  pos-one : Pos
  pos-suc : Pos -> Pos

data ZPos : Set where
  zpos-zero : ZPos
  zpos-pos : Pos -> ZPos

inc-zpos : ZPos -> ZPos
inc-zpos zpos-zero = zpos-pos pos-one
inc-zpos (zpos-pos x) = zpos-pos (pos-suc x) 

nat-zpos : Nat -> ZPos
nat-zpos zero = zpos-zero
nat-zpos (suc n) = inc-zpos (nat-zpos n)

pos-nat : Pos -> Nat
pos-nat pos-one = 1
pos-nat (pos-suc p) = suc (pos-nat p)

zpos-nat : ZPos -> Nat
zpos-nat zpos-zero = zero
zpos-nat (zpos-pos x) = pos-nat x

zpos-nat-inc-zpos : (n : ZPos) -> zpos-nat (inc-zpos n) ≡ suc (zpos-nat n)
zpos-nat-inc-zpos zpos-zero = refl
zpos-nat-inc-zpos (zpos-pos x) = refl

nat-zpos-id : (n : Nat) -> zpos-nat (nat-zpos n) ≡ n
nat-zpos-id zero = refl
nat-zpos-id (suc n) rewrite zpos-nat-inc-zpos (nat-zpos n) | nat-zpos-id n = refl

zpos-nat-id-aux : ∀ x ->  inc-zpos (nat-zpos (pos-nat x)) ≡ zpos-pos (pos-suc x)
zpos-nat-id-aux pos-one = refl
zpos-nat-id-aux (pos-suc x) rewrite zpos-nat-id-aux x = refl

zpos-nat-id : (n : ZPos) -> nat-zpos (zpos-nat n) ≡ n
zpos-nat-id zpos-zero = refl
zpos-nat-id (zpos-pos pos-one) = refl
zpos-nat-id (zpos-pos (pos-suc x)) = zpos-nat-id-aux x

iso-nat-zpos : Iso Nat ZPos
iso-nat-zpos = iso nat-zpos zpos-nat zpos-nat-id nat-zpos-id

_+ZP_ = lift2 iso-nat-zpos _+N_


data AddPos : (l m n : Pos) -> Set where
  add-pos-one : {n : Pos} -> AddPos pos-one n (pos-suc n)
  add-pos-left : {l m n : Pos} -> AddPos l m n -> AddPos (pos-suc l) m (pos-suc n)

-- add-pos-plus : (m n : ZPos) -> AddPos ( m) (suc n) (suc m +N suc n)
-- add-pos-plus zero zero = add-pos-one
-- add-pos-plus zero (suc n) = add-pos-right (add-pos-plus zero n)
-- add-pos-plus (suc m) n = add-pos-left (add-pos-plus m n)

-- add-pos-zero : {l m : Nat} -> AddPos l m 0 -> Zero
-- add-pos-zero ()

-- add-pos-one-zero : {l m : Nat} -> AddPos l m 1 -> Zero
-- add-pos-one-zero (add-pos-left ())
-- add-pos-one-zero (add-pos-right ())

-- add-pos-left-zero : {m n : Nat} -> AddPos 0 m n -> Zero
-- add-pos-left-zero (add-pos-right a) = add-pos-left-zero a

-- data Fin : Nat -> Set where
--   fzero : ∀ {n} -> Fin (suc n)
--   fsuc : ∀ {n} -> Fin n -> Fin (suc n)

-- fin-to-nat : {n : Nat} -> Fin n -> Nat
-- fin-to-nat fzero = zero
-- fin-to-nat (fsuc f) = suc (fin-to-nat f)

-- data Type : Set where
--   Unit : Type
--   _+_ : (S T : Type) -> Type

-- data Size : Type -> Nat -> Set where
--   size-unit : Size Unit 1
--   size-sum : {S T : Type} {ss st sst : Nat} -> (a : AddPos ss st sst) -> (s : Size S ss) -> (t : Size T st) -> Size (S + T) sst

-- size-zero : {T : Type} -> Size T 0 -> Zero
-- size-zero (size-sum () s t)

-- data Value : Type -> Set where
--   value-unit : Value Unit
--   value-inl : {S T : Type} -> Value S -> Value (S + T)
--   value-inr : {S T : Type} -> Value T -> Value (S + T)

-- value-inl-map : {S1 S2 T : Type} -> (Value S1 -> Value S2) -> Value (S1 + T) -> Value (S2 + T)
-- value-inl-map f (value-inl v) = value-inl (f v)
-- value-inl-map f (value-inr v) = value-inr v

-- fill-left : {l m n : Nat} -> Add l m n -> Fin l -> Fin n
-- fill-left (add-zero n) ()
-- fill-left (add-suc-left a) fzero = fzero
-- fill-left (add-suc-left a) (fsuc f) = fsuc (fill-left a f)

-- fill-left-spec : {l m : Nat} -> (f : Fin l) -> fin-to-nat (fill-left (add-plus l m) f) ≡ fin-to-nat f
-- fill-left-spec fzero = refl
-- fill-left-spec (fsuc f) = cong suc (fill-left-spec f)

-- fill-left' : {l m n : Nat} -> AddPos l m n -> Fin l -> Fin n
-- fill-left' add-pos-one-one fzero = fzero
-- fill-left' add-pos-one-one (fsuc ())
-- fill-left' (add-pos-left a) fzero = fzero
-- fill-left' (add-pos-left a) (fsuc f) = fsuc (fill-left' a f)
-- fill-left' (add-pos-right a) fzero = fzero
-- fill-left' (add-pos-right a) (fsuc f) = fsuc (fill-left' a (fsuc f))

-- fill-left'-spec : {l m : Nat} -> (f : Fin (suc l)) -> fin-to-nat (fill-left' (add-pos-plus l m) f) ≡ fin-to-nat f
-- fill-left'-spec {zero} {zero} fzero = refl
-- fill-left'-spec {zero} {zero} (fsuc ())
-- fill-left'-spec {zero} {suc m} fzero = refl
-- fill-left'-spec {zero} {suc m} (fsuc ())
-- fill-left'-spec {suc l} {zero} fzero = refl
-- fill-left'-spec {suc l} {zero} (fsuc f) = cong suc (fill-left'-spec f)
-- fill-left'-spec {suc l} {suc m} fzero = refl
-- fill-left'-spec {suc l} {suc m} (fsuc f) = cong suc (fill-left'-spec f)

-- fill-right : {l m n : Nat} -> Add l m n -> Fin m -> Fin n
-- fill-right (add-zero n) f = f
-- fill-right (add-suc-left a) f = fsuc (fill-right a f)

-- fill-right-spec : {l m : Nat} -> (f : Fin m) -> fin-to-nat (fill-right (add-plus l m) f) ≡ l +N fin-to-nat f
-- fill-right-spec {zero} f = refl
-- fill-right-spec {suc l} f = cong suc (fill-right-spec {l} f)

-- size-one-unit : {T : Type} -> Size T 1 -> T ≡ Unit
-- size-one-unit size-unit = refl
-- size-one-unit (size-sum a s s₁) = elim-zero (add-pos-one-zero a)

-- encode : {T : Type} {st : Nat} -> Size T st -> Value T -> Fin st
-- encode size-unit v = fzero
-- encode (size-sum add-pos-one-one s t) (value-inl v) rewrite size-one-unit s = fzero
-- encode (size-sum add-pos-one-one s t) (value-inr v) rewrite size-one-unit t = fsuc fzero
-- encode (size-sum (add-pos-left a) s t) (value-inl v) = {!!}
-- encode (size-sum (add-pos-left a) s t) (value-inr v) = {!!}
-- encode (size-sum (add-pos-right a) s t) v = {!!}


-- decode : {T : Type} {st : Nat} -> Size T st -> Fin st -> Value T
-- decode = {!!}
