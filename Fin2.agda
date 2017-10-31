module Fin2 where

infix 4 _≡_
data _≡_ {A : Set} (a : A) : A -> Set where
  refl : a ≡ a
{-# BUILTIN EQUALITY _≡_ #-}

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

data Add : (l m n : Nat) -> Set where
  add-zero : (n : Nat) -> Add zero n n
  add-suc-left : {l m n : Nat} -> Add l m n -> Add (suc l) m (suc n)

add-suc-right : ∀ {l m n : Nat} -> Add l m n -> Add l (suc m) (suc n)
add-suc-right (add-zero n) = add-zero (suc n)
add-suc-right (add-suc-left a) = add-suc-left (add-suc-right a)

add-commutative : ∀ {l m n} -> Add l m n -> Add m l n
add-commutative (add-zero zero) = add-zero zero
add-commutative (add-zero (suc n)) = add-suc-left (add-commutative (add-zero n))
add-commutative (add-suc-left a) = add-suc-right (add-commutative a)

data Fin : Nat -> Set where
  fzero : ∀ {n} -> Fin (suc n)
  fsuc : ∀ {n} -> Fin n -> Fin (suc n)

data Type : Set where
  Unit : Type
--  _+_ : (S T : Type) -> Type

data Size : Type -> Nat -> Set where
  size-unit : Size Unit 1

data Value : {T : Type} {ct : Nat} -> Size T ct -> Set where
  value-unit : Value size-unit

encode : ∀ {T ct} (t : Size T ct) -> Value t -> Fin ct
encode size-unit unit = fzero

decode : ∀ {T ct} (t : Size T ct) -> Fin ct -> Value t
decode size-unit fzero = value-unit
decode size-unit (fsuc ())

encode-decode : ∀ {T ct} (t : Size T ct) (f : Fin ct) -> encode t (decode t f) ≡ f
encode-decode size-unit fzero = refl
encode-decode size-unit (fsuc ())

decode-encode : ∀ {T ct} (t : Size T ct) (v : Value t) -> decode t (encode t v) ≡ v
decode-encode size-unit value-unit = refl
