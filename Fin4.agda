module _ where

open import Agda.Builtin.Nat
  using (Nat; zero; suc)
  renaming (_+_ to _+N_)

open import Agda.Builtin.FromNat

data False : Set where
record True : Set where
  constructor true

data Fin : Nat -> Set where
  fz : {n : Nat} -> Fin (suc n)
  fs : {n : Nat} -> Fin n -> Fin (suc n)

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

data Vec (A : Set) : Nat -> Set where
  nil : Vec A zero
  _::_ : A -> {n : Nat} -> Vec A n -> Vec A (suc n)
infixr 5 _::_

index-at : {n : Nat} -> Fin n -> {A : Set} -> Vec A n -> A
index-at fz     (x :: _) = x
index-at (fs i) (_ :: xs) = index-at i xs

data Type : Set where
  Unit : Type
  Sum : {n : Nat} -> Vec Type n -> Type

data Value : Type -> Set where
  unit : Value Unit
  choose : {n : Nat} -> (f : Fin n) -> {v : Vec Type n} -> Value (index-at f v) -> Value (Sum v)

module Ex where
  3-Unit : Type
  3-Unit = Sum (Unit :: Unit :: Unit :: nil)

  sum : Value 3-Unit
  sum = choose 0 unit

  sum2 : Value 3-Unit
  sum2 = choose 1 unit
  
