module Fin where

open import Agda.Builtin.Nat
  using (Nat; zero; suc)
import Agda.Builtin.Nat as Nat

open import Agda.Builtin.Equality

data _+N_ : (n m : Nat) -> Set where
  zero+m : (m : Nat) -> zero +N m
  suc+m : (n m : Nat) -> n +N m -> (suc n) +N m

eval+N : (n m : Nat) -> n +N m -> Nat
eval+N .0       m (zero+m .m) = m
eval+N .(suc n) m (suc+m n .m e) = suc (eval+N n m e)

eval+N≡Nat+ : (n m : Nat) -> (e : n +N m) -> eval+N n m e ≡ n Nat.+ m
eval+N≡Nat+ .0 m (zero+m .m) = refl
eval+N≡Nat+ .(suc n) m (suc+m n .m e) rewrite eval+N≡Nat+ n m e = refl

data NatExp : Set where
  lit  : Nat            -> NatExp
  _+E_ : (n m : NatExp) -> NatExp

⟦_⟧ : NatExp -> Nat
⟦ lit x ⟧ = x
⟦ e1 +E e2 ⟧ = ⟦ e1 ⟧ Nat.+ ⟦ e2 ⟧


data Fin : Nat -> Set where
  fzero : (n : Nat)          -> Fin (suc n)
  fsuc  : (n : Nat) -> Fin n -> Fin (suc n)

data _+_ (A B : Set) : Set where
  inl : A -> A + B
  inr : B -> A + B

data _×_ (A B : Set) : Set where
  pair : A -> B -> A × B
