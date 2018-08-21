module _ where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc) renaming (_+_ to _+ᴺ_)

id : {A : Set} → A → A
id x = x

record Inspect {A : Set} {B : A → Set} (f : (x : A) → B x) (x : A) (y : B x) : Set where
  constructor inspected
  field eq : f x ≡ y

inspect : {A : Set} {B : A -> Set} (f : (x : A) -> B x) (x : A)
  -> Inspect f x (f x)
inspect f x = inspected refl

sym : {A : Set} -> {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

cong : {A B : Set} -> (f : A -> B) -> {x y : A} -> x ≡ y -> f x ≡ f y
cong _ refl = refl

trans : {A : Set} -> {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl refl = refl

subst : {A : Set} {x y : A} (p : x ≡ y) {P : A → Set} (Px : P x) → P y
subst refl Px = Px


data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc : {n : Nat} → Fin n → Fin (suc n)

data _+ᵀ_ (A B : Set) : Set where
  inl : A → A +ᵀ B
  inr : B → A +ᵀ B

inl-injective : {A B : Set} {a1 a2 : A} → inl {A} {B} a1 ≡ inl a2 → a1 ≡ a2
inl-injective refl = refl

inr-injective : {A B : Set} {b1 b2 : B} → inr {A} {B} b1 ≡ inr b2 → b1 ≡ b2
inr-injective refl = refl

inl≢inr : {A B C : Set} {a : A} {b : B} (p : inl a ≡ inr b) → C
inl≢inr ()

+ᵀ-bimap : {A1 A2 B1 B2 : Set} (f : A1 → A2) (g : B1 → B2) (s : A1 +ᵀ B1) → A2 +ᵀ B2
+ᵀ-bimap f g (inl a1) = inl (f a1)
+ᵀ-bimap f g (inr b1) = inr (g b1)

data _×_ (A B : Set) : Set where
  pair : A → B → A × B

record Σ {A : Set} (B : A → Set) : Set where
  field
    fst : A
    snd : B fst

+ᵀ-elim : {A B C : Set} → (A → C) → (B → C) → A +ᵀ B → C
+ᵀ-elim f g (inl a) = f a
+ᵀ-elim f g (inr b) = g b

+ᵀ-elim-bimap : {A1 B1 A2 B2 C : Set} (f1 : A1 → A2) (g1 : B1 → B2) (f2 : A2 → C) (g2 : B2 → C) (s : A1 +ᵀ B1) → +ᵀ-elim f2 g2 (+ᵀ-bimap f1 g1 s) ≡ +ᵀ-elim (λ x → f2 (f1 x)) (λ x → g2 (g1 x)) s
+ᵀ-elim-bimap f1 f2 g1 g2 (inl a1) = refl
+ᵀ-elim-bimap f1 f2 g1 g2 (inr b1) = refl

record Iso (A B : Set) : Set where
  field
    encode : A → B
    decode : B → A
    left-identity : (a : A) → decode (encode a) ≡ a
    right-identity : (b : B) → encode (decode b) ≡ b

+ᵀ-bimap-inl : {A1 A2 B1 B2 : Set} (iso : Iso A1 A2) (g : B1 → B2) (s : A1 +ᵀ B1) (r : A2) → +ᵀ-bimap (Iso.encode iso) g s ≡ inl r → s ≡ inl (Iso.decode iso r)
+ᵀ-bimap-inl iso g (inl x) r p rewrite sym (inl-injective p) = cong inl (sym (Iso.left-identity iso x))
+ᵀ-bimap-inl iso g (inr x) r p = inl≢inr (sym p)

+ᵀ-bimap-inl-op : {A1 A2 B1 B2 : Set} (iso : Iso A1 A2) (g : B1 → B2) (s : A2 +ᵀ B1) (r : A1) → +ᵀ-bimap (Iso.decode iso) g s ≡ inl r → s ≡ inl (Iso.encode iso r)
+ᵀ-bimap-inl-op iso g (inl x) r p rewrite sym (inl-injective p) = cong inl (sym (Iso.right-identity iso x))
+ᵀ-bimap-inl-op iso g (inr x) r p = inl≢inr (sym p)

+ᵀ-bimap-inr : {A1 A2 B1 B2 : Set} (f : A1 → A2) (iso : Iso B1 B2) (s : A1 +ᵀ B1) (r : B2) → +ᵀ-bimap f (Iso.encode iso) s ≡ inr r → s ≡ inr (Iso.decode iso r)
+ᵀ-bimap-inr f iso (inl x) r p = inl≢inr p
+ᵀ-bimap-inr f iso (inr x) r p rewrite sym (inr-injective p) = cong inr (sym (Iso.left-identity iso x))

+ᵀ-bimap-inr-op : {A1 A2 B1 B2 : Set} (f : A1 → A2) (iso : Iso B1 B2) (s : A1 +ᵀ B2) (r : B1) → +ᵀ-bimap f (Iso.decode iso) s ≡ inr r → s ≡ inr (Iso.encode iso r)
+ᵀ-bimap-inr-op f iso (inl x) r p = inl≢inr p
+ᵀ-bimap-inr-op f iso (inr x) r p rewrite sym (inr-injective p) = cong inr (sym (Iso.right-identity iso x))

record IsoSplit (A1 A2 B : Set) : Set where
  field
    embed1 : A1 → B
    embed2 : A2 → B
    split : B → A1 +ᵀ A2
    preserve1 : ∀ a1 → split (embed1 a1) ≡ inl a1
    preserve2 : ∀ a2 → split (embed2 a2) ≡ inr a2
    preserveB : ∀ b → +ᵀ-elim embed1 embed2 (split b) ≡ b

isoSplit-to-iso : {A1 A2 B : Set} → IsoSplit A1 A2 B → Iso (A1 +ᵀ A2) B
isoSplit-to-iso {A1} {A2} {B} record { embed1 = embed1 ; embed2 = embed2 ; split = split ; preserve1 = preserve1 ; preserve2 = preserve2 ; preserveB = preserveB }
  = record
  { encode = encode
  ; decode = decode
  ; left-identity = left-identity
  ; right-identity = right-identity
  }
  where
  encode : (x : A1 +ᵀ A2) → B
  encode (inl a1) = embed1 a1
  encode (inr a2) = embed2 a2

  decode : (b : B) → A1 +ᵀ A2
  decode b = split b

  left-identity : (x : A1 +ᵀ A2) → split (encode x) ≡ x
  left-identity (inl a1) = preserve1 a1
  left-identity (inr a2) = preserve2 a2

  right-identity : (b : B) → encode (split b) ≡ b
  right-identity b with split b | inspect split b
  right-identity b | inl a1 | inspected eq = trans (sym (cong (+ᵀ-elim embed1 embed2) eq)) (preserveB b) 
  right-identity b | inr a2 | inspected eq = trans (sym (cong (+ᵀ-elim embed1 embed2) eq)) (preserveB b)

expand-fin : {m : Nat} -> Fin m -> (n : Nat) -> Fin (m +ᴺ n)
expand-fin fzero    n = fzero
expand-fin (fsuc f) n = fsuc (expand-fin f n)

shift-fin : (m : Nat) -> {n : Nat} -> Fin n -> Fin (m +ᴺ n)
shift-fin zero    f = f
shift-fin (suc m) f = fsuc (shift-fin m f)

shift-fin-inl : {m n : Nat} → Fin m +ᵀ Fin n → Fin (suc m) +ᵀ Fin n
shift-fin-inl (inl x) = inl (fsuc x)
shift-fin-inl (inr y) = inr y

split-fin : (m : Nat) {n : Nat} (f : Fin (m +ᴺ n)) → Fin m +ᵀ Fin n
split-fin zero f = inr f
split-fin (suc m) fzero = inl fzero
split-fin (suc m) (fsuc f) = shift-fin-inl (split-fin m f)

split-fin-after-expand-fin : {m : Nat} -> (f : Fin m) -> (n : Nat) -> split-fin m (expand-fin f n) ≡ inl f
split-fin-after-expand-fin fzero n = refl
split-fin-after-expand-fin (fsuc f) n = cong shift-fin-inl (split-fin-after-expand-fin f n)

split-fin-after-shift-fin : (m : Nat) -> {n : Nat} -> (f : Fin n) -> split-fin m (shift-fin m f) ≡ inr f
split-fin-after-shift-fin zero f = refl
split-fin-after-shift-fin (suc m) f = cong shift-fin-inl (split-fin-after-shift-fin m f)

split-fin-left-expand-fin : {m n : Nat}
  -> (x : Fin (m +ᴺ n))
  -> (y : Fin m)
  -> split-fin m x ≡ inl y
  -> x ≡ expand-fin y n
split-fin-left-expand-fin {zero} x y ()
split-fin-left-expand-fin {suc m} fzero .fzero refl = refl
split-fin-left-expand-fin {suc m} (fsuc x) y p with split-fin m x | inspect (split-fin m) x
split-fin-left-expand-fin {suc m} {n} (fsuc x) y p | inl z | inspected eq =
  trans
    (cong fsuc (split-fin-left-expand-fin x z eq))
    (sym (cong (λ a → expand-fin a n) (inl-injective (sym p))))
split-fin-left-expand-fin {suc m} (fsuc x) y () | inr _ | inspected eq

split-fin-right-shift-fin : {m n : Nat}
  -> (x : Fin (m +ᴺ n))
  -> (y : Fin n)
  -> split-fin m x ≡ inr y
  -> shift-fin m y ≡ x
split-fin-right-shift-fin {zero} x y p = sym (inr-injective p)
split-fin-right-shift-fin {suc m} fzero y ()
split-fin-right-shift-fin {suc m} (fsuc x) y p with split-fin m x | inspect (split-fin m) x
split-fin-right-shift-fin {suc m} (fsuc x) y () | inl _ | inspected eq
split-fin-right-shift-fin {suc m} (fsuc x) y p | inr z | inspected eq =
  cong fsuc
    (trans
      (cong (shift-fin m) (inr-injective (sym p)))
      (split-fin-right-shift-fin x z eq))

iso-sum-fin
  : ∀ {A B na nb}
  → Iso A (Fin na)
  → Iso B (Fin nb)
  → IsoSplit A B (Fin (na +ᴺ nb))
iso-sum-fin {A} {B} {na} {nb}
  isoA @ record { encode = encodeA ; decode = decodeA ; left-identity = left-identityA ; right-identity = right-identityA }
  isoB @ record { encode = encodeB ; decode = decodeB ; left-identity = left-identityB ; right-identity = right-identityB }
  =
  record
  { embed1 = embed1
  ; embed2 = embed2
  ; split = split
  ; preserve1 = preserve1
  ; preserve2 = preserve2
  ; preserveB = preserveB
  }
  where
  embed1 : (x : A) → Fin (na +ᴺ nb)
  embed1 x = expand-fin (encodeA x) nb

  embed2 : (x : B) → Fin (na +ᴺ nb)
  embed2 x = shift-fin na (encodeB x)

  split : Fin (na +ᴺ nb) → A +ᵀ B
  split f = +ᵀ-bimap decodeA decodeB (split-fin na f)

  preserve1 : ∀ a → split (embed1 a) ≡ inl a
  preserve1 a rewrite split-fin-after-expand-fin (encodeA a) nb | left-identityA a = refl

  preserve2 : ∀ b → split (embed2 b) ≡ inr b
  preserve2 b rewrite split-fin-after-shift-fin na (encodeB b) | left-identityB b = refl

  preserveB : ∀ f → +ᵀ-elim embed1 embed2 (split f) ≡ f
  preserveB f with split f | inspect split f
  preserveB f | inl a | inspected eq = sym (split-fin-left-expand-fin f (encodeA a) (+ᵀ-bimap-inl-op isoA decodeB (split-fin na f) a eq))
  preserveB f | inr b | inspected eq = split-fin-right-shift-fin f (encodeB b) (+ᵀ-bimap-inr-op decodeA isoB (split-fin na f) b eq) 
