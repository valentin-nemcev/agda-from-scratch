module 3-Indexed where

data Nat : Set where
  nz : Nat
  nn : Nat -> Nat

n1 = nn nz
n2 = nn n1
n3 = nn n2
n4 = nn n3

_+_ : Nat -> Nat -> Nat
nz + b = b
nn a + b = nn (a + b)


data Even : Nat -> Set where -- Indexed type
  enz : Even nz
  enn : {n : Nat} -> Even n -> Even (nn (nn n))
  -- Constructor has implicit argument

-- en4 : Even (nn (nn (nn (nn nz))))
en4 : Even n4
en4 = enn (enn enz)


-- en3 : Even n3
-- en3 = ? -- Can't construct this


-- nat-to-even : (n : Nat) -> Even n -- Can't do this, won't be total


even-to-nat : {n : Nat} -> Even n -> Nat
even-to-nat {x} _ = x


e+e=e : (n m : Nat) -> Even n -> Even m -> Even (n + m)
e+e=e nz m _ em = em
e+e=e (nn nz) m ()
e+e=e (nn (nn n)) m (enn en) em = enn (e+e=e n m en em)


-- e+e=e nz m enz em = em
-- e+e=e (nn nz) m ()
-- e+e=e (nn (nn n)) m (enn en) em = enn (e+e=e n m en em)


-- e+e=e' : (n m : _) -> Even n -> Even m -> Even (n + m)
e+e=e' : forall n m -> Even n -> Even m -> Even (n + m)
e+e=e' = e+e=e



-- -> is logical implication

true-implies-true : Set -> Set
true-implies-true a = a

data Void : Set where

false-implies-anything : Void -> Set
false-implies-anything _ = Nat -- Could be any type that has values


data _And_ : Set -> Set -> Set where
  pair : {A B : Set} -> A -> B -> A And B

a-and-b->a : {A B : Set} -> A And B -> A
a-and-b->a (pair a b) = a

-- 47min
