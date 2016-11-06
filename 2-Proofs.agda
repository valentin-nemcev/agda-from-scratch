module 2-Proofs where

data Bool : Set where
  true : Bool
  false : Bool

data Nat : Set where
  nz : Nat
  nn : Nat -> Nat

n1 = nn nz
n2 = nn n1
n3 = nn n2
n4 = nn n3




-- True proposition
n42 : Nat -- Nat has constructors, so it should be True
-- Proof:
n42 = n1 -- here, we can prove that Nat has at least one value



-- Type without constructors
data Void : Set where -- bottom
  -- nothing here

-- False proposition?
-- n43 : Void -- Void has no values
-- n43 = ?? -- can't prove false propostions


data True : Set where
  tt : True -- don't care about the name, just that we have one constructor

TrueIsTrue : True
TrueIsTrue = tt -- yep

BoolIsTrue : Bool
BoolIsTrue = false -- yep, it's a true proposition

-- voidIsFalse : Void -- still can't prove this

-- Not : Set -> Set
-- Not Void = True -- can't pattern match on types
-- Not _ = Void

-- function that returns types
Even? : Nat -> Set
-- Even? nz = true -- Type error: Bool is not Set
Even? nz = True
-- Even? (nn nz) = not (Even? nz) -- Type error
-- Even? (nn nz) = Not (Even? nz) -- Can't define Not for types
Even? (nn nz) = Void
Even? (nn (nn n)) = Even? n -- 2 + n -> Even? n

n2-even : Even? n2 -- True
n2-even = tt -- yep, it's even, this program passes type check

-- n3-even : Even? n3
-- n3-even = tt -- ha-ha, no, type error
-- still can't prove 3 is not even



half : (n : Nat) -> Even? n -> Nat -- Dependent type
half nz tt = nz
half (nn nz) () -- () means no value
half (nn (nn x)) e = nn (half x e) -- x and n are in different scope

-- C-c C-n half n4 tt
-- n2

-- C-c C-n half n3 tt
-- Type error

-- C-c C-d half n3
-- Void → Nat

-- C-c C-d half n2
-- True → Nat


-- Dependent types

id : (A : Set) -> A -> A
id _ x = x

-- C-c C-d id Bool
-- Bool → Bool

-- C-c C-n id Nat n2
-- n2

-- C-c C-n id Nat false
-- Type error

-- C-c C-n id _ false
-- false

-- Implicit arguments

id-impl : {A : Set} -> A -> A
id-impl x = x

-- C-c C-n id-impl false
-- false
-- 27 min
