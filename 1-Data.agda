module 1-Data where




data Bool : Set where -- George Boole, 1847
  true : Bool
  false : Bool

-- C-c C-n true
-- true

-- C-c C-d true
-- Bool


not : Bool -> Bool
not true = false
not false = true


-- C-c C-n not true
-- false


_and_ : Bool -> Bool -> Bool
_and_ true true = true
_and_ _ _ = false


-- C-c C-n _and_ true false
-- false
-- C-c C-n _and_ true
-- _and_ true
-- C-c C-d _and_ true
-- Bool → Bool


-- C-c C-n true and false
-- false

_or_ : Bool -> Bool -> Bool
false or false = false
_ or _ = true


-- C-c C-n not (((true and true) or (false and true)) and (not false))
-- false



-- data Nat : Set where
--   n1 : Nat
--   n2 : Nat
--   n3 : Nat
--   n4 : Nat
--   n5 : Nat
--   n6 : Nat
--   -- not fun at all

-- inductive set
data Nat : Set where --  Giuseppe Peano, 1889
  nz : Nat -- 0, zero, base case
  nn : Nat -> Nat -- 1 + n, non-zero, induction step

-- nn (nn (nn (nn nz))) -- 1 + 1 + 1 + 1 + 0

n1 = nn nz
n2 = nn n1
n3 = nn n2
n4 = nn n3

-- structural recursion
even? : Nat -> Bool
even? nz = true  -- base case
even? (nn n) = not (even? n) -- 1 + n, induction step

-- C-c C-n even? n3
-- even? (nn (nn (nn nz)))
-- not (not (not true))
-- false


-- structural recursion by left argument
_+_ : Nat -> Nat -> Nat
nz + m = m -- 0 + m = m
(nn n) + m = n + (nn m) -- (1 + n) + m = n + (1 + m)

-- C-c C-n n2 + n1
-- (nn (nn nz)) + (nn nz)
-- (nn nz) + (nn (nn nz))
-- nz + (nn (nn (nn nz)))
-- n3

-- structural recursion by right argument
_+:_ : Nat -> Nat -> Nat
m +: nz = m
m +: (nn n) = (nn m) + n

-- C-c C-n n2 +: n1
-- (nn (nn nz)) +: (nn nz)
-- (nn (nn (nn nz))) +: nz
-- n3



_equal_ : Nat -> Nat -> Bool
-- n eq n = true -- can't write this
nz equal nz = true -- 0 = 0
(nn n) equal nz = false -- (1 + n) != 0
nz equal (nn m) = false
(nn n) equal (nn m) = n equal m -- (1 + n) ?= (1 + m) -> n = m


double : Nat -> Nat
double n = n + n

n16 = (double (double (double n2)))

half : Nat -> Nat
half nz = nz
half (nn nz) = nz -- Can't omit this case
half (nn (nn n)) = nn (half n) -- half (2 + n) = 1 + half n

-- half' : Nat -> Nat
-- half' n = if (even? n) then (half n) else ?

-- Olimp WIFI
-- itiktitikt
-- proxy.ifmo.ru:3128

-- We need to pass a proof!


-- 26min
