module 3a-Parity where

data Nat : Set where
  nz : Nat
  nn : Nat -> Nat

n2 = nn (nn nz)
n4 = nn (nn n2)

_+_ : Nat -> Nat -> Nat
nz + m = m
nn n + m = nn (n + m)


double : Nat -> Nat
double nz = nz
double (nn n) = nn (nn (double n))



data EvenOdd : Nat -> Set where
  even : (n : Nat) -> EvenOdd (double n)
  odd : (n : Nat) -> EvenOdd (nn (double n))


eo-rec : forall n -> EvenOdd n -> EvenOdd (nn n)
eo-rec .(double k) (even k) = odd k
eo-rec .(nn (double k)) (odd k) = even (nn k)

eo : forall n -> EvenOdd n
eo nz = even nz
eo (nn n) = eo-rec n (eo n)
