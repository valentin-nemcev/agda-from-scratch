module 4-Equality where

data Nat : Set where
  nz : Nat
  nn : Nat -> Nat

n1 = nn nz
n2 = nn n1
n3 = nn n2
n4 = nn n3

data Even : Nat -> Set where -- Indexed type
  enz : Even nz
  enn : {n : Nat} -> Even n -> Even (nn (nn n)) -- Constructor has implicit argument

en4 : Even n4
en4 = enn (enn enz)
_+_ : Nat -> Nat -> Nat
nz + b = b
nn a + b = nn (a + b)

double : Nat -> Nat
double n = n + n

data _==_ : Nat -> Nat -> Set where
  equals : {n : Nat} -> n == n


2+2=4 : (n2 + n2) == n4
2+2=4 = equals



-- Congruence
==-cong : forall {a b : Nat} ->
    (f : Nat -> Nat) -> a == b -> f a == f b
==-cong f equals = equals

_~_ : forall {a b c} -> a == b -> b == c -> a == c
_~_ equals equals = equals


n=n+0 : forall b -> b == (b + nz)
n=n+0 nz = equals
n=n+0 (nn b) = ==-cong nn (n=n+0 b)

nn+n=n+nn : forall b a -> (nn b + a) == (b + nn a)
nn+n=n+nn nz a = equals
nn+n=n+nn (nn b) a = ==-cong nn (nn+n=n+nn b a)

+-comm : forall a b -> (a + b) == (b + a)
+-comm nz b = n=n+0 b
+-comm (nn a) b = ==-cong nn (+-comm a b ) ~ nn+n=n+nn b a

-- nn (a + b) == (b + nn a)

-- nn (a + b) == nn (b + a)  (nn b + a) == (b + nn a)
--
-- n=n+0 : forall b -> b == (b + nz)
-- n=n+0 nz = equals
-- n=n+0 (nn b) = ==-cong nn (n=n+0 b)
--
-- nn+n=n+nn : forall b a -> (nn b + a) == (b + nn a)
-- nn+n=n+nn nz a = equals
-- nn+n=n+nn (nn b) a = ==-cong nn (nn+n=n+nn b a)
--
-- +-comm : forall a b -> (a + b) == (b + a)
-- +-comm nz b = n=n+0 b
-- +-comm (nn a) b = ==-cong nn (+-comm a b) ~ nn+n=n+nn b a

-- (nn a + b) == (b + nn a)
-- _+_
-- nn (a + b) == (b + nn a)

-- a                        b                c
-- nn (a + b) == nn (b + a)  (nn b + a) == (b + nn a)



==-sym : forall {a b} -> a == b -> b == a
==-sym equals = equals


double' : Nat -> Nat
double' nz = nz
double' (nn n) = nn (nn (double' n)) -- This form is better for induction

double-even' : forall n -> Even (double' n)
double-even' nz = enz
double-even' (nn n) = enn (double-even' n) -- Easy proof



double'=double : forall n -> double' n == double n
double'=double nz = equals
double'=double (nn n) = ==-cong nn (==-cong nn (double'=double n)
                                    ~ (nn+n=n+nn n n))

-- Similar to congruence but for propositions
==-subst : forall {a b} (P : Nat -> Set) 
      -> P a -> a == b -> P b
==-subst P p equals = p

double-even : forall n -> Even (double n)
double-even n =
  ==-subst Even (double-even' n) (double'=double n)
