module 5-Rewrite where

data Nat : Set where
  nz : Nat
  nn : Nat -> Nat

n2 = nn (nn nz)
n4 = nn (nn n2)

_+_ : Nat -> Nat -> Nat
nz + m = m
nn n + m = nn (n + m)


data _==_ {l : _} : {A : Set l} -> A -> A -> Set l where
  refl : {A : Set l} {a : A} -> a == a

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}

==-sym : forall {l} {A : Set l} {a b : A} -> a == b -> b == a
==-sym refl = refl

==-cong : forall {A B : Set} {a b : A} (f : A -> B) -> a == b -> (f a) == (f b)
==-cong f refl = refl

==-subst : forall {l} {A : Set l} {a b : A} (P : A -> Set) -> P a -> a == b -> P b
==-subst _ p refl = p

==-subst' : forall {l} {A : Set l} {a b} {P : A -> Set}  -> P a -> a == b -> P b
==-subst' p refl = p

_~_ : forall {A : Set} {a b c : A} -> a == b -> b == c -> a == c
refl ~ refl = refl

nn+n=n+nn : forall a' b' -> (nn a' + b') == (a' + nn b')
nn+n=n+nn nz b' = refl
nn+n=n+nn (nn a') b'  = ==-cong nn (nn+n=n+nn a' b')


double : Nat -> Nat
double n = n + n

half : Nat -> Nat
half nz = nz
half (nn nz) = nz
half (nn (nn n)) = nn (half n)

double' : Nat -> Nat
double' nz = nz
double' (nn n) = nn (nn (double' n))

double'=double : forall n -> double' n == double n
double'=double nz = refl
double'=double (nn n) = ==-cong nn (==-cong nn (double'=double n)
                                    ~ (nn+n=n+nn n n))


dh' : forall n -> half (double' n) == n
dh' nz = refl
dh' (nn n) = ==-cong nn (dh' n)

dh-rewrite : Nat -> Nat -> Set
dh-rewrite n d = half (d) == n

dh : forall n -> half (double n) == n
dh n = ==-subst (dh-rewrite n) (dh' n) (double'=double n)


dh2 : forall n -> half (double n) == n
dh2 n with (double n) | double'=double n
... | _ | refl = dh' n

dh3 : forall n -> half (double n) == n
dh3 n rewrite (==-sym (double'=double n)) = dh' n
