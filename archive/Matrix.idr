module Matrix

import Data.Vect
import Data.Fin

%default total

infixl 10 <@>
--infixl 10 .

implementation {n : Nat} -> Num a => Num (Vect n a) where
  (+) a b = [| a + b |]
  (*) a b = [| a * b |]
  fromInteger i = replicate n (fromInteger i)

Matrix : {t : Type} -> Nat -> Nat -> Type
Matrix m n = Vect m (Vect n t)

unitVector : {n : Nat} -> (_ : Fin n) -> Vect n Double
unitVector i = updateAt i (const 1) (replicate n 0)

enumerateFin : (n : Nat) -> Vect n (Fin n)
enumerateFin n = reverse (impl n) where
  impl : (n : Nat) -> Vect n (Fin n)
  impl 0 = []
  impl (S k) = the (Fin (S k)) last :: map weaken (impl k)

-- Generate an T^(m×n) matrix with a function Fin m × Fin n -> T
matrix : {t : Type} -> (m : Nat) -> (n : Nat) -> (Nat -> Nat -> t) -> Matrix {t=t} m n
matrix 0 n f = []
matrix (S m) n f = row (S m) n f :: matrix m n f where
  row : {t : Type} -> (m : Nat) -> (n : Nat) -> (Nat -> Nat -> t) -> Vect n t
  row m 0 f = []
  row m (S n) f = f m (S n) :: row m n f

forceNatToFin : {n : Nat} -> Nat -> Fin n
forceNatToFin i = case natToFin i n of
  Just x => x
  Nothing => ?ignore

-- Generate an T^(m×n) matrix with a function Fin m × Fin n -> T
matrix2 : (m : Nat) -> (n : Nat) -> (Fin m -> Fin n -> Double) -> Matrix {t=Double} m n
matrix2 0 n f = []
matrix2 (S m) n f = let f' = \i => \j => f (weaken i) j in row (S m) n f :: matrix2 m n f' where
  row : (m : Nat) -> (n : Nat) -> (Fin m -> Fin n -> Double) -> Vect n Double
  row m 0 f = []
  row m n@(S n') f =
    let f' : Fin m -> Fin n' -> Double
        f' i j = f i (weaken j)
    in f (forceNatToFin m) (forceNatToFin n) :: row m n' f'
--    in f (the (Fin m) last) (the (Fin n) last) :: row m n' f'
--  row m (S n) f = f (the (Fin m) 0) (S n) :: row m n (\i => \j => f i (weaken j))

identity : {n : Nat} -> Matrix {t=Double} n n
-- identity = map unitVector (enumerateFin n)
identity = matrix n n (\i, j => if i == j then 1 else 0)

dot : Num a => {n : Nat} -> Vect n a -> Vect n a -> a
dot a b = sum (a * b)

transpose : {m : Nat} -> {n : Nat} -> Matrix {t=Double} m n -> Matrix {t=Double} n m
transpose x = matrix2 n m (\i, j => i `index` (j `index` x))
--  let rows = toList $ enumerateFin n
--      cols = toList $ enumerateFin m
--  in fromList [fromList [i `index` (j `index` x) | j <- cols] | i <- rows]

--(.) : Num a => {n : Nat} -> Vect n a -> Vect n a -> a
--(.) = dot

norm : {n : Nat} -> Vect n Double -> Double
norm x = sqrt (sum (x * x))

(<@>) : {t : Type} -> {m,n,p : Nat} -> Num t => Matrix {t=t} m n -> Matrix {t=t} n p -> Matrix {t=t} m p
(<@>) x y =
  let y' = transpose y
  in map (\row => map (dot row) y') x
