
module Matrix

import Data.Vect

dot : Num a => Vect n a -> Vect n a -> a
dot a b = foldr (+) 0 ((*) <$> a <*> b)

Num a => Num (Vect n a) where
  (+) Nil Nil = Nil
  (+) (x :: xs) (y :: ys) = x + y :: xs + ys
  (*) Nil Nil = Nil
  (*) (x :: xs) (y :: ys) = x * y :: xs * ys
  fromInteger i = replicate (fromInteger i) n

-- namespace Vect
--   (+) : Num a => Vect n a -> Vect n a -> Vect n a
--   (+) Nil Nil = Nil
--   (+) (x :: xs) (y :: ys) = x + y :: dot xs ys
--
-- namespace Matrix
--   (+) : Num a => Vect n (Vect m a) -> Vect n (Vect m a) -> Vect n (Vect m a)
--   (+) Nil Nil = Nil
--   (+) (x :: xs) (y :: ys) = x + y :: xs + ys

-- data Matrix : Nat -> Nat -> Type -> Type where
--   Matrix : {a: Type} -> (n: Nat) -> (m: Nat) -> Vect n (Vect m a)

-- matmul : Matrix m n a -> Matrix n p a -> Matrix m p a
-- matmul {m} {n} {p} (a :: as) (b :: bs) =  :: matmul as bs

-- idea: data Matrix with Num instance?

-- idea: define Vect as a Functor and

-- Looks like this is in Data.Vect.replicate too
repeat : a -> (n: Nat) -> Vect n a
repeat x 0 = fromList []
repeat x (S n) = x :: repeat x n
