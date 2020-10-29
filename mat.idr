
module Matrix

import Data.Vect

dot : Num a => Vect n a -> Vect n a -> Vect n a
dot Nil Nil = Nil
dot (x :: xs) (y :: ys) = (x * y) :: (dot xs ys)

namespace Vect
  (+) : Num a => Vect n a -> Vect n a -> Vect n a
  (+) Nil Nil = Nil
  (+) (x :: xs) (y :: ys) = x + y :: dot xs ys

namespace Matrix
  (+) : Num a => Vect n (Vect m a) -> Vect n (Vect m a) -> Vect n (Vect m a)
  (+) Nil Nil = Nil
  (+) (x :: xs) (y :: ys) = x + y :: xs + ys

-- data Matrix : Nat -> Nat -> Type -> Type where
--   Matrix : {a: Type} -> (n: Nat) -> (m: Nat) -> Vect n (Vect m a)

-- matmul : Matrix m n a -> Matrix n p a -> Matrix m p a
-- matmul {m} {n} {p} (a :: as) (b :: bs) =  :: matmul as bs

-- idea: data Matrix with Num instance?

-- idea: define Vect as a Functor and
