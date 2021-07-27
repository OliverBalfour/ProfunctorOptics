module Matrix
import Data.Vect
%default total

implementation {n : Nat} -> Num a => Num (Vect n a) where
  (+) a b = [| a + b |]
  (*) a b = [| a * b |]
  fromInteger i = replicate n (fromInteger i)

Matrix : {t : Type} -> Nat -> Nat -> Type
Matrix m n = Vect m (Vect n t)

--unitVector : {n : Nat} -> Nat -> Vect n Double
--unitVector i = replicate i 0 ++ [1] ++ replicate (n - i - 1) 0

-- todo: how can I generalise this to Num t => Matrix {t=t} n n?
--identity : {n : Nat} -> Matrix {t=Double} n n
--identity = fromList (map unitVector [0..(n-1)])

dot : Num a => {n : Nat} -> Vect n a -> Vect n a -> a
dot a b = sum (a * b)

main : IO ()
main = putStrLn "hello"
