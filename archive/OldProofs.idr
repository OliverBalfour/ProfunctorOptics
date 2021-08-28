module OldProofs
import Data.List
%default total


orDistributesOverAnd : (p, q, r : Type)
                    -> (Either p (q, r) -> (Either p q, Either p r),
                        (Either p q, Either p r) -> Either p (q, r))
-- orDistributesOverAnd = ?help
-- orDistributesOverAnd = (?t1, ?t2)
orDistributesOverAnd p q r = (lhs, rhs)
  where

    lhs : Either p (q, r) -> (Either p q, Either p r)
    lhs (Left p) = (Left p, Left p)
    lhs (Right (q, r)) = (Right q, Right r)

    rhs : (Either p q, Either p r) -> Either p (q, r)
    rhs (Left p, _) = Left p
    rhs (Right q, Left p) = Left p
    rhs (Right q, Right r) = Right (q, r)

rev1 : List a -> List a
rev1 [] = []
rev1 (x :: xs) = rev1 xs ++ [x]

shift : List a -> List a -> List a
shift xs [] = xs
shift xs (y::ys) = shift (y::xs) ys

rev2 : List a -> List a
rev2 xs = shift [] xs

nilRightIdentity : (xs : List a) -> xs ++ [] = xs
nilRightIdentity [] = Refl
nilRightIdentity (x::xs) =
  let iH = nilRightIdentity xs
  in rewrite iH in Refl

lemma1 : (xs, ys : List a) -> rev1 xs ++ ys = shift ys xs
lemma1 xs [] = rewrite appendNilRightNeutral (rev1 xs) in revsExtensionallyEqual
lemma1 xs (y::ys) =
  let iH = lemma1 xs ys
  in ?help3

revsExtensionallyEqual : (x : List a) -> rev1 x = rev2 x
revsExtensionallyEqual [] = Refl
revsExtensionallyEqual (x::xs) =
  let iH = revsExtensionallyEqual xs
  in ?help
