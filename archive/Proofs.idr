
module Proofs

%default total

-- Exercise 1: + is commutative

plusRightId : (x : Nat) -> x + 0 = x
plusRightId Z = Refl
plusRightId (S x) =
  let iH = plusRightId x
  in rewrite iH in Refl

succInjective : (x, y : Nat) -> S x = S y -> x = y
succInjective _ _ Refl = Refl

lemma : (x, y : Nat) -> S (plus x y) = plus x (S y)
lemma Z y = Refl
lemma (S x) y =
  let iH = lemma x y
  in rewrite iH in Refl

plusComm : (x, y : Nat) -> x + y = y + x
plusComm Z y = rewrite plusRightId y in Refl
plusComm (S x) y =
  let iH = plusComm x y
  in rewrite iH
  in lemma y x

-- Exercise 2: reverse functions extensional equality

rev1 : List a -> List a
rev1 [] = []
rev1 (x::xs) = rev1 xs ++ [x]

shunt : List a -> List a -> List a
shunt [] ys = ys
shunt (x::xs) ys = shunt xs (x::ys)

rev2 : List a -> List a
rev2 xs = shunt xs []

lemma6 : (xs, ys, zs : List a) -> (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
lemma6 [] ys zs = Refl
lemma6 (x::xs) ys zs =
  let iH = lemma6 xs ys zs in rewrite iH in Refl

lemma4 : (xs, ys : List a) -> rev1 xs ++ ys = shunt xs ys
lemma4 [] _ = Refl
lemma4 (x::xs) ys =
  let iH = lemma4 xs (x::ys)
      prf = lemma6 (rev1 xs) [x] ys
  in rewrite prf in iH

revTrEq : (xs : List a) -> rev1 xs = rev2 xs
revTrEq [] = Refl
revTrEq (x::xs) = lemma4 xs [x]

-- Exercise 3: rev injective

-- note: rev1 is the inefficient one
rev1Lemma : (y : a) -> (xs : List a) -> y :: rev1 xs = rev1 (xs ++ [y])
rev1Lemma _ [] = Refl
rev1Lemma y (x::xs) =
  let iH = rev1Lemma y xs
  in rewrite cong (++[x]) iH
  in Refl

rev1Involution : (xs : List a) -> xs = rev1 (rev1 xs)
rev1Involution [] = Refl
rev1Involution (x::xs) =
  let iH = rev1Involution xs
      shed = cong (x::) iH
  in rewrite shed
  in rev1Lemma x (rev1 xs)

rev1Injective : (xs, ys : List a) -> rev1 xs = rev1 ys -> xs = ys
rev1Injective xs ys prf =
  rewrite rev1Involution xs
  in rewrite rev1Involution ys
  in cong rev1 prf

rev2Injective : (xs, ys : List a) -> rev2 xs = rev2 ys -> xs = ys
rev2Injective xs ys prf =
  let step1 : (rev2 xs = rev1 ys) = trans prf (sym (revTrEq ys))
      step2 : (rev1 xs = rev1 ys) = trans (revTrEq xs) step1
  in rev1Injective xs ys step2
