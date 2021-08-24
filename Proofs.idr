
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
-- shunt xs [] = xs
-- shunt xs (y::ys) = shunt (y::xs) ys
shunt [] ys = ys
shunt (x::xs) ys = shunt xs (x::ys)

rev2 : List a -> List a
rev2 xs = shunt xs []

lemma3 : (xs, ys : List a) -> (x : a) -> (xs ++ [x]) ++ ys = xs ++ (x :: ys)

-- lemma2 : (xs, ys : List a) -> rev1 xs ++ ys = shunt ys xs
-- lemma2 [] ys = Refl
-- lemma2 (x::xs) ys =
--   let iH = lemma2 xs ys
--   in ?help  -- rewrite lemma3 (rev1 xs) ys x in ?help

nilRightIdConcat : (xs : List a) -> xs ++ [] = xs
nilRightIdConcat [] = Refl
nilRightIdConcat (x::xs) = rewrite nilRightIdConcat xs in Refl

-- shuntLemma : (xs, ys, zs : List a) -> shunt zs xs ++ ys = shunt (zs ++ ys) xs
-- -- shuntLemma [] ys zs = Refl
-- -- shuntLemma (x::xs) ys zs =
-- --   let iH = shuntLemma xs ys zs
-- --   in ?help

-- -- shuntLemma xs [] zs =
-- --   rewrite nilRightIdConcat (shunt zs xs) in
-- --     rewrite nilRightIdConcat zs in
-- --       Refl
-- -- shuntLemma xs (y::ys) zs =
-- --   let iH = shuntLemma xs ys zs in ?help

-- shuntLemma xs ys [] = ?help
-- shuntLemma xs ys (z::zs) =
--   let iH = shuntLemma xs ys zs
--   in ?help2

lemma2 : (xs, ys : List a) -> shunt xs ys = shunt xs [] ++ ys
lemma2 [] ys = Refl
lemma2 (x::xs) [] = rewrite nilRightIdConcat (shunt xs [x]) in Refl
lemma2 (x::xs) (y::ys) =
  let iH = lemma2 xs ys
  in ?help3
-- lemma2 xs [] = rewrite nilRightIdConcat (shunt [] xs) in Refl
-- lemma2 xs' (y::ys) =
--   let iH = lemma2 xs' ys
--   in case xs' of
--     [] => Refl
--     (x::xs) => ?help

lemma5 : (xs : List a) -> (x : a) -> [x] ++ xs = x :: xs
lemma5 xs x = Refl

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
rev1Injective : (xs, ys : List a) -> rev1 xs = rev1 ys -> xs = ys

