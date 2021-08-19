
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
shunt xs [] = xs
shunt xs (y::ys) = shunt (y::xs) ys

rev2 : List a -> List a
rev2 xs = shunt [] xs

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

lemma2 : (xs, ys : List a) -> shunt [] xs ++ ys = shunt ys xs
lemma2 [] ys = Refl
lemma2 (x::xs) ys =
  let iH = lemma2 xs ys
  in ?help
-- lemma2 xs [] = rewrite nilRightIdConcat (shunt [] xs) in Refl
-- lemma2 xs' (y::ys) =
--   let iH = lemma2 xs' ys
--   in case xs' of
--     [] => Refl
--     (x::xs) => ?help

revExtEq : (xs : List a) -> rev1 xs = rev2 xs
revExtEq [] = Refl
revExtEq (x::xs) =
  let iH = revExtEq xs
  in rewrite iH
  in lemma2 xs [x] -- shuntLemma xs [x] []
