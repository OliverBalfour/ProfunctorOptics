
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
