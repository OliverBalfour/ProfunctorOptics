
module Proofs

%default total

plusRightId : (x : Nat) -> x + 0 = x
plusRightId Z = Refl
plusRightId (S x) =
  let iH = plusRightId x
  in rewrite iH in Refl

plusComm : (x, y : Nat) -> x + y = y + x
plusComm x Z = rewrite plusRightId x in Refl
plusComm x (S y) =
  let iH = plusComm x y
  in rewrite iH
  in ?help
