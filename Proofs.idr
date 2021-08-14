
module Proofs

%default total

infixl 7 <>

-- groups are types (like sets) with extra structure following some laws
interface Group a where
  -- components
  (<>) : a -> a -> a
  neg : a -> a
  e : a
  -- laws
  assoc : (x, y, z : a) -> (x <> y) <> z = x <> (y <> z)
  identity : (x : a) -> (e <> x = x, x <> e = x)
  inverses : (x : a) -> (neg x <> x = e, x <> neg x = e)

-- subgroups are boolean predicates on a group where the filtered set of group
-- elements still adheres to the group laws
-- Subgroup : 

-- data Zn : Nat -> Type where

-- implementation Group Zn where
  --

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
