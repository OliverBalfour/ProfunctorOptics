
module Lens

import Data.Bits
import Data.Fin

%default total

record Lens a b s t where
  constructor MkLens
  view : s -> a
  update : (b, s) -> t

π₁ : Lens a b (a, c) (b, c)
π₁ = MkLens fst update where
  update : (b, (a, c)) -> (b, c)
  update (x', (x, y)) = (x', y)

π₂ : Lens a b (c, a) (c, b)
π₂ = MkLens snd update where
  update : (b, (c, a)) -> (c, b)
  update (x', (y, x)) = (y, x')

sgn : Lens Bool Bool Integer Integer
sgn = MkLens signum chsgn where
  signum : Integer -> Bool
  signum x = x >= 0
  chsgn : (Bool, Integer) -> Integer
  chsgn (True,  x) =  abs x
  chsgn (False, x) = -abs x

record Prism a b s t where
  constructor MkPrism
  match : s -> Either t a
  build : b -> t

op : Prism a b (Maybe a) (Maybe b)
op = MkPrism match build where
  match : Maybe a -> Either (Maybe b) a
  match (Just x) = Right x
  match Nothing = Left Nothing
  build : b -> Maybe b
  build = Just

-- whole :: Prism Integer Integer Double Double
-- whole = MkPrism match build where
--   match : Double -> Either Double Integer
--   match x = -- integer if it's a whole number otherwise a double
--   build : Integer -> Double
--   build = fromInteger

record Adapter a b s t where
  constructor MkAdapter
  from : s -> a
  to : b -> t

-- witness to the iso (A x B) x C ~=~ A x (B x C)
prodAssoc : Adapter ((a,b),c) ((a',b'),c') (a,(b,c)) (a',(b',c'))
prodAssoc = MkAdapter (\(x,(y,z))=>((x,y),z)) (\((x,y),z)=>(x,(y,z)))
