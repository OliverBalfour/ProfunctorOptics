
module Lens

%default total

-- Primitive optics
-- Simpler to write than profunctor optics but they don't compose well
-- And you can't compose prisms and lenses with this encoding
-- Solution: write primitive optics and map them to profunctor optics

data Lens : Type -> Type -> Type -> Type -> Type where
  MkLens
    :  (view : s -> a)
    -> (update : (b, s) -> t)
    -> Lens a b s t

data Prism : Type -> Type -> Type -> Type -> Type where
  MkPrism
    :  (match : s -> Either t a)
    -> (build : b -> t)
    -> Prism a b s t

data Adapter : Type -> Type -> Type -> Type -> Type where
  MkAdapter
    :  (from : s -> a)
    -> (to : b -> t)
    -> Adapter a b s t

-- Basic optics: product projections, optionals, etc.

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

op : Prism a b (Maybe a) (Maybe b)
op = MkPrism match build where
  match : Maybe a -> Either (Maybe b) a
  match (Just x) = Right x
  match Nothing = Left Nothing
  build : b -> Maybe b
  build = Just

-- witness to the iso (A x B) x C ~=~ A x (B x C)
prodAssoc : Adapter ((a,b),c) ((a',b'),c') (a,(b,c)) (a',(b',c'))
prodAssoc = MkAdapter (\(x,(y,z))=>((x,y),z)) (\((x,y),z)=>(x,(y,z)))
