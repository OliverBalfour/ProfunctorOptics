
module PrimitiveOptics

import Profunctor

%default total

-- Primitive optics
-- Simpler to write than profunctor optics but they don't compose well
-- And you can't compose prisms and lenses with this encoding
-- Solution: write primitive optics and map them to profunctor optics

public export
data PrimLens : Type -> Type -> Type -> Type -> Type where
  MkPrimLens
    :  (view : s -> a)
    -> (update : (b, s) -> t)
    -> PrimLens a b s t

public export
data PrimPrism : Type -> Type -> Type -> Type -> Type where
  MkPrimPrism
    :  (match : s -> Either t a)
    -> (build : b -> t)
    -> PrimPrism a b s t

public export
data PrimAdapter : Type -> Type -> Type -> Type -> Type where
  MkPrimAdapter
    :  (from : s -> a)
    -> (to : b -> t)
    -> PrimAdapter a b s t

-- Basic optics: product projections, optionals, etc.

π₁ : PrimLens a b (a, c) (b, c)
π₁ = MkPrimLens fst update where
  update : (b, (a, c)) -> (b, c)
  update (x', (x, y)) = (x', y)

π₂ : PrimLens a b (c, a) (c, b)
π₂ = MkPrimLens snd update where
  update : (b, (c, a)) -> (c, b)
  update (x', (y, x)) = (y, x')

sgn : PrimLens Bool Bool Integer Integer
sgn = MkPrimLens signum chsgn where
  signum : Integer -> Bool
  signum x = x >= 0
  chsgn : (Bool, Integer) -> Integer
  chsgn (True,  x) =  abs x
  chsgn (False, x) = -abs x

op : PrimPrism a b (Maybe a) (Maybe b)
op = MkPrimPrism match build where
  match : Maybe a -> Either (Maybe b) a
  match (Just x) = Right x
  match Nothing = Left Nothing
  build : b -> Maybe b
  build = Just

-- witness to the iso (A x B) x C ~=~ A x (B x C)
prodAssoc : PrimAdapter ((a,b),c) ((a',b'),c') (a,(b,c)) (a',(b',c'))
prodAssoc = MkPrimAdapter (\(x,(y,z))=>((x,y),z)) (\((x,y),z)=>(x,(y,z)))

-- Primitive optics are special cases of profunctors

public export
implementation {a : Type} -> {b : Type} -> Profunctor (PrimPrism a b) where
  dimap f g (MkPrimPrism m b) = MkPrimPrism (bimap g id . m . f) (g . b)

public export
implementation {a : Type} -> {b : Type} -> Cocartesian (PrimPrism a b) where
  left (MkPrimPrism m b) = MkPrimPrism (either (bimap Left id . m) (Left . Right)) (Left . b)
  right (MkPrimPrism m b) = MkPrimPrism (either (Left . Left) (bimap Right id . m)) (Right . b)
