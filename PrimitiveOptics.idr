
module PrimitiveOptics

import VProfunctor
import Morphism

%default total

-- Primitive optics
-- Simpler to write than profunctor optics but they don't compose well
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

-- Examples of simple optics

-- Product left/right projection lens
π₁ : PrimLens a b (a, c) (b, c)
π₁ = MkPrimLens fst update where
  update : (b, (a, c)) -> (b, c)
  update (x', (x, y)) = (x', y)
π₂ : PrimLens a b (c, a) (c, b)
π₂ = MkPrimLens snd update where
  update : (b, (c, a)) -> (c, b)
  update (x', (y, x)) = (y, x')

-- Sign of an integer lens
sgn : PrimLens Bool Bool Integer Integer
sgn = MkPrimLens signum chsgn where
  signum : Integer -> Bool
  signum x = x >= 0
  chsgn : (Bool, Integer) -> Integer
  chsgn (True,  x) =  abs x
  chsgn (False, x) = -abs x

-- Maybe prism
op : PrimPrism a b (Maybe a) (Maybe b)
op = MkPrimPrism match build where
  match : Maybe a -> Either (Maybe b) a
  match (Just x) = Right x
  match Nothing = Left Nothing
  build : b -> Maybe b
  build = Just

-- Adapter for the isomorphism (A x B) x C = A x (B x C)
prodAssoc : PrimAdapter ((a,b),c) ((a',b'),c') (a,(b,c)) (a',(b',c'))
prodAssoc = MkPrimAdapter (\(x,(y,z)) => ((x,y),z)) (\((x,y),z) => (x,(y,z)))

-- Primitive optics are special cases of profunctors

-- Definitions and lemmas from the Either bifunctor
bimapEither : (a -> c) -> (b -> d) -> Either a b -> Either c d
bimapEither f g (Left x) = Left (f x)
bimapEither f g (Right x) = Right (g x)

bimapId : (z : Either a b) -> bimapEither (\x => x) (\x => x) z = z
bimapId (Left y) = Refl
bimapId (Right y) = Refl

bimapLemma : (g :  e -> t) -> (g' : b -> e) -> (x' : Either b a)
  -> bimapEither (g . g') (\x => x) x' = bimapEither g (\x => x) (bimapEither g' (\x => x) x')
bimapLemma g g' (Left x) = Refl
bimapLemma g g' (Right x) = Refl

-- PrimPrism a b forms a Cocartesian profunctor
public export
implementation {a : Type} -> {b : Type} -> VProfunctor (PrimPrism a b) where
  dimap f g (MkPrimPrism m b) = MkPrimPrism (bimapEither g id . m . f) (g . b)
  pid (MkPrimPrism m b) = cong (`MkPrimPrism` b) (
    extensionality (\x => bimapId (m x)))
  pcomp (MkPrimPrism m b) f' f g g' = cong (`MkPrimPrism` (\x => g (g' (b x))))
    (extensionality (\x => bimapLemma g g' (m (f' (f x)))))

public export
implementation {a : Type} -> {b : Type} -> Cocartesian (PrimPrism a b) where
  left (MkPrimPrism m b) = MkPrimPrism (either (bimapEither Left id . m) (Left . Right)) (Left . b)
  right (MkPrimPrism m b) = MkPrimPrism (either (Left . Left) (bimapEither Right id . m)) (Right . b)
