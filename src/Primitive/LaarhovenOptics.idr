
module Primitive.LaarhovenOptics

import Category.VFunctor

-- van Laarhoven lens type
public export
LaarhovenLens : {f : Type -> Type} -> VFunctor f => Type -> Type -> Type
LaarhovenLens a s = (a -> f a) -> (s -> f s)

-- Left product projection
public export
laarhovenProj : {f : Type -> Type} -> VFunctor f => LaarhovenLens {f=f} a (a,b)
laarhovenProj g (x, y) = fmap (,y) (g x)

-- The Const functor turns van Laarhoven optics into getters
-- Note this Const stores one of the first type and the Const in VProfunctor
-- stores one of the second type
record Const a b where
  constructor MkConst
  unConst : a

implementation {a : Type} -> VFunctor (Const a) where
  fmap f (MkConst x) = MkConst x
  fid (MkConst x) = Refl
  fcomp (MkConst x) g h = Refl
  infixSame g (MkConst x) = Refl

-- Identity functor
public export
record Id a where
  constructor MkId
  unId : a

-- The identity functor turns van Laarhoven optics into update functions
public export
implementation VFunctor Id where
  fmap f (MkId x) = MkId (f x)
  fid (MkId x) = Refl
  fcomp (MkId x) g h = Refl
  infixSame g (MkId x) = Refl

-- Useful combinators
public export
view' : LaarhovenLens {f=Const a} a s -> (s -> a)
view' optic structure = unConst $
  optic (\x => MkConst x) structure

public export
update' : LaarhovenLens {f=Id} a s -> ((a, s) -> s)
update' optic (field, structure) = unId $
  optic (\x => MkId field) structure
