
module VProfunctor

import VFunctor
import Morphism

%default total

-- Verified profunctors

public export
interface VProfunctor (p : Type -> Type -> Type) where
  dimap : (a -> b) -> (c -> d) -> p b c -> p a d
  dimap f g = lmap f . rmap g

  lmap : (a -> b) -> p b c -> p a c
  lmap = flip dimap (\x => x)

  rmap : (a -> b) -> p c a -> p c b
  rmap = dimap (\x => x)

  pid : {a, b : Type} -> (x : p a b) -> dimap (\x => x) (\x => x) x = x
  pcomp
    : {a, b, c, d, e, t : Type}
    -> (x : p a b)
    -> (f' : c -> a) -> (f  : d -> c)
    -> (g :  e -> t) -> (g' : b -> e)
    -> dimap (f' . f) (g . g') x = (dimap f g . dimap f' g') x

-- Profunctors for product and sum types, and monoidal profunctors

public export
interface VProfunctor p => Cartesian p where
  first  : p a b -> p (a, c) (b, c)
  second : p a b -> p (c, a) (c, b)

public export
interface VProfunctor p => Cocartesian p where
  left  : p a b -> p (Either a c) (Either b c)
  right : p a b -> p (Either c a) (Either c b)

public export
interface VProfunctor p => Monoidal p where
  par   : p a b -> p c d -> p (a, c) (b, d)
  empty : p () ()

-- Profunctor implementations

public export
implementation VProfunctor Morphism where
  dimap f g (Mor h) = Mor (g . h . f)
  pid (Mor f) = cong Mor (sym (ext f))
  pcomp (Mor x) f' f g g' = Refl

public export
implementation Cartesian Morphism where
  first (Mor f) = Mor (\(a, c) => (f a, c))
  second (Mor f) = Mor (\(c, a) => (c, f a))

public export
implementation Cocartesian Morphism where
  left (Mor f) = Mor (\case
    Left a => Left (f a)
    Right c => Right c)
  right (Mor f) = Mor (\case
    Left c => Left c
    Right a => Right (f a))

public export
implementation Monoidal Morphism where
  par (Mor f) (Mor g) = Mor (\(x, y) => (f x, g y))
  empty = Mor (const ())

public export
implementation {k : Type -> Type} -> VFunctor k => VProfunctor (KleisliMorphism k) where
  dimap f g (Kleisli h) = Kleisli (fmap g . h . f)
  -- this proof reduces to `fmap (\x => x) . f = f` for `f : a -> k b`
  -- we can't make `fid : fmap (\x => x) = id` because we need something
  -- to pattern match on to prove it, so we use extensionality
  pid (Kleisli f) = cong Kleisli (extensionality' (\x => fid (f x)))
  pcomp (Kleisli u) f' f g g' = cong Kleisli (extensionality' (\x =>
    fcomp (u (f' (f x))) g g'))
