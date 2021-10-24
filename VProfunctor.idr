
module VProfunctor

import VFunctor
import Morphism

%default total
%hide Applicative

-- Verified profunctors
public export
interface VProfunctor (p : Type -> Type -> Type) where
  -- dimap maps two morphisms over a profunctor
  -- p(a,-) is a covariant functor, p(-,a) is contravariant
  dimap : (a -> b) -> (c -> d) -> p b c -> p a d

  -- Identity law, dimap id id = id
  pid : {a, b : Type} -> (x : p a b) -> dimap (\x => x) (\x => x) x = x
  -- Composition law, dimap (f' . f) (g . g') = dimap f g . dimap f' g'
  pcomp
    : {a, b, c, d, e, t : Type}
    -> (x : p a b)
    -> (f' : c -> a) -> (f  : d -> c)
    -> (g :  e -> t) -> (g' : b -> e)
    -> dimap (f' . f) (g . g') x = (dimap f g . dimap f' g') x

-- Profunctors for product and sum types, and monoidal profunctors

-- Cartesianly strong profunctors preserve product types
public export
interface VProfunctor p => Cartesian p where
  first  : p a b -> p (a, c) (b, c)
  second : p a b -> p (c, a) (c, b)

-- Co-Cartesianly strong profunctors preserve sum types
public export
interface VProfunctor p => Cocartesian p where
  left  : p a b -> p (Either a c) (Either b c)
  right : p a b -> p (Either c a) (Either c b)

-- Profunctors with monoid object structure
public export
interface VProfunctor p => Monoidal p where
  par   : p a b -> p c d -> p (a, c) (b, d)
  empty : p () ()

-- Profunctor implementations

-- Hom(-,-) profunctor, the canonical profunctor
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

-- Hom profunctor in the Kleisli category
-- This is the category of monadic types `m a` with Kleisli composition
-- f . g = \x => join (f (g x)), where join : m (m a) -> m a
-- We only require a functor for convenience
public export
implementation {k : Type -> Type} -> VFunctor k => VProfunctor (KleisliMorphism k) where
  dimap f g (Kleisli h) = Kleisli (fmap g . h . f)
  -- This proof reduces to `fmap (\x => x) . f = f` for `f : a -> k b`
  -- We can't make `fid` intensional, ie `fid : fmap (\x => x) = id`,
  -- because we need something to pattern match on to prove fid, so we must use
  -- extensionality here
  pid (Kleisli f) = cong Kleisli (extensionality (\x => fid (f x)))
  pcomp (Kleisli u) f' f g g' = cong Kleisli (extensionality (\x =>
    fcomp (u (f' (f x))) g g'))
