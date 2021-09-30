
module VProfunctor

import VFunctor
import Morphism

%default total

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

public export
implementation VProfunctor Morphism where
  dimap f g (Mor h) = Mor (g . h . f)
  pid (Mor f) = cong Mor (sym (ext f))
  pcomp (Mor x) f' f g g' = Refl

public export
implementation {k : Type -> Type} -> VFunctor k => VProfunctor (KleisliMorphism k) where
  dimap f g (Kleisli h) = Kleisli (fmap g . h . f)
  -- this proof reduces to `fmap (\x => x) . f = f` for `f : a -> k b`
  -- which means either changing fid to have type `fmap (\x => x) = id`
  -- or invoking extensionality
  -- if we made `fid : fmap (\x => x) = id` we wouldn't be able to prove it
  -- on List for instance, because we have nothing to pattern match on
  -- so we resort to extensionality
  pid (Kleisli f) = cong Kleisli (extensionality' (\x => fid (f x)))
  pcomp (Kleisli u) f' f g g' = cong Kleisli (extensionality' (\x =>
    fcomp (u (f' (f x))) g g'))
