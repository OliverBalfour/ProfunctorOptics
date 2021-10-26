
module Category.VProfunctor

import Category.VFunctor
import Category.Morphism

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

public export
implementation {k : Type -> Type} -> VApplicative k => Cocartesian (KleisliMorphism k) where
  left (Kleisli f) = Kleisli (either (fmap Left . f) (ret . Right))
  right (Kleisli f) = Kleisli (either (ret . Left) (fmap Right . f))

-- Const profunctor, Const r a is isomorphic to Hom((), a)
-- This profunctor allows us to use our optics as constructors
-- eg: op {p=Const} (MkConst 3) == MkConst (Just 3)
public export
record Const r a where
  constructor MkConst  -- MkConst : a -> Const r a
  unConst : a          -- unConst : Const r a -> a

public export
implementation VProfunctor Const where
  dimap f g (MkConst x) = MkConst (g x)
  pid (MkConst x) = Refl
  pcomp (MkConst x) f' f g g' = Refl

public export
implementation Cocartesian Const where
  left (MkConst x) = MkConst (Left x)
  right (MkConst x) = MkConst (Right x)

public export
implementation Monoidal Const where
  par (MkConst x) (MkConst y) = MkConst (x, y)
  empty = MkConst ()

-- `Forget r` profunctor
-- Allows us to use our profunctor optics as getters
-- eg: unForget (π₁ {p=Forget Int} (MkForget (\x => x))) (3, True) == 3
-- Inspired by PureScript's profunctor-lenses:
-- https://github.com/purescript-contrib/purescript-profunctor-lenses/
public export
record Forget r a b where
  constructor MkForget  -- MkForget : (a -> r) -> Forget r a b
  unForget : a -> r     -- unForget : Forget r a b -> (a -> r)

public export
implementation {r : Type} -> VProfunctor (Forget r) where
  dimap f g (MkForget h) = MkForget (h . f)
  pid (MkForget x) = Refl
  pcomp (MkForget x) f' f g g' = Refl

public export
implementation {r : Type} -> Cartesian (Forget r) where
  first (MkForget f) = MkForget (\(x, y) => f x)
  second (MkForget f) = MkForget (\(x, y) => f y)
