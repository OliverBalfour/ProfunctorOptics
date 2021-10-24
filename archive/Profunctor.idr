
module Profunctor

%default total

infixr 0 ~>
infixr 0 ~~>

-- Function equality axioms
-- This was introduced because we need a way to equate values of type
-- Profunctor p => p a b. These are generally functions but may be standalone
-- values, and we need a way to use extensional equality without constraining
-- ourselves to only function valued profunctors
-- The alternative is to require that all profunctors be functions, and then
-- constants are maps x : () -> a instead of just x : a
etaReductionEq : (f : a -> b) -> (\x => f x) = f
extEq : (f, g : a -> b) -> (x : a) -> f x = g x -> f = g

-- Profunctors and their laws

public export
interface Profunctor (p : Type -> Type -> Type) where
  dimap : (a -> b) -> (c -> d) -> p b c -> p a d
  dimap f g = lmap f . rmap g

  lmap : (a -> b) -> p b c -> p a c
  lmap = flip dimap Basics.id

  rmap : (a -> b) -> p c a -> p c b
  rmap = dimap Basics.id

public export
interface Profunctor p => VerifiedProfunctor (p : Type -> Type -> Type) where
  proId : {a, b : Type} -> (x : p a b) -> dimap {p=p} Basics.id Basics.id x = x
  proComp
    : {a, b, c, d, e, t : Type}
    -> (x : p a b)
    -> (f' : c -> a) -> (f  : d -> c)
    -> (g :  e -> t) -> (g' : b -> e)
    -> dimap {p=p} (f' . f) (g . g') x = (dimap {p=p} f g . dimap {p=p} f' g') x

-- Profunctors for product and sum types, and monoidal profunctors

public export
interface Profunctor p => Cartesian p where
  first  : p a b -> p (a, c) (b, c)
  second : p a b -> p (c, a) (c, b)

public export
interface Profunctor p => Cocartesian p where
  left  : p a b -> p (Either a c) (Either b c)
  right : p a b -> p (Either c a) (Either c b)

public export
interface Profunctor p => Monoidal p where
  par   : p a b -> p c d -> p (a, c) (b, d)
  empty : p () ()


-- Other interfaces

public export
interface Functor f => VerifiedFunctor (f : Type -> Type) where
  mapId : {x : f a}
    -> map {f=f} Basics.id x = x
  mapComp : {x : f a} -> {g : b -> c} -> {h : a -> b}
    -> map (g . h) x = (map {f=f} g . map {f=f} h) x


-- Function types form the Hom(-,-) profunctor

-- (~>) is a synonym for (->) which is built-in, not a type constructor
public export
(~>) : Type -> Type -> Type
a ~> b = a -> b

public export
implementation Profunctor (~>) where
  -- dimap : (a -> b) -> (c -> d) -> (b ~> c) -> (a ~> d)
  dimap f g h = g . h . f

public export
implementation VerifiedProfunctor (~>) where
  proId f = etaReductionEq f
  proComp x f' f g g' = Refl

public export
implementation Cartesian (~>) where
  -- first  : (a ~> b) -> ((a, c) ~> (b, c))
  first f (a, c) = (f a, c)
  -- second : (a ~> b) -> ((c, a) ~> (c, b))
  second f (c, a) = (c, f a)

public export
implementation Cocartesian (~>) where
  -- left  : (a ~> b) -> ((Either a c) ~> (Either b c))
  left f (Left a) = Left (f a)
  left f (Right c) = Right c
  -- right : (a ~> b) -> ((Either c a) ~> (Either c b))
  right f (Left c) = Left c
  right f (Right a) = Right (f a)

public export
implementation Monoidal (~>) where
  -- par   : (a ~> b) -> (c ~> d) -> ((a, c) ~> (b, d))
  par f g (x, y) = (f x, g y)
  -- empty : () ~> ()
  empty = const ()


-- Function types with a functorial return value
-- This is the Hom(-,-) profunctor in the Kleisli category, except it's defined
-- for functors and applicatives too

public export
(~~>) : {f : Type -> Type} -> Type -> Type -> Type
a ~~> b = a -> f b

public export
implementation {f : Type -> Type} -> Functor f => Profunctor ((~~>) {f=f}) where
  dimap g h i = map {f=f} h . i . g

-- public export
-- implementation {f : Type -> Type} -> (VerifiedFunctor f, Profunctor ((~~>) {f=f})) => VerifiedProfunctor ((~~>) {f=f}) where
--   proId g = ?help1
--   proComp x f' f g g' = ?help2

public export
implementation {f : Type -> Type} -> (Functor f, Profunctor ((~~>) {f=f})) => Cartesian ((~~>) {f=f}) where
  -- first  : (a ~~> b) -> ((a, c) ~~> (b, c))
  first g (a, c) = map (,c) (g a)
  -- second : (a ~~> b) -> ((c, a) ~~> (c, b))
  second g (c, a) = map (c,) (g a)

public export
implementation {f : Type -> Type} -> (Applicative f, Profunctor ((~~>) {f=f})) => Cocartesian ((~~>) {f=f}) where
  -- left  : (a ~~> b) -> ((Either a c) ~~> (Either b c))
  left g (Left a) = map Left (g a)
  left g (Right c) = pure (Right c)
  -- right : (a ~~> b) -> ((Either c a) ~~> (Either c b))
  right g (Left c) = pure (Left c)
  right g (Right a) = map Right (g a)

public export
implementation {f : Type -> Type} -> (Applicative f, Profunctor ((~~>) {f=f})) => Monoidal ((~~>) {f=f}) where
  -- par   : (a ~~> b) -> (c ~~> d) -> ((a, c) ~~> (b, d))
  par g h (x, y) = (,) <$> g x <*> h y
  -- empty : () ~~> ()
  empty () = pure ()
