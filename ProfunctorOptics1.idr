
module ProfunctorOptics1

%default total

-- Profunctors and associated definitions

T2 : Type
T2 = Type -> Type
T3 : Type
T3 = Type -> Type -> Type

interface Profunctor (p : T3) where
  dimap : (a -> b) -> (c -> d) -> p b c -> p a d
  dimap f g = lmap f . rmap g

  lmap : (a -> b) -> p b c -> p a c
  lmap = flip dimap Basics.id

  rmap : (a -> b) -> p c a -> p c b
  rmap = dimap Basics.id

interface Profunctor p => VerifiedProfunctor (p : T3) where
  proId : {a, b : Type} -> (x : p a b) -> dimap Basics.id Basics.id x = x
  proComp
    : {a, b, c, d, e, t : Type}
    -> (x : p a b)
    -> (f' : c -> a) -> (f  : d -> c)
    -> (g :  e -> t) -> (g' : b -> e)
    -> dimap (f' . f) (g . g') x = (dimap f g . dimap f' g') x

-- -- Invalid syntax but illustrative
-- instance Profunctor (->) where
--   dimap f g h = g . h . f

-- Like a morphism in a Kleisli category, but f is only required to be a functor
-- Ideally don't use a record to carry around types, is there a nicer way
-- to do this using dependent types?
record UpStar (f : T2) a b where
  constructor MkUpStar
  unUpStar : a -> f b

implementation {f : T2} -> Functor f => Profunctor (UpStar f) where
  dimap g h (MkUpStar i) = MkUpStar (map h . i . g)

-- Profunctors for product types

interface Profunctor p => Cartesian p where
  first  : p a b -> p (a, c) (b, c)
  second : p a b -> p (c, a) (c, b)

-- interface (VerifiedProfunctor p, Cartesian p) => VerifiedCartesian p where
--   ... (see page 12 for laws)

-- implementation Functor f => Cartesian (UpStar f) where
--   first (MkUpStar i) = ... (see page 12)

-- Profunctors for sum types

interface Profunctor p => Cocartesian p where
  left  : p a b -> p (Either a c) (Either b c)
  right : p a b -> p (Either c a) (Either c b)

-- laws for VerifiedCocartesian are on p13

-- implementation Applicative f => Cocartesian (UpStar f) where
--   -- ... see p13

interface Profunctor p => Monoidal p where
  par   : p a b -> p c d -> p (a, c) (b, d)
  empty : p () ()

-- laws for Monoidal on p14

-- implementation Applicative f => Monoidal (UpStar f) where
--   empty = MkUpStar pure
--   -- par = ...

-- Profunctor optics

OpticT : Type
OpticT = T3 -> Type -> Type -> Type -> Type -> Type

Optic : OpticT
Optic p a b s t = p a b -> p s t

Adapter : OpticT
Adapter p a b s t = Optic p a b s t  -- huh?

fork : (a -> b) -> (a -> c) -> a -> (b, c)
fork f g x = (f x, g x)

cross : (a -> b) -> (c -> d) -> (a, c) -> (b, d)
cross f g (x, y) = (f x, g y)

π₁ : {p : T3} -> Cartesian p => p a b -> p (a, c) (b, c)
π₁ = dimap (fork fst id) (cross id snd) . first
