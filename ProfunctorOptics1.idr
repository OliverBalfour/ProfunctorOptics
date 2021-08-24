
module ProfunctorOptics1

%default total

interface Profunctor (p : Type -> Type -> Type) where
  dimap : (a -> b) -> (c -> d) -> p b c -> p a d
  dimap f g = lmap f . rmap g

  lmap : (a -> b) -> p b c -> p a c
  lmap = flip dimap Basics.id

  rmap : (a -> b) -> p c a -> p c b
  rmap = dimap Basics.id

interface Profunctor p => VerifiedProfunctor (p : Type -> Type -> Type) where
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
record UpStar (f : Type -> Type) a b where
  constructor MkUpStar
  unUpStar : a -> f b

-- Type not accessible in this context error
-- implementation Functor f => Profunctor (UpStar f) where
--   dimap = g h (UpStar i) = MkUpStar (map (h . i . g))

-- Profunctors for product types

interface Profunctor p => Cartesian p where
  first  : p a b -> p (a, c) (b, c)
  second : p a b -> p (c, a) (c, b)

-- interface (VerifiedProfunctor p, Cartesian p) => VerifiedCartesian p where
--   ... (see page 12 for laws)

-- implementation Functor f => Cartesian (UpStar f) where
--   first (UpStar i) = ... (see page 12)

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
