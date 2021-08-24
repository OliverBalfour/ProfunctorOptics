
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

-- TODO: don't use a record to carry around types, is there a nicer way
-- to do this using dependent types?
record UpStar (f : Type -> Type) a b where
  constructor MkUpStar
  unUpStar : a -> f b
