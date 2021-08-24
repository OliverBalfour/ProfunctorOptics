
module ProfunctorOptics1

%default total

infixr 0 ~>

-- Helpers

T2 : Type
T2 = Type -> Type
T3 : Type
T3 = Type -> Type -> Type
T4 : Type
T4 = Type -> Type -> Type -> Type
T5 : Type
T5 = Type -> Type -> Type -> Type -> Type

fork : (a -> b) -> (a -> c) -> a -> (b, c)
fork f g x = (f x, g x)

cross : (a -> b) -> (c -> d) -> (a, c) -> (b, d)
cross f g (x, y) = (f x, g y)

-- Profunctors and associated definitions

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

-- Profunctors for sum types

interface Profunctor p => Cocartesian p where
  left  : p a b -> p (Either a c) (Either b c)
  right : p a b -> p (Either c a) (Either c b)

-- Monoidal profunctors (par : P x P -> P, empty : P)

interface Profunctor p => Monoidal p where
  par   : p a b -> p c d -> p (a, c) (b, d)
  empty : p () ()

-- Profunctor optics

OpticT : Type
OpticT = T3 -> T5

Optic : OpticT
Optic p a b s t = p a b -> p s t

Adapter : T5
Adapter a b s t = {p : T3} -> Profunctor p => Optic p a b s t

Lens : T5
Lens a b s t = {p : T3} -> Cartesian p => Optic p a b s t

Prism : T5
Prism a b s t = {p : T3} -> Cocartesian p => Optic p a b s t

LensPrism : T5
LensPrism a b s t = {p : T3}
  -> (Cartesian p, Cocartesian p)
  => Optic p a b s t

Traversal : T5
Traversal a b s t = {p : T3}
  -> (Cartesian p, Cocartesian p, Monoidal p)
  => Optic p a b s t

-- π₁ : {p : T3} -> Cartesian p => p a b -> p (a, c) (b, c)
π₁ : Lens a b (a, c) (b, c)
π₁ = dimap (fork fst id) (cross id snd) . first

-- op : {p : T3} -> Cocartesian p => p a b -> p (Maybe a) (Maybe b)
op : Prism a b (Maybe a) (Maybe b)
op = dimap (maybe (Left Nothing) Right) (either id Just) . right

op_π₁ : LensPrism a b (Maybe (a, c)) (Maybe (b, c))
op_π₁ = op . π₁

-- Profunctor (->), allows us to use our optics

-- (~>) is a synonym for (->) which is built-in, not a type constructor
(~>) : T3
a ~> b = a -> b

implementation Profunctor (~>) where
  -- dimap : (a -> b) -> (c -> d) -> (b ~> c) -> (a ~> d)
  dimap f g h = g . h . f

implementation Cartesian (~>) where
  -- first  : (a ~> b) -> ((a, c) ~> (b, c))
  first f (a, c) = (f a, c)
  -- second : (a ~> b) -> ((c, a) ~> (c, b))
  second f (c, a) = (c, f a)

implementation Cocartesian (~>) where
  -- left  : (a ~> b) -> ((Either a c) ~> (Either b c))
  left f (Left a) = Left (f a)
  left f (Right c) = Right c
  -- right : (a ~> b) -> ((Either c a) ~> (Either c b))
  right f (Left c) = Left c
  right f (Right a) = Right (f a)

implementation Monoidal (~>) where
  -- par   : (a ~> b) -> (c ~> d) -> ((a, c) ~> (b, d))
  par = cross
  -- empty : () ~> ()
  empty = const ()

