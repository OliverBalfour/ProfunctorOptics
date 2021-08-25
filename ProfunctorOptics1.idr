
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


-- Complex data structures

data FunList : Type -> Type -> Type -> Type where
  Done : t -> FunList a b t
  More : a -> FunList a b (b -> t) -> FunList a b t

out : FunList a b t -> Either t (a, FunList a b (b -> t))
out (Done t) = Left t
out (More x l) = Right (x, l)

inn : Either t (a, FunList a b (b -> t)) -> FunList a b t
inn (Left t) = Done t
inn (Right (x, l)) = More x l

implementation Functor (FunList a b) where
  map f (Done t) = Done (f t)
  map f (More x l) = More x (map (f .) l)

implementation Applicative (FunList a b) where
  pure = Done
  Done f <*> l = map f l
  More x l <*> l2 = assert_total More x (map flip l <*> l2)

single : a -> FunList a b b
single x = More x (Done id)

fuse : FunList b b t -> t
fuse (Done t) = t
fuse (More x l) = fuse l x

traverse : {p : T3} -> (Cocartesian p, Monoidal p)
  => p a b
  -> p (FunList a c t) (FunList b c t)
traverse k = assert_total dimap out inn (right (par k (traverse k)))

makeTraversal : (s -> FunList a b t) -> Traversal a b s t
makeTraversal h k = dimap h fuse (traverse k)

-- Binary trees

data BTree : Type -> Type where
  Empty : BTree a
  Node : BTree a -> a -> BTree a -> BTree a

-- TODO: is FunList a Monad? If so, we can do traversals other than in-order

inorder' : {f : T2} -> Applicative f
  => (a -> f b)
  -> BTree a -> f (BTree b)
inorder' m Empty = pure Empty
inorder' m (Node l x r) = Node <$> inorder' m l <*> m x <*> inorder' m r

inorder : {a, b : Type} -> Traversal a b (BTree a) (BTree b)
inorder = makeTraversal (inorder' single)

-- Lists

listTraverse' : {f : T2} -> Applicative f
  => (a -> f b)
  -> List a -> f (List b)
listTraverse' g [] = pure []
listTraverse' g (x::xs) = (::) <$> g x <*> listTraverse' g xs

listTraverse : {a, b : Type} -> Traversal a b (List a) (List b)
listTraverse = makeTraversal (listTraverse' single)

-- -- This proof is commented out because it causes Idris to infinite loop
-- listTraverseGeneralisesMap : {a, b : Type}
--   -> (f' : a -> b)
--   -> (xs' : List a)
--   -> listTraverse {p=(~>)} f' xs' = map f' xs'
-- listTraverseGeneralisesMap f [] = Refl
-- listTraverseGeneralisesMap f (x::xs) =
--   let iH = listTraverseGeneralisesMap {a=a} {b=b} f xs
--   in rewrite iH in Refl

-- Rose trees

-- data RTree : Type -> Type where
--   Leaf : a -> RTree a
--   Branch : List (RTree a) -> RTree a

-- implementation Functor RTree where
--   -- map : (a -> b) -> (RTree a -> RTree b)
--   map f (Leaf x) = Leaf (f x)
--   map f (Branch []) = Branch []
--   map f (Branch (x::xs)) = Branch (map f x :: map (map f) xs)

-- implementation Foldable RTree where
--   -- foldr : (elem -> acc -> acc) -> acc -> RTree elem -> acc
--   foldr f a (Leaf x) = f x a
--   foldr f a (Branch []) = a
--   foldr f a (Branch (x::xs)) = ?help

-- implementation Traversable RTree where
--   -- traverse : Applicative f => (a -> f b) -> RTree a -> f (RTree b)
--   traverse g (Leaf x) = Leaf <$> g x
--   traverse g (Branch []) = pure (Branch [])
--   traverse g (Branch (x::xs)) =
--     let x' = traverse g x
--         xs' = traverse g (Branch xs)
--     in Branch <$> ?help2 -- (x' :: xs')

-- traverseRTree' : {f : T2} -> Applicative f
--   => (a -> f b)
--   -> RTree a -> f (RTree b)
-- traverseRTree' g (Leaf x) = Leaf <$> g x
-- traverseRTree' g (Branch branches) = foldr
--   (\branch, acc => ?help (Branch [traverse g branch, acc]))
--   (pure (Branch []))
--   branches

-- -- foldr (\(Branch acc) x => Branch $ (::) <$> traverseRTree' g x <*> acc) (pure []) xs


-- Some tests
-- Aside: the fact that we can express unit tests on a type level means we get
-- *compiler errors when unit tests fail*. Isn't that beautiful?

square : Num a => a -> a
square x = x * x

-- can use (op {p=(~>)} . π₁ {p=(~>)}) instead, Idris doesn't guess p very well
test1 : op_π₁ {p=(~>)} ProfunctorOptics1.square (Just (3, True)) = Just (9, True)
test1 = Refl

test2 : inorder {p=(~>)} ProfunctorOptics1.square (Node (Node Empty 3 Empty) 4 Empty) = Node (Node Empty 9 Empty) 16 Empty
test2 = Refl

test3 : listTraverse {p=(~>)} ProfunctorOptics1.square [1,2,3,4] = [1,4,9,16]
test3 = Refl
