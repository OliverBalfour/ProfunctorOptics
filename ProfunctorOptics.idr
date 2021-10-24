
module ProfunctorOptics

import VProfunctor
import VFunctor
import PrimitiveOptics
import Morphism
import Data.Vect

%default total
%hide Prelude.Interfaces.(<*>)
%hide Prelude.Interfaces.(<$>)

infixr 0 ~>


-- Profunctor optics

Optic : (Type -> Type -> Type) -> Type -> Type -> Type -> (Type -> Type)
Optic p a b s t = p a b -> p s t

Adapter : Type -> Type -> Type -> Type -> Type
Adapter a b s t = {p : Type -> Type -> Type} -> VProfunctor p => Optic p a b s t

Lens : Type -> Type -> Type -> Type -> Type
Lens a b s t = {p : Type -> Type -> Type} -> Cartesian p => Optic p a b s t

Prism : Type -> Type -> Type -> Type -> Type
Prism a b s t = {p : Type -> Type -> Type} -> Cocartesian p => Optic p a b s t

LensPrism : Type -> Type -> Type -> Type -> Type
LensPrism a b s t = {p : Type -> Type -> Type}
  -> (Cartesian p, Cocartesian p)
  => Optic p a b s t

Traversal : Type -> Type -> Type -> Type -> Type
Traversal a b s t = {p : Type -> Type -> Type}
  -> (Cartesian p, Cocartesian p, Monoidal p)
  => Optic p a b s t

-- Product types (trivial)

-- π₁ : {p : Type -> Type -> Type} -> Cartesian p => p a b -> p (a, c) (b, c)
π₁ : Lens a b (a, c) (b, c)
π₁ = first

π₂ : Lens a b (c, a) (c, b)
π₂ = second

-- Optional types

-- op : {p : Type -> Type -> Type} -> Cocartesian p => p a b -> p (Maybe a) (Maybe b)
op : Prism a b (Maybe a) (Maybe b)
op = dimap (maybe (Left Nothing) Right) (either id Just) . right

-- Sum/coproduct types (trivial)

leftP : Prism a b (Either a c) (Either b c)
leftP = left

rightP : Prism a b (Either c a) (Either c b)
rightP = right

-- Composition

op_π₁ : LensPrism a b (Maybe (a, c)) (Maybe (b, c))
op_π₁ = op . π₁

-- Map primitive optics to profunctor optics

prismFromPrim : PrimPrism a b s t -> Prism a b s t
prismFromPrim (MkPrimPrism m b) = dimap m (either id b) . right

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

implementation {a : Type} -> {b : Type} -> VFunctor (FunList a b) where
  fmap f (Done t) = Done (f t)
  fmap f (More x l) = More x (fmap (f .) l)
  fid (Done t) = Refl
  fid (More x l) = cong (More x) (fid l)
  fcomp (Done t) g h = Refl
  fcomp (More x l) g h = cong (More x) (fcomp l (g .) (h .))
  infixSame f x = Refl

implementation {a : Type} -> {b : Type} -> VApplicative (FunList a b) where
  ret = Done
  Done f <*> l = fmap f l
  More x l <*> l2 = assert_total More x (fmap flip l <*> l2)
  aid (Done t) = Refl
  aid (More x l) = cong (More x) (aid l)
  ahom g x = Refl
  aint u y = believe_me () -- todo
  acomp u v w = believe_me ()

single : a -> FunList a b b
single x = More x (Done id)

fuse : FunList b b t -> t
fuse (Done t) = t
fuse (More x l) = fuse l x

traverse : {p : Type -> Type -> Type} -> (Cocartesian p, Monoidal p)
  => p a b
  -> p (FunList a c t) (FunList b c t)
traverse k = assert_total dimap out inn (right (par k (traverse k)))

makeTraversal : (s -> FunList a b t) -> Traversal a b s t
makeTraversal h k = dimap h fuse (traverse k)

-- Binary tree traversals

inorder' : {f : Type -> Type} -> VApplicative f
  => (a -> f b)
  -> BTree a -> f (BTree b)
inorder' m Null = ret Null
inorder' m (Node l x r) = Node <$> inorder' m l <*> m x <*> inorder' m r

inorder : {a, b : Type} -> Traversal a b (BTree a) (BTree b)
inorder = makeTraversal (inorder' single)

preorder' : {f : Type -> Type} -> VApplicative f
  => (a -> f b)
  -> BTree a -> f (BTree b)
preorder' m Null = ret Null
preorder' m (Node l x r) =
  (\mid, left, right => Node left mid right) <$>
    m x <*> preorder' m l <*> preorder' m r

preorder : {a, b : Type} -> Traversal a b (BTree a) (BTree b)
preorder = makeTraversal (preorder' single)

postorder' : {f : Type -> Type} -> VApplicative f
  => (a -> f b)
  -> BTree a -> f (BTree b)
postorder' m Null = ret Null
postorder' m (Node l x r) =
  (\left, right, mid => Node left mid right) <$>
    postorder' m l <*> postorder' m r <*> m x

postorder : {a, b : Type} -> Traversal a b (BTree a) (BTree b)
postorder = makeTraversal (postorder' single)

-- Lists

listTraverse' : {f : Type -> Type} -> VApplicative f
  => (a -> f b)
  -> List a -> f (List b)
listTraverse' g [] = ret []
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
--   -- traverse : VApplicative f => (a -> f b) -> RTree a -> f (RTree b)
--   traverse g (Leaf x) = Leaf <$> g x
--   traverse g (Branch []) = pure (Branch [])
--   traverse g (Branch (x::xs)) =
--     let x' = traverse g x
--         xs' = traverse g (Branch xs)
--     in Branch <$> ?help2 -- (x' :: xs')

-- traverseRTree' : {f : Type -> Type} -> VApplicative f
--   => (a -> f b)
--   -> RTree a -> f (RTree b)
-- traverseRTree' g (Leaf x) = Leaf <$> g x
-- traverseRTree' g (Branch branches) = foldr
--   (\branch, acc => ?help (Branch [traverse g branch, acc]))
--   (ret (Branch []))
--   branches

-- -- foldr (\(Branch acc) x => Branch $ (::) <$> traverseRTree' g x <*> acc) (ret []) xs


-- Some unit tests (if these fail we get type errors)

square : Num a => a -> a
square x = x * x

test1 : Maybe (Int, Bool)
test1 = applyMor (op_π₁ {p=Morphism} (Mor ProfunctorOptics.square)) (Just (3, True))

test2 : BTree Int
test2 = applyMor (inorder {p=Morphism} (Mor ProfunctorOptics.square)) (Node (Node Null 3 Null) 4 Null)

test3 : List Int
test3 = applyMor (listTraverse {p=Morphism} (Mor ProfunctorOptics.square)) [1,2,3,4]

testsPass :
  ( ProfunctorOptics.test1 = Just (9, True)
  -- , ProfunctorOptics.test2 = Node (Node Null 9 Null) 16 Null
  -- , ProfunctorOptics.test3 = [1,4,9,16]
  )

testsPass = (Refl) -- , Refl, Refl)
