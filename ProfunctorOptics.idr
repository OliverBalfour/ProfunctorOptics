
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

implementation Functor (FunList a b) where
  map f (Done t) = Done (f t)
  map f (More x l) = More x (map (f .) l)

implementation Applicative (FunList a b) where
  pure = Done
  Done f <*> l = map f l
  More x l <*> l2 = assert_total More x (map flip l <**> l2)

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

-- Dependently typed version of FunList (they're both isomorphic to ∃n. A^n x (B^n -> T))
-- I should use (n : Nat ** (Vect n a, Vect n b -> t)) as this has the right quantifier
-- data BoringList : Type -> Type -> Type -> Type where
--   MkBoringList : (n : Nat) -> (Vect n a, Vect n b -> t) -> BoringList a b t

-- traverse' : {p : Type -> Type -> Type} -> (Cocartesian p, Monoidal p)
--   => p a b
--   -> p (BoringList a c t) (BoringList b c t)
-- traverse' k = ?test

-- fuse' : BoringList b b t -> t
-- fuse' (MkBoringList n (as, bs2t)) = ?this_isn't_possible

-- How do I define this?
-- makeTraversal' : (s -> BoringList a b t) -> Traversal a b s t
-- makeTraversal' h k = dimap h fuse' (traverse' k)

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

-- TODO: left subtree prism for a binary tree
-- can we construct this from op?
-- leftSubtree : {a : Type} -> Prism a a (BTree a) (BTree a)
-- leftSubtree = prismFromPrim prim where
--   prim : PrimPrism (BTree a) (BTree a) (BTree a) (BTree a)
--   prim = MkPrimPrism match build where
--     match : BTree a -> Either (BTree a) (BTree a)
--     match Null = Left Null

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


-- Some tests
-- Aside: the fact that we can express unit tests on a type level means we get
-- *compiler errors when unit tests fail*. Isn't that beautiful?

-- square : Num a => a -> a
-- square x = x * x

-- -- can use (op {p=(~>)} . π₁ {p=(~>)}) instead, Idris doesn't guess p very well
-- test1 : op_π₁ {p=(~>)} ProfunctorOptics.square (Just (3, True)) = Just (9, True)
-- test1 = Refl

-- test2 : inorder {p=(~>)} ProfunctorOptics.square (Node (Node Empty 3 Empty) 4 Empty) = Node (Node Empty 9 Empty) 16 Empty
-- test2 = Refl

-- test3 : listTraverse {p=(~>)} ProfunctorOptics.square [1,2,3,4] = [1,4,9,16]
-- test3 = Refl


-- -- Ideas for more optics

-- -- index : Nat -> Prism on lists, gets/sets the nth item of a list if it exists
-- -- index' : Fin n -> Lens on Vect n a
