
module ProfunctorOptics

import Category.VProfunctor
import Category.VFunctor
import Category.Morphism
import Primitive.PrimitiveOptics
import Data.Vect

%default total
%hide Prelude.Interfaces.(<*>)
%hide Prelude.Interfaces.(<$>)

infixr 0 ~>

-- Profunctor optic types

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

-- Product types

-- π₁ : {p : Type -> Type -> Type} -> Cartesian p => p a b -> p (a, c) (b, c)
π₁ : Lens a b (a, c) (b, c)
π₁ = first

π₂ : Lens a b (c, a) (c, b)
π₂ = second

-- Optional types

-- op : {p : Type -> Type -> Type} -> Cocartesian p => p a b -> p (Maybe a) (Maybe b)
op : Prism a b (Maybe a) (Maybe b)
op = dimap (maybe (Left Nothing) Right) (either id Just) . right

-- Sum/coproduct types

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

-- This type is from van Laarhoven
-- https://twanvl.nl/blog/haskell/non-regular1
-- FunList a b t is isomorphic to ∃n. a^n × (b^n -> t)
-- which is equivalent to the type of a traversable (Pickering et. al. 2018)
-- It allows us to write optics for lists and trees
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

-- List traversals

listTraverse' : {f : Type -> Type} -> VApplicative f
  => (a -> f b)
  -> List a -> f (List b)
listTraverse' g [] = ret []
listTraverse' g (x::xs) = (::) <$> g x <*> listTraverse' g xs

listTraverse : {a, b : Type} -> Traversal a b (List a) (List b)
listTraverse = makeTraversal (listTraverse' single)

-- PrimPrism a b forms a Cocartesian profunctor
-- This allows us to convert primitive optics to profunctor optics

-- Definitions and lemmas from the Either bifunctor for `VProfunctor (PrimPrism a b)`
bimapEither : (a -> c) -> (b -> d) -> Either a b -> Either c d
bimapEither f g (Left x) = Left (f x)
bimapEither f g (Right x) = Right (g x)

bimapId : (z : Either a b) -> bimapEither (\x => x) (\x => x) z = z
bimapId (Left y) = Refl
bimapId (Right y) = Refl

bimapLemma : (g :  e -> t) -> (g' : b -> e) -> (x' : Either b a)
  -> bimapEither (g . g') (\x => x) x' = bimapEither g (\x => x) (bimapEither g' (\x => x) x')
bimapLemma g g' (Left x) = Refl
bimapLemma g g' (Right x) = Refl

public export
implementation {a : Type} -> {b : Type} -> VProfunctor (PrimPrism a b) where
  dimap f g (MkPrimPrism m b) = MkPrimPrism (bimapEither g id . m . f) (g . b)
  pid (MkPrimPrism m b) = cong (`MkPrimPrism` b) (
    extensionality (\x => bimapId (m x)))
  pcomp (MkPrimPrism m b) f' f g g' = cong (`MkPrimPrism` (\x => g (g' (b x))))
    (extensionality (\x => bimapLemma g g' (m (f' (f x)))))

public export
implementation {a : Type} -> {b : Type} -> Cocartesian (PrimPrism a b) where
  left (MkPrimPrism m b) = MkPrimPrism (either (bimapEither Left id . m) (Left . Right)) (Left . b)
  right (MkPrimPrism m b) = MkPrimPrism (either (Left . Left) (bimapEither Right id . m)) (Right . b)

-- Unit tests (if these fail we get type errors)

test1 : applyMor (op_π₁ {p=Morphism} (Mor (\x => x * x))) (Just (3, True)) = Just (9, True)
test1 = Refl

-- `Forget r` profunctor optics operate as getters
test2 : unForget (π₁ {p=Forget Int} (MkForget (\x => x))) (3, True) = 3
test2 = Refl

-- General proof of how π₁ {p=Forget r} operates like fst
forgetLeftProjection : {r,b : Type} -> (x : r) -> (y : b)
  -> fst (x, y) = unForget (π₁ {p=Forget r} (MkForget (\z => z))) (x, y)
forgetLeftProjection x y = Refl

-- Const profunctor optics recovers sum type constructors
test3 : op {p=Const} (MkConst 3) = MkConst (Just 3)
test3 = Refl
