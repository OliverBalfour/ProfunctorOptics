
module Zipper

-- Exercise 2: tree zipper

data BTree : Type -> Type where
  Branch : BTree a -> BTree a -> BTree a
  Leaf : a -> BTree a

data Context : Type -> Type where
  Top : Context a
  Left : Context a -> BTree a -> Context a
  Right : Context a -> BTree a -> Context a

Zipper : Type -> Type
Zipper a = (BTree a, Context a)

left : Zipper a -> Zipper a
left (Branch l r, ctx) = (l, Left ctx r)
left x = x

right : Zipper a -> Zipper a
right (Branch l r, ctx) = (r, Right ctx l)
right x = x

up : Zipper a -> Zipper a
up (l, Left ctx r) = (Branch l r, ctx)
up (r, Right ctx l) = (Branch l r, ctx)
up z@(_, Top) = z

top : BTree a -> Zipper a
top tree = (tree, Top)

ascend : Zipper a -> Zipper a
ascend z@(_, Top) = z
ascend z = ascend (up z)
