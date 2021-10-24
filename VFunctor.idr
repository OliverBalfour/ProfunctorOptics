
module VFunctor

import Morphism
import Data.Vect

%default total
%hide Applicative
%hide (<*>)

infixl 4 <*>

-- Verified functors
-- Optics over functorial types can be verified in part using functor laws
public export
interface VFunctor (f : Type -> Type) where
  -- fmap maps functions
  fmap : (a -> b) -> (f a -> f b)
  -- fmap respects identity, F(id) = id
  fid : (x : f a)
    -> fmap (\x => x) x = x
  -- fmap respects composition, F(g . h) = F(g) . F(h)
  fcomp : (x : f a) -> (g : b -> c) -> (h : a -> b)
    -> fmap (g . h) x = (fmap g . fmap h) x

-- Verified applicative functors
public export
interface VFunctor f => VApplicative (f : Type -> Type) where
  -- pure (aka return, η)
  ret : a -> f a
  -- ap
  (<*>) : f (a -> b) -> (f a -> f b)
  -- identity law, pure id <*> v = v
  aid : (v : f a) -> ret (\x => x) <*> v = v
  -- homomorphism law, pure g <*> pure x = pure (g x)
  ahom : (g : a -> b) -> (x : a)
    -> ret g <*> ret x = ret (g x)
  -- interchange law, u <*> pure y = pure ($ y) <*> u
  aint : (u : f (a -> b)) -> (y : a)
    -> u <*> ret y = ret ($ y) <*> u
  -- composition law, ((pure (.) <*> u) <*> v) <*> w = u <*> (v <*> w)
  acomp : (u : f (b -> c)) -> (v : f (a -> b)) -> (w : f a)
    -> ((ret (.) <*> u) <*> v) <*> w = u <*> (v <*> w)

-- Lists are functors
public export
implementation VFunctor List where
  -- fmap for lists is map
  fmap f [] = []
  fmap f (x::xs) = f x :: fmap f xs
  fid [] = Refl
  fid (x::xs) = cong (x::) (fid xs)
  fcomp [] g h = Refl
  fcomp (x::xs) g h = cong (g (h x) ::) (fcomp xs g h)

-- forall xs. xs ++ [] = xs
public export
nilRightId : (xs : List a) -> xs ++ [] = xs
nilRightId [] = Refl
nilRightId (x::xs) =
  let iH = nilRightId xs
  in rewrite iH in Refl

-- List concatenation is associative
public export
concatAssoc : (xs, ys, zs : List a) -> xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
concatAssoc [] ys zs = Refl
concatAssoc (x::xs) ys zs = cong (x::) (concatAssoc xs ys zs)

-- Lists are applicative functors
public export
implementation VApplicative List where
  -- pure makes a singleton list
  ret = (::[])
  -- ap applies a list of functions to a list of arguments
  -- [f1, ..., fn] <*> [x1, ..., xn] = [f1 x1, ..., f1 xn, f2 x1, ..., fn xn]
  (<*>) [] xs = []
  (<*>) (f::fs) xs = fmap f xs ++ (fs <*> xs)
  -- Laws
  aid [] = Refl
  aid (x::xs) =
    let iH = aid xs
        shed : (fmap (\x => x) xs = xs) = fid xs
        prf : ((fmap (\y => y) xs ++ []) = xs)
        prf = rewrite shed in rewrite nilRightId xs in Refl
    in cong (x::) prf
  ahom g x = Refl
  aint [] y = Refl
  aint (u::us) y =
    let iH = aint us y
    in cong (u y::) iH
  acomp us vs ws =
    let elimNil : (((fmap (.) us ++ []) <*> vs) <*> ws = ((fmap (.) us) <*> vs) <*> ws)
        elimNil = cong (\x => (x <*> vs) <*> ws) (nilRightId (fmap (.) us))
    in rewrite elimNil in case us of
      -- Goal: ((fmap (.) <*> us) vs) <*> ws = us <*> (vs <*> ws)
      [] => Refl
      (u::us') => let iH = acomp us' vs ws in let
        l1 : List (a -> c)
        l1 = fmap ((.) u) vs
        l2 : List (a -> c)
        l2 = (fmap (.) us') <*> vs
        step : ((l1 ++ l2) <*> ws = (l1 <*> ws) ++ (l2 <*> ws))
        step = concatDist l1 l2 ws
        elimNil2 : (fmap u (vs <*> ws) ++ (<*>) ((fmap (.) us' ++ []) <*> vs) ws = fmap u (vs <*> ws) ++ (((fmap (.) us') <*> vs) <*> ws))
        elimNil2 = cong (\x => fmap u (vs <*> ws) ++ (<*>) (x <*> vs) ws) (nilRightId (fmap (.) us'))
        prf : ((l1 ++ l2) <*> ws = fmap u (vs <*> ws) ++ (us' <*> (vs <*> ws)))
        prf = rewrite step in rewrite sym iH in rewrite elimNil2 in
          cong (++ (((fmap (.) us') <*> vs) <*> ws)) (
            -- Goal: ((fmap ((.) u) vs) <*> ws = fmap u (vs <*> ws))
            case vs of
              [] => Refl
              (v::vs') => let
                iH2 = acomp us' vs' ws
                step2 : ((<*>) (fmap ((.) u) vs') ws = fmap u (vs' <*> ws))
                step2 = apLemma u vs' ws
                step3 : (fmap (u . v) ws ++ (<*>) (fmap ((.) u) vs') ws = fmap (u . v) ws ++ fmap u (vs' <*> ws))
                step3 = cong (fmap (u . v) ws ++) step2
                step4 : (fmap (u . v) ws ++ fmap u (vs' <*> ws) = fmap u (fmap v ws) ++ fmap u (vs' <*> ws))
                step4 = rewrite fcomp ws u v in Refl
                step5 : (fmap u (fmap v ws) ++ fmap u (vs' <*> ws) = fmap u (fmap v ws ++ (vs' <*> ws)))
                step5 = fmapHom u (fmap v ws) (vs' <*> ws)
                final : (fmap (u . v) ws ++ ((fmap ((.) u) vs') <*> ws) = fmap u (fmap v ws ++ (vs' <*> ws)))
                final = (step3 `trans` step4) `trans` step5
                in final
            )
        in prf
    where
      -- Lemmas
      -- Empty xs gives empty fs <*> xs
      apRightNil : (fs : List (p -> q)) -> fs <*> [] = []
      apRightNil [] = Refl
      apRightNil (f::fs) = apRightNil fs
      -- (<*>) distributes over (++)
      concatDist : (as, bs : List (p -> q)) -> (xs : List p)
          -> (as ++ bs) <*> xs = (as <*> xs) ++ (bs <*> xs)
      concatDist [] bs xs = Refl
      concatDist (a::as) bs xs = rewrite concatDist as bs xs in
        concatAssoc (fmap a xs) (as <*> xs) (bs <*> xs)
      -- fmap is a monoid homomorphism over the (List a, (++), []) monoid
      fmapHom : (m : p -> q) -> (as, bs : List p)
        -> fmap m as ++ fmap m bs = fmap m (as ++ bs)
      fmapHom m [] bs = Refl
      fmapHom m (a::as) bs = rewrite fmapHom m as bs in Refl
      -- Function composition can be done before or after (<*>)
      apLemma : (m : q -> r) -> (as : List (p -> q)) -> (bs : List p)
        -> ((fmap ((.) m) as) <*> bs = fmap m (as <*> bs))
      apLemma m [] bs = Refl
      apLemma m (a::as) bs =
        let iH = apLemma m as bs
        in rewrite sym (fmapHom m (fmap a bs) (as <*> bs))
        in rewrite sym iH
        in rewrite fcomp bs m a
        in Refl

-- Maybe is an applicative functor
public export
implementation VFunctor Maybe where
  -- fmap maps over Just values
  fmap f (Just x) = Just (f x)
  fmap f Nothing = Nothing
  fid (Just x) = Refl
  fid Nothing = Refl
  fcomp (Just x) g h = Refl
  fcomp Nothing g h = Refl

public export
implementation VApplicative Maybe where
  ret = Just
  -- ap returns a Just value iff it's possible to do so
  (<*>) (Just f) (Just x) = Just (f x)
  (<*>) _ _ = Nothing
  aid (Just x) = Refl
  aid Nothing = Refl
  ahom g x = Refl
  aint (Just f) y = Refl
  aint Nothing y = Refl
  acomp (Just u) (Just v) (Just w) = Refl
  acomp Nothing _ _ = Refl
  acomp (Just u) Nothing _ = Refl
  acomp (Just u) (Just v) Nothing = Refl

-- Either a (partially applied sum type) is an applicative functor
-- over the second type variable
public export
implementation {a:Type} -> VFunctor (Either a) where
  fmap f (Left x) = Left x
  fmap f (Right x) = Right (f x)
  fid (Left x) = Refl
  fid (Right x) = Refl
  fcomp (Left x) g h = Refl
  fcomp (Right x) g h = Refl

public export
implementation {a:Type} -> VApplicative (Either a) where
  ret = Right
  -- same as VApplicative Maybe, Left x is treated as Nothing and Right x
  -- as Just x
  (<*>) (Right f) (Right x) = Right (f x)
  (<*>) (Left x) y = Left x
  (<*>) _ (Left x) = Left x
  aid (Left x) = Refl
  aid (Right x) = Refl
  ahom g x = Refl
  aint (Left x) y = Refl
  aint (Right x) y = Refl
  acomp (Right u) (Right v) (Right w) = Refl
  acomp (Left _) _ _ = Refl
  acomp (Right u) (Left x) _ = Refl
  acomp (Right u) (Right v) (Left x) = Refl

-- Partially applied product type is a functor
-- over the second type variable
-- (a,) is only an applicative if a is a monoid (omitted)
public export
implementation {a:Type} -> VFunctor (a,) where
  fmap f (x, y) = (x, f y)
  fid (x, y) = Refl
  fcomp (x, y) g h = Refl

-- Morphism a = Hom(a, -) is an applicative functor,
-- the covariant Hom functor
public export
implementation {a:Type} -> VFunctor (Morphism a) where
  -- fmap is function composition
  -- The Mor wrapper is only present to help Idris unify types in proofs
  fmap f (Mor g) = Mor (f . g)
  fid (Mor f) = cong Mor (sym (ext f))
  fcomp (Mor f) g h = Refl

public export
implementation {a:Type} -> VApplicative (Morphism a) where
  ret x = Mor (const x)
  (<*>) (Mor f) (Mor g) = Mor (\x => f x (g x))
  aid (Mor x) = Refl
  ahom g x = Refl
  aint (Mor f) y = Refl
  acomp (Mor u) (Mor v) (Mor w) = Refl

plusZeroRightId : (n : Nat) -> n + 0 = n
plusZeroRightId Z = Refl
plusZeroRightId (S n) = rewrite plusZeroRightId n in Refl

vectPlusZero : {n : Nat} -> Vect (plus n 0) a -> Vect n a
vectPlusZero xs = replace {p = \prf => Vect prf a} (plusZeroRightId n) xs

-- As with lists, length indexed vectors are functors
public export
implementation {n:Nat} -> VFunctor (Vect n) where
  fmap f [] = []
  fmap f (x::xs) = f x :: fmap f xs
  fid [] = Refl
  fid (x::xs) = cong (x::) (fid xs)
  fcomp [] g h = Refl
  fcomp (x::xs) g h = cong (g (h x) ::) (fcomp xs g h)

-- Binary trees are functors
public export
data BTree : Type -> Type where
  Null : BTree a
  Node : BTree a -> a -> BTree a -> BTree a

public export
implementation VFunctor BTree where
  -- fmap maps f recursively over the values in every node
  fmap f Null = Null
  fmap f (Node l x r) = Node (fmap f l) (f x) (fmap f r)
  fid Null = Refl
  fid (Node l x r) =
    let iH1 = fid l
        iH2 = fid r
    in rewrite iH1
    in rewrite iH2
    in Refl
  fcomp Null g h = Refl
  fcomp (Node l x r) g h =
    let iH1 = fcomp l g h
        iH2 = fcomp r g h
    in rewrite iH1
    in rewrite iH2
    in Refl

-- Rose trees are functors
public export
data RTree : Type -> Type where
  Leaf : a -> RTree a
  Branch : List (RTree a) -> RTree a

-- These are for VFunctor RTree but had to be pulled out so `branches`
-- could be used in a proof about fmap as well as fmap
mutual
  branches : (a -> b) -> List (RTree a) -> List (RTree b)
  branches f [] = []
  branches f (b::bs) = fmapRTree f b :: branches f bs

  fmapRTree : (a -> b) -> (RTree a) -> (RTree b)
  fmapRTree f (Leaf x) = Leaf (f x)
  fmapRTree f (Branch bs) = Branch (branches f bs)

public export
implementation VFunctor RTree where
  fmap = fmapRTree
  fid (Leaf x) = Refl
  fid (Branch bs) = cong Branch (prf bs) where
    prf : (bs : List (RTree a)) -> branches (\x => x) bs = bs
    prf [] = Refl
    prf (b::bs) = rewrite prf bs in cong (::bs) (fid b)
  fcomp (Leaf x) g h = Refl
  fcomp (Branch bs) g h = cong Branch (prf bs g h) where
    prf : (bs : List (RTree a)) -> (g : b -> c) -> (h : a -> b)
      -> (branches (g . h) bs = branches g (branches h bs))
    prf [] g h = Refl
    prf (b::bs) g h = rewrite prf bs g h
      in cong (:: branches g (branches h bs)) (fcomp b g h)
