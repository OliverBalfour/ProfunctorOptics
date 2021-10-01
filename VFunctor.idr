
module VFunctor

import Morphism
import Data.Vect

%default total
%hide Applicative
%hide (<*>)

infixl 4 <*>

-- Verified functors
public export
interface VFunctor (f : Type -> Type) where
  fmap : (a -> b) -> (f a -> f b)
  fid : (x : f a)
    -> fmap (\x => x) x = x
  fcomp : (x : f a) -> (g : b -> c) -> (h : a -> b)
    -> fmap (g . h) x = (fmap g . fmap h) x

public export
interface VFunctor f => VApplicative (f : Type -> Type) where
  ret : a -> f a
  (<*>) : f (a -> b) -> (f a -> f b)
  aid : (v : f a) -> ret (\x => x) <*> v = v
  ahom : (g : a -> b) -> (x : a)
    -> ret g <*> ret x = ret (g x)
  aint : (u : f (a -> b)) -> (y : a)
    -> u <*> ret y = ret ($ y) <*> u
  acomp : (u : f (b -> c)) -> (v : f (a -> b)) -> (w : f a)
    -> ((ret (.) <*> u) <*> v) <*> w = u <*> (v <*> w)
  -- As lawful fmap implementations are unique and `fmap f x = pure f <*> x`
  -- satisfies functor laws, this is always true
  -- afmap : (g : a -> b) -> (x : f a) -> ret g <*> x = g `fmap` x

public export
implementation VFunctor List where
  fmap f [] = []
  fmap f (x::xs) = f x :: fmap f xs
  fid [] = Refl
  fid (x::xs) = cong (x::) (fid xs)
  fcomp [] g h = Refl
  fcomp (x::xs) g h = cong (g (h x) ::) (fcomp xs g h)

public export
nilRightId : (xs : List a) -> xs ++ [] = xs
nilRightId [] = Refl
nilRightId (x::xs) =
  let iH = nilRightId xs
  in rewrite iH in Refl

public export
concatAssoc : (xs, ys, zs : List a) -> xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
concatAssoc [] ys zs = Refl
concatAssoc (x::xs) ys zs = cong (x::) (concatAssoc xs ys zs)

public export
implementation VApplicative List where
  ret = (::[])
  (<*>) [] xs = []
  (<*>) (f::fs) xs = fmap f xs ++ (fs <*> xs)
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
    in rewrite elimNil in
      -- Goal: ((fmap (.) <*> us) vs) <*> ws = us <*> (vs <*> ws)
      case us of
        [] => Refl
        (u::us') => let iH = acomp us' vs ws in
          let l1 : List (a -> c)
              l1 = fmap ((.) u) vs
              l2 : List (a -> c)
              l2 = (fmap (.) us') <*> vs
              step : ((l1 ++ l2) <*> ws = (l1 <*> ws) ++ (l2 <*> ws))
              step = concatHom l1 l2 ws
              elimNil2 : (fmap u (vs <*> ws) ++ (<*>) ((fmap (.) us' ++ []) <*> vs) ws = fmap u (vs <*> ws) ++ (((fmap (.) us') <*> vs) <*> ws))
              elimNil2 = cong (\x => fmap u (vs <*> ws) ++ (<*>) (x <*> vs) ws) (nilRightId (fmap (.) us'))
              prf : ((l1 ++ l2) <*> ws = fmap u (vs <*> ws) ++ (us' <*> (vs <*> ws)))
              prf = rewrite step in rewrite sym iH in rewrite elimNil2 in
                cong (++ (((fmap (.) us') <*> vs) <*> ws)) (
                  -- Goal: ((fmap ((.) u) vs) <*> ws = fmap u (vs <*> ws))
                  case vs of
                    [] => Refl
                    (v::vs') =>
                      let iH2 = acomp us' vs' ws
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
      apRightNil : (fs : List (p -> q)) -> fs <*> [] = []
      apRightNil [] = Refl
      apRightNil (f::fs) = apRightNil fs
      concatHom : (as, bs : List (p -> q)) -> (xs : List p)
          -> (as ++ bs) <*> xs = (as <*> xs) ++ (bs <*> xs)
      concatHom [] bs xs = Refl
      concatHom (a::as) bs xs = rewrite concatHom as bs xs in
        concatAssoc (fmap a xs) (as <*> xs) (bs <*> xs)
      fmapHom : (m : p -> q) -> (as, bs : List p)
        -> fmap m as ++ fmap m bs = fmap m (as ++ bs)
      fmapHom m [] bs = Refl
      fmapHom m (a::as) bs = rewrite fmapHom m as bs in Refl
      apLemma : (m : q -> r) -> (as : List (p -> q)) -> (bs : List p)
        -> ((fmap ((.) m) as) <*> bs = fmap m (as <*> bs))
      apLemma m [] bs = Refl
      apLemma m (a::as) bs =
        let iH = apLemma m as bs
        in rewrite sym (fmapHom m (fmap a bs) (as <*> bs))
        in rewrite sym iH
        in rewrite fcomp bs m a
        in Refl

public export
implementation VFunctor Maybe where
  fmap f (Just x) = Just (f x)
  fmap f Nothing = Nothing
  fid (Just x) = Refl
  fid Nothing = Refl
  fcomp (Just x) g h = Refl
  fcomp Nothing g h = Refl

public export
implementation VApplicative Maybe where
  ret = Just
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

-- (a,) is only an applicative if a is a monoid
public export
implementation {a:Type} -> VFunctor (a,) where
  fmap f (x, y) = (x, f y)
  fid (x, y) = Refl
  fcomp (x, y) g h = Refl

public export
implementation {a:Type} -> VFunctor (Morphism a) where
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

public export
implementation {n:Nat} -> VFunctor (Vect n) where
  fmap f [] = []
  fmap f (x::xs) = f x :: fmap f xs
  fid [] = Refl
  fid (x::xs) = cong (x::) (fid xs)
  fcomp [] g h = Refl
  fcomp (x::xs) g h = cong (g (h x) ::) (fcomp xs g h)

plusZeroRightId : (n : Nat) -> n + 0 = n
plusZeroRightId Z = Refl
plusZeroRightId (S n) = rewrite plusZeroRightId n in Refl

vectPlusZero : {n : Nat} -> Vect (plus n 0) a -> Vect n a
vectPlusZero xs = replace {p = \prf => Vect prf a} (plusZeroRightId n) xs

-- TODO: VApplicative (Vect n)
-- This requires vectNilRightId : (xs : Vect n a) -> xs ++ [] = xs
-- This doesn't work because Idris can't resolve len ~ plus len 0 in the body,
-- but len is inaccessible so we can't use vectPlusZero to help us
-- vectNilRightId : (xs : Vect n a) -> vectPlusZero (xs ++ []) = xs
-- vectNilRightId [] = Refl
-- vectNilRightId (x::xs) = cong (x::) (vectNilRightId xs)

public export
data BTree : Type -> Type where
  Null : BTree a
  Node : BTree a -> a -> BTree a -> BTree a

public export
implementation VFunctor BTree where
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

public export
data RTree : Type -> Type where
  Leaf : a -> RTree a
  Branch : List (RTree a) -> RTree a

-- These are for VFunctor RTree but had to be pulled out so branches
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
