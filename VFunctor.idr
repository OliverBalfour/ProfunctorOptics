
module VFunctor

import Morphism

%default total

-- Verified functors
public export
interface VFunctor (f : Type -> Type) where
  fmap : (a -> b) -> (f a -> f b)
  fid : (x : f a)
    -> fmap (\x => x) x = x
  fcomp : (x : f a) -> (g : b -> c) -> (h : a -> b)
    -> fmap (g . h) x = (fmap g . fmap h) x

public export
interface VApplicative (f : Type -> Type) where
  ret : a -> f a
  splat : f (a -> b) -> (f a -> f b)
  aid : (v : f a) -> ret (\x => x) `splat` v = v
  ahom : (g : a -> b) -> (x : a)
    -> ret g `splat` ret x = ret (g x)
  aint : (u : f (a -> b)) -> (y : a)
    -> u `splat` ret y = ret ($ y) `splat` u
  acomp : (u : f (b -> c)) -> (v : f (a -> b)) -> (w : f a)
    -> ((ret (.) `splat` u) `splat` v) `splat` w = u `splat` (v `splat` w)

public export
implementation VFunctor List where
  fmap f [] = []
  fmap f (x::xs) = f x :: fmap f xs
  fid [] = Refl
  fid (x::xs) = cong (x::) (fid xs)
  fcomp [] g h = Refl
  fcomp (x::xs) g h = cong (g (h x) ::) (fcomp xs g h)

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
  splat (Just f) (Just x) = Just (f x)
  splat _ _ = Nothing
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
implementation {a:Type} -> VFunctor (a,) where
  fmap f (x, y) = (x, f y)
  fid (x, y) = Refl
  fcomp (x, y) g h = Refl

public export
implementation {a:Type} -> VFunctor (Morphism a) where
  fmap f (Mor g) = Mor (f . g)
  fid (Mor f) = cong Mor (sym (ext f))
  fcomp (Mor f) g h = Refl
