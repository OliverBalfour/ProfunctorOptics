
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
implementation VFunctor List where
  fmap f [] = []
  fmap f (x::xs) = f x :: fmap f xs
  fid [] = Refl
  fid (x::xs) = cong (x::) (fid xs)
  fcomp [] g h = Refl
  fcomp (x::xs) g h = cong (g (h x) ::) (fcomp xs g h)

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
