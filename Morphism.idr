
-- Derived from Data.Morphisms

module Morphism

%default total

-- Morphisms in the category of Idris types
public export
record Morphism a b where
  constructor Mor
  applyMor : a -> b

infixr 1 ~>

public export
(~>) : Type -> Type -> Type
(~>) = Morphism

-- Morphisms in a Kleisli category
public export
record Kleislimorphism (f : Type -> Type) a b where
  constructor Kleisli
  applyKleisli : a -> f b

infixr 1 ~~>

public export
(~~>) : {f : Type -> Type} -> Type -> Type -> Type
(~~>) = Kleislimorphism f

-- Helpers

public export
eta : (a -> b) -> (a -> b)
eta f = \x => f x

-- `f = \x => f x`
public export
ext : (f : a -> b) -> (eta f = f)
ext f = Refl

-- `id . f = f`
public export
idCompLeftId : (f : a -> b) -> (\x => x) . f = f
idCompLeftId f = ext f
