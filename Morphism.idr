
-- Derived from Data.Morphisms

module Morphism

%default total

-- Morphisms in the category of Idris types
-- This wrapper exists to help Idris unify types in some proofs
public export
record Morphism a b where
  constructor Mor
  applyMor : a -> b

infixr 1 ~>

public export
(~>) : Type -> Type -> Type
(~>) = Morphism

-- Morphisms in a Kleisli category
-- Functions of type a -> f b for a functor or monad f
public export
record KleisliMorphism (f : Type -> Type) a b where
  constructor Kleisli
  applyKleisli : a -> f b

infixr 1 ~~>

public export
(~~>) : {f : Type -> Type} -> Type -> Type -> Type
(~~>) = KleisliMorphism f

-- Helpers

public export
eta : (a -> b) -> (a -> b)
eta f = \x => f x

-- f = \x => f x
public export
ext : (f : a -> b) -> (eta f = f)
ext f = Refl

-- id . f = f
public export
idCompLeftId : (f : a -> b) -> (\x => x) . f = f
idCompLeftId f = ext f

-- Extensionality axiom: used sparingly, uses a back door in the type system
-- Idris cannot rewrite types using axioms so this must be avoided at all costs
public export
extensionality : {f, g : a -> b} -> ((x : a) -> f x = g x) -> f = g
extensionality {f} {g} prf = believe_me ()

-- Alias for Prelude <*> which we hide
infixl 4 <**>
public export
(<**>) : Applicative f => f (a -> b) -> f a -> f b
(<**>) = (<*>)
