
module Group

%default total
%hide Monoid

infixl 7 <>

-- a group is a type with an associative binary function with an id and inverses
-- this record can represent verified groups of subsets of types (eg elements
-- of a type that satisfy a predicate)
record Group where
  constructor MkGroup
  -- components
  t : Type
  -- pred : t -> Bool
  (<>) : t -> t -> t
  neg : t -> t
  e : t
  -- laws
  assoc : (x, y, z : t) -> (x <> y) <> z = x <> (y <> z)
  identity : (x : t) -> (e <> x = x, x <> e = x)
  inverses : (x : t) -> (neg x <> x = e, x <> neg x = e)

record Monoid where
  constructor MkMonoid
  t : Type
  (<>) : t -> t -> t
  e : t
  assoc : (x, y, z : t) -> (x <> y) <> z = x <> (y <> z)
  identity : (x : t) -> (e <> x = x, x <> e = x)

intAddAssoc : (x, y, z : Integer) -> (x + y) + z = x + (y + z)
intAddId : (x : Integer) -> (0 + x = x, x + 0 = x)
intAddInv : (x : Integer) -> (-x + x = 0, x + -x = 0)

intAdd : Group
intAdd = MkGroup Integer (+) negate 0 intAddAssoc intAddId intAddInv

groupIsMonoid : Group -> Monoid
groupIsMonoid g = MkMonoid g.t ((<>) g) g.e g.assoc g.identity
