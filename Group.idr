
module Group

%default total
%hide Monoid

infixl 7 <>

-- a group is a type with an associative binary function with an id and inverses
-- this record can represent verified groups of subsets of types (eg elements
-- of a type that satisfy a predicate)
-- it cannot directly encode groups of function types unfortunately
-- (eg for S_n you could use Vect n (Fin n) instead of Fin n -> Fin n)
record Group where
  constructor MkGroup
  -- components
  t : Type
  pred : t -> Type  -- should return () if we want t, Void otherwise
  (<>) : t -> t -> t
  neg : t -> t
  e : t
  -- laws
  closure : (x, y : t) -> (pred x, pred y) -> pred (x <> y)
  assoc : (x, y, z : t) -> (pred x, pred y, pred z) -> (x <> y) <> z = x <> (y <> z)
  identity : (x : t) -> pred x -> (e <> x = x, x <> e = x)
  inverses : (x : t) -> pred x -> (neg x <> x = e, x <> neg x = e)

record Monoid where
  constructor MkMonoid
  t : Type
  pred : t -> Type
  (<>) : t -> t -> t
  e : t
  closure : (x, y : t) -> (pred x, pred y) -> pred (x <> y)
  assoc : (x, y, z : t) -> (pred x, pred y, pred z) -> (x <> y) <> z = x <> (y <> z)
  identity : (x : t) -> pred x -> (e <> x = x, x <> e = x)

intAddAssoc : (x, y, z : Integer) -> ((),(),()) -> (x + y) + z = x + (y + z)
intAddId : (x : Integer) -> () -> (0 + x = x, x + 0 = x)
intAddInv : (x : Integer) -> () -> (-x + x = 0, x + -x = 0)
intAddClosure : (x, y : Integer) -> ((), ()) -> ()

intAdd : Group
intAdd = MkGroup Integer (const ()) (+) negate 0 intAddClosure intAddAssoc intAddId intAddInv

groupIsMonoid : Group -> Monoid
groupIsMonoid g = MkMonoid g.t g.pred ((<>) g) g.e g.closure g.assoc g.identity

-- equates any subgroups of the same group with extensional equality
subgroupsShareAncestor : Group -> Group -> Type
subgroupsShareAncestor h g =
  let a = g.t
      b = h.t
      gf = (<>) g
      hf = (<>) h
  in (x : a) -> (y : b) -> gf x x = hf y y

-- type of a proof H <= G
-- in other functions you can specify a `subgroup h g` prf as an argument
Subgroup : Group -> Group -> Type
Subgroup h g =
  ( subgroupsShareAncestor g h
  , (x : g.t) -> h.pred x -> g.pred x  -- x in H => x in G
  )

nZ : (n : Nat) -> Group
nZ = MkGroup Integer (\k => ()) (+) negate 0 intAddClosure intAddAssoc intAddId intAddInv
