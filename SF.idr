
%default total

silly : (n, m : Nat) -> n = m -> n + n = m + m
silly n m prf = rewrite prf in Refl

ex2 : (n,m,o:Nat)->n=m->m=o->n+m=m+o
ex2 n m o nm mo = rewrite nm in rewrite sym mo in Refl

ex3 : (n : Nat) -> S n = Z -> Void
ex3 n p impossible

ex3alt : (n : Nat) -> S n == Z = False
ex3alt _ = Refl

andb_true_elim2 : (b,c: Bool) -> b && c = True -> c = True
andb_true_elim2 b True prf = Refl
andb_true_elim2 False False prf impossible
andb_true_elim2 True False prf impossible

andb_true_elim2alt : (b, c) -> c
andb_true_elim2alt = snd
