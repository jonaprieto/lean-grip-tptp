% Conservative common syntax accepted by both Lean and E.
fof(operators, axiom, ! [X] : ((p(X) & q(X)) => (r(X) | ~s(X)))).
fof(equality, conjecture, ! [X] : (f(-1, 1/2, 1.5E-2) = g(X))).
fof(quoted, axiom, 'quoted proposition').
cnf(disjunction, axiom, (p(a) | ~q(a) | r(a))).
