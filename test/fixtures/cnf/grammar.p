% Curated CNF grammar coverage for the typed parser.
cnf(unit, axiom, p(a)).
cnf(disjunction, axiom, (p(a) | ~(q(a)) | r(a) != s(a))).
cnf(nested, conjecture, ((p(a) | ~q(a)))).
cnf(empty, plain, $false).
