% Conservative FOF/CNF syntax shared with installed prover parsers.
fof(implication, axiom, ! [X] : (p(X) => q(X))).
fof(biconditional, conjecture, (p <=> q)).
cnf(disjunction, axiom, (p(a) | ~q(a))).
