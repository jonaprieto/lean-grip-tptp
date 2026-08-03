% Curated FOF grammar coverage for the typed parser.
fof(universal, axiom, ! [X] : (p(X) => q(X))).
fof(connectives, axiom, ((p <=> q) & (r <~> s) & (t ~| u) & (v ~& w))).
fof(terms, axiom, f(-1, 1/2, 1.5E-2) = g('quoted', `X)).
fof(existential, conjecture, ? [X, Y] : (X = Y | X != Y)).
