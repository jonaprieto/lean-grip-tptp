%------------------------------------------------------------------------------
% File     : SYN000-1 : TPTP v6.4.0. Released v4.0.0.
% Domain   : Syntactic
% Problem  : Basic TPTP CNF syntax
% Source   : [TPTP]
% Status   : Unsatisfiable
% SPC      : CNF_UNS_RFO_SEQ_NHN
%------------------------------------------------------------------------------
cnf(propositional,axiom,
    ( p0
    | ~ q0
    | r0
    | ~ s0 )).

cnf(first_order,axiom,
    ( p(X)
    | ~ q(X,a)
    | r(X,f(Y),g(X,f(Y),Z))
    | ~ s(f(f(f(b)))) )).

cnf(equality,axiom,
    ( f(Y) = g(X,f(Y),Z)
    | f(f(f(b))) != a
    | X = f(Y) )).

cnf(true_false,axiom,
    ( $true
    | $false )).

cnf(single_quoted,axiom,
    ( 'A proposition'
    | 'A predicate'(Y)
    | p('A constant')
    | p('A function'(a))
    | p('A \'quoted \\ escape\'') )).

cnf(numbered_name,axiom,
    ( p(X)
    | ~ q(X,a)
    | r(X,f(Y),g(X,f(Y),Z))
    | ~ s(f(f(f(b)))) )).

cnf(role_hypothesis,hypothesis,
    p(h)).

cnf(role_negated_conjecture,negated_conjecture,
    ~ p(X)).

include('Axioms/SYN000-0.ax').

/* This
   is a block
   comment.
*/

%------------------------------------------------------------------------------
