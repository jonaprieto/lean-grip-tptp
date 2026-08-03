%------------------------------------------------------------------------------
% File     : PUZ001+1 : TPTP v6.4.0. Released v2.0.0.
% Domain   : Puzzles
% Problem  : Dreadbury Mansion
% Source   : [Hah94]
% Status   : Theorem
% SPC      : FOF_THM_RFO_SEQ
%------------------------------------------------------------------------------
fof(pel55_1,axiom,
    ( ? [X] :
        ( lives(X)
        & killed(X,agatha) ) )).

fof(pel55_2_1,axiom,
    ( lives(agatha) )).

fof(pel55_2_2,axiom,
    ( lives(butler) )).

fof(pel55_2_3,axiom,
    ( lives(charles) )).

fof(pel55_3,axiom,
    ( ! [X] :
        ( lives(X)
       => ( X = agatha
          | X = butler
          | X = charles ) ) )).

fof(pel55_4,axiom,
    ( ! [X,Y] :
        ( killed(X,Y)
       => hates(X,Y) ) )).

fof(pel55_5,axiom,
    ( ! [X,Y] :
        ( killed(X,Y)
       => ~ richer(X,Y) ) )).

fof(pel55_6,axiom,
    ( ! [X] :
        ( hates(agatha,X)
       => ~ hates(charles,X) ) )).

fof(pel55_7,axiom,
    ( ! [X] :
        ( X != butler
       => hates(agatha,X) ) )).

fof(pel55_8,axiom,
    ( ! [X] :
        ( ~ richer(X,agatha)
       => hates(butler,X) ) )).

fof(pel55_9,axiom,
    ( ! [X] :
        ( hates(agatha,X)
       => hates(butler,X) ) )).

fof(pel55_10,axiom,
    ( ! [X] :
      ? [Y] : ~ hates(X,Y) )).

fof(pel55_11,axiom,
    ( agatha != butler )).

fof(pel55,conjecture,
    ( killed(agatha,agatha) )).

%------------------------------------------------------------------------------
