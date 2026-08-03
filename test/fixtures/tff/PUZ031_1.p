% Curated TF0 example from the official TPTP typed first-order tutorial.
tff(human_type,type,human: $tType).
tff(grade_type,type,grade: $tType).
tff(john_decl,type,john: human).
tff(a_decl,type,a: grade).
tff(f_decl,type,f: grade).
tff(grade_of_decl,type,grade_of: human > grade).
tff(created_equal_decl,type,created_equal: (human * human) > $o).

tff(all_created_equal,axiom,
    ! [H1:human,H2:human] : created_equal(H1,H2)).
tff(john_got_an_f,axiom,grade_of(john) = f).
tff(someone_got_an_a,axiom,?[H:grade]: H = a).
tff(a_is_not_f,axiom,a != f).
tff(there_is_someone_else,conjecture,
    ? [H:human] : (H != john & created_equal(H,john))).
