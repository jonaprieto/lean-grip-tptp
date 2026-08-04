%----TF1-style polymorphic list and map declarations.
tff(bird_type,type,bird: $tType).
tff(list_type,type,list: $tType > $tType).
tff(map_type,type,map: ($tType * $tType) > $tType).
tff(nil_type,type,nil: !>[A:$tType] : list(A)).
tff(cons_type,type,cons: !>[A:$tType] : ((A * list(A)) > list(A))).
tff(is_empty_type,type,is_empty: !>[A:$tType] : (list(A) > $o)).
tff(lookup_type,type,lookup: !>[A:$tType,B:$tType] : ((map(A,B) * A) > B)).

tff(bird_list_not_empty,axiom,
    ![B:bird,Bs:list(bird)] : ~is_empty(bird,cons(bird,B,Bs))).
tff(lookup_same,axiom,
    ![A:$tType,B:$tType,M:map(A,B),K:A,V:B] : lookup(A,B,M,K) = V).
