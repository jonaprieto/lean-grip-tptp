tff(nat_type,type,nat: $tType).
tff(zero_type,type,zero: nat).
tff(succ_type,type,succ: nat > nat).
tff(add_type,type,add: (nat * nat) > nat).
tff(add_zero,axiom,![X:nat]: add(X,zero) = X).
