% background
fluent(loaded). fluent(alive).
value(true). value(false).
action(load). action(shoot).

% transition generation
holds(loaded,true) :- occ(load).
holds(alive,false) :- occ(shoot), holds'(loaded,true).
holds(F,V) :- holds'(F,V), not holds(F,VV) : value(VV), VV != V.
{ occ(A) : action(A) } 1.
:- holds(alive,true), last.
#show occ/1.

% state generation
#external holds'(F,V) : fluent(F), value(V).

% other externals
#external last.

% init
init(holds(loaded,false)).
init(holds(alive,true)).

% more
action(wait).
done(wait) :- occ(wait).
done(wait) :- done'(wait).
:- last, not done(wait).
#external done'(wait).
