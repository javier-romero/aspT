% background

dom(1..10).
{a(X)} :- dom(X).
{b(X)} :- dom(X).
:- a(X), b(X).
:- a(X), not b(X).
:- not a(X), b(X).
a :- a(X).
a :- b(X).
%
%%%%%%%%%%%%%%%%%%%%%%%%%%% HEADS
%
% DISJUNCTION, TRUE
e :- not a(X) : dom(X).
a ; e.
% DISJUNCTION, FALSE and FACT
b(X) : dom(X) ; c.
a :- not c.
% DISJUNCTION, FALSE and 1-CONSTRAINT
b(X) : dom(X) :- not d.
{ d }.
a :- not d.
% CHOICE
% TRUE AND FALSE
f :- not 1 #sum { 1: a(X); 1: b(X) }.
:- g, not a(X) : dom(X).
{ f ; g } :- not a.
%
%%%%%%%%%%%%%%%%%%%%%%%% WHEADS
%
% DISJUNCTION, TRUE
h :- not a(X) : dom(X); not b(X) : dom(X).
a ; h :- 10 #sum { 10,X: not a(X), dom(X); 20,X: not b(X), dom(X) }.
% DISJUNCTION, FALSE and FACT
b(X) : dom(X); i :- 10 #sum { 10,X: not a(X), dom(X); 20,X: not b(X), dom(X) }.
a :- not i.
% DISJUNCTION, FALSE and 1-CONSTRAINT
b(X) : dom(X) :- 0 #sum { 1,X : a(X); -1: j }.
{ j }.
a :- not j.
% CHOICE
% TRUE AND FALSE
k :- not 1 #sum { 1: a(X); 1: b(X) }.
:- l, not a(X) : dom(X).
{ k ; l } :- 0 #sum { -1: a; 1,X: a(X) }.
%
%%%%%%%%%%%%%%%%%%%%%% SATISFIED BODY
%
% SATISFIED BODY, FACT
m :- not a(X), dom(X).
a :- not m.
% SATISFIED BODY, 1-c
n :- o, not a(X), not b(X), dom(X).
{ o }.
:- n, not a(X) : dom(X).
a :- o.
%
%%%%%%%%%%%%%%%%%%%%%%%%% UNSATISFIED BODY
%
p(X) :- a(X), not b(X) : dom(X).
a :- p(X).
#show a/1.
%
%%%%%%%%%%%%%%%%%%%% SATISFIED WBODY
%
% SATISFIED WBODY, FACT
q :- 100 #sum { 100,X: not a(X), not b(X), dom(X) }.
a :- not q.
% SATISFIED WBODY, not FACT
{ r ; s } :- 100 #sum { 100,X: not a(X), dom(X); 100,X: not b(X), dom(X) }.
:- not a(X): dom(X); r.
:- not a(X): dom(X); s.
a :- r.
a :- s.
% SATISFIED WBODY, 1-CONSTRAINT
:- 200 #sum { 100,X: a(X); 100,X: b(X); 100,a(1): not a(1); 100,t: not t }.
{ t }.
a :- not t.
%
%%%%%%%%% INPUT CONSTRAINTS and WRULES
%
{ u; w; x }.
:- u.
:- not w.
y :- 3 #sum { 3: x }.
:- y, not a(X) : dom(X).
a :- u.
a :- not w.
a :- x.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fluent(loaded) :- not a.
fluent(alive)  :- not a.

value(true). value(false).
action(load). action(shoot).
#show fluent/1.

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

% extension: always one wait action
action(wait).
done(wait) :- occ(wait).
done(wait) :- done'(wait).
:- last, not done(wait).
#external done'(wait).
