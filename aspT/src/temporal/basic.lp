#program base. % as strips-incremental.lp

% Define unsubsumed mutexes

mutex(G,X) :- mutexGroup(G), contains(G,X,V). %, fluent(X,V).
mutex(G)   :- mutexGroup(G), #count{X : mutex(G,X)} > 1.

% Define initial state

init(holds(X,V)) :- initialState(X,V). %, fluent(X).

%%%#program step(t). % new

% generate (a SAT problem)
{     holds(X,V) } :- contains(X,V).
{ occurs(A) : action(A) }.

% effects
:- occurs(A), postcondition(A,_,X,V), not holds(X,V).

% preconditions
:- occurs(A), precondition(A,X,V),    not holds'(X,V).

% inertia
:- holds(X,V), not holds'(X,V),
   not occurs(A) : postcondition(A,_,X,V).

% existence and uniqueness of value
:- not 1 { holds(X,V) } 1, variable(X).

% mutexes
:- 2 #sum { 1,X,V: holds(X,V), contains(mutexGroup(G),X,V) }, mutex(G).

%%%#program check(t). % as strips-incremental.lp

% Check goal conditions

:- last, goal(X,V), not holds(X,V).
#show occurs/1.

% NEW: GENERATE STATE
#external holds'(X,V) : contains(X,V).

% NEW: LAST ATOM
#external last.
