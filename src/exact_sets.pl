% a module containing predicates implementing an exact set,
% i.e. sets capable of dealing with variables

:- module(exact_sets, [l_insert/3,
                       exact_subset/2,
                       exact_subset_of_two/3,
                       exact_subset_of_three/4,
                       exact_subset_of_four/5,
                       exact_inter/3,
                       exact_rem/3]).

:- use_module(library(plunit)).

l_insert([],R,R).
l_insert([V|T],In,Out) :- insert(In,V,In2),
  l_insert(T,In2,Out).


insert([],X,[X]).
insert([H|T],X,R) :-  (H==X -> R=[H|T] ; R=[H|R2],insert(T,X,R2)).

exact_subset([],_).
exact_subset([H|T],L) :- exact_del(H,L,L2), exact_subset(T,L2).

:- begin_tests(exact_subset).

test(exact_subset1) :-
    exact_subset([], _).

test(exact_subset2) :-
    exact_subset([A,B,C], [A,_D,C,B]).

test(exact_subset3, fail) :-
    exact_subset([_A,B,C], [_D,C,B]).

:- end_tests(exact_subset).


% checks whether first argument is subset of the union of the second and third argument
exact_subset_of_two([],_,_).
exact_subset_of_two([H|T],L1,L2) :- 
   (exact_del(H,L1,L12) ->  exact_subset_of_two(T,L12,L2)
            ; (exact_del(H,L2,L22), exact_subset_of_two(T,L1,L22))
   ).

:- begin_tests(exact_subset_of_two).

test(exact_subset_of_two1) :-
    exact_subset_of_two([], _, _).

test(exact_subset_of_two2) :-
    exact_subset_of_two([A,B,C], [A,_D,C,B], [_E,_F]).

test(exact_subset_of_two3) :-
    exact_subset_of_two([A,B,C], [A,_D,C], [B, _E,_F]).

test(exact_subset_of_two4, fail) :-
    exact_subset_of_two([_A,B,C], [_D,C,B], []).

:- end_tests(exact_subset_of_two).


% checks whether first argument is subset of the union of the second, third and fourth argument
exact_subset_of_three([],_,_,_).
exact_subset_of_three([H|T],L1,L2,L3) :- 
   (exact_del(H,L1,L12) ->  exact_subset_of_three(T,L12,L2,L3)
            ; (exact_del(H,L2,L22) -> exact_subset_of_three(T,L1,L22,L3)
                    ; (exact_del(H,L3,L32), exact_subset_of_three(T,L1,L2,L32))
              )
   ).

exact_subset_of_four(X,L1,L2,L3,L4) :- append(L3,L4,L34), /* to be improved */ exact_subset_of_three(X,L1,L2,L34).
   
exact_del(X,[Y|T],R) :-
   (X==Y -> R=T ; R=[Y|R2],exact_del(X,T,R2)).


exact_inter([],_R,[]).
exact_inter([H1|T1],L2,Res) :-
	(exact_del(H1,L2,L2D)
	 -> Res = [H1|RR]
	 ;  (L2D=L2, Res=RR)
	),exact_inter(T1,L2D,RR).


%% removes all elements from the first argument list from the second argument list
exact_rem([],R,R).
exact_rem([H|T],In,Out) :-
  (exact_del(H,In,In2)
    -> exact_rem(T,In2,Out)
     ; exact_rem(T,In,Out)
  ).


:- begin_tests(exact_rem).

test(exact_rem1) :-
    exact_rem([], [], []).

test(exact_rem2) :-
    exact_rem([a,b], [], []).

test(exact_rem3) :-
    exact_rem([a,b], [a,b], []).

test(exact_rem4) :-
    exact_rem([b,a], [a,b], []).

test(exact_rem5) :-
    exact_rem([b,a], [a,b,c], [c]).

:- end_tests(exact_rem).
