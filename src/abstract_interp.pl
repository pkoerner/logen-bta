:- module(abstract_interp, [l_lub_pat/2,
                            lub_pat/3,
                            glb_pat/3,
                            glb/3,
                            gen_memo_pat/3,
                            less_eq_pat/2,
                            check_pat/1,
                            top_env/1,
                            get_abstract_pattern/3,
                            update_abstract_environment/4]).

:- use_module(library(plunit)).
                        
:- use_module(exact_sets).

l_lub_pat([H|T],Res) :- llub2(T,H,Res).
l_lub_pat([],[]).

llub2([],A,A).
llub2([H|T],Acc,Res) :- lub_pat(H,Acc,NA), llub2(T,NA,Res).

lub_pat(bot,X,R) :- !, R=X.
lub_pat(X,bot,R) :- !, R=X.
lub_pat([],[],R) :- !, R=[].
lub_pat([X|T1],[Y|T2],R) :- !, R = [Z|T3], lub(X,Y,Z), lub_pat(T1,T2,T3).
lub_pat(X,Y,_) :- print_error('Could not compute LUB:',lub(X,Y)),
                  fail.

lub(s,X,X).
lub(d,_,d).
lub(nv,s,nv).
lub(nv,list,nv).
lub(nv,list_nv,nv).
lub(nv,nv,nv).
lub(nv,d,d).
lub(list,s,list).
lub(list,list_nv,list).
lub(list,list,list).
lub(list,nv,nv).
lub(list,d,d).
lub(list_nv,s,list_nv).
lub(list_nv,list_nv,list_nv).
lub(list_nv,list,list).
lub(list_nv,nv,nv).
lub(list_nv,d,d).


gen_memo_pat([],[],R) :- !, R=[].
gen_memo_pat([X|T1],[Y|T2],R) :- !, R = [Z|T3], gen_memo(X,Y,Z), gen_memo_pat(T1,T2,T3).
gen_memo_pat(X,Y,_) :-
 print_error('Could not compute MEMO LUB:',lub(X,Y)), fail.
                  
/* Discuss this with German: */
gen_memo(s,list_nv,d) :- !.
gen_memo(s,list,d) :- !.
gen_memo(X,Y,Z) :- lub(X,Y,Z).


glb_pat([],[],R) :- !, R=[].
glb_pat([X|T1],[Y|T2],R) :- !, R = [Z|T3], glb(X,Y,Z), glb_pat(T1,T2,T3).
glb_pat(X,Y,_) :- 
 print_error('Could not compute GLB for pattern:',glb_pat(X,Y)), fail.


glb(s,_,s).
glb(d,X,X).
glb(list_nv,s,s).
glb(list_nv,X,list_nv) :- less_eq(list_nv,X).
glb(list,X,X) :- less_eq(X,list).
glb(list,X,list) :- X=nv ; X=d.
glb(nv,X,X) :- less_eq(X,nv).
glb(nv,d,nv).


less_eq_pat([],[]) :- !.
less_eq_pat([X|T1],[Y|T2]) :- !, less_eq(X,Y), less_eq_pat(T1,T2).
less_eq_pat(X,Y) :- print('### Could not compute LEQ of '), print(X), print(' and '), print(Y),nl,
                  fail.

less_eq(s,_).
less_eq(list_nv,X) :- X \= s.
less_eq(list,X) :- X \= s, X\=list_nv.
less_eq(nv,X) :- X=nv ; X=d.
less_eq(d,d).

check_pat(X) :- var(X), !, print('### Variables as binding type'),nl,fail.
check_pat([]).
check_pat([H|T]) :- 
  ((nonvar(H),valid_binding_type(H)) -> true ;
     print_error('Illegal binding-type: ',H),fail),
  check_pat(T).

valid_binding_type(s).
valid_binding_type(d).
valid_binding_type(nv).
valid_binding_type(list).
valid_binding_type(list_nv).

% an abstract environment has the form:
% aenv(ListOf_StaticVars,ListOf_ListNVVars,ListOf_ListVars,ListOf_NonvarVars)

top_env(aenv([],[],[],[])). % i.e., every variable is dynamic

/* gets the abstract binding-type pattern of a concrete call, based on the
   abstract environment */
 
get_abstract_pattern(Call,Pattern,aenv(StaticVars,ListNVVars,ListVars,NonvarVars)) :- !,Call =.. [_Fun|Args],
    %print(get_arg_sd_vals(Args,Pattern,StaticVars,ListVars,NonvarVars)),nl,
    get_arg_sd_vals(Args,Pattern,StaticVars,ListNVVars,ListVars,NonvarVars).
   % print(get_arg_sd_vals_exit(Args,Pattern,StaticVars,ListVars,NonvarVars)),nl.
get_abstract_pattern(Call,Pattern,Env) :- print(illegal_call(get_abstract_pattern(Call,Pattern,Env))),nl,fail.

:- begin_tests(get_abstract_pattern).

test(get_abstract_parttern1) :-
    get_abstract_pattern(foo(A,_B), Pattern, aenv([A], [], [], [])), !,
    Pattern == [s, d].

test(get_abstract_parttern2) :-
    get_abstract_pattern(foo([1,2|A],B), Pattern, aenv([B], [A], [], [])), !,
    Pattern == [list_nv, s].

test(get_abstract_parttern3) :-
    get_abstract_pattern(foo(B,B), Pattern, aenv([B], [], [], [])), !,
    Pattern == [s, s].

test(get_abstract_parttern4) :-
    get_abstract_pattern(foo([A,B,C],_D), Pattern, aenv([A], [B,C], [], [])), !,
    Pattern == [list_nv, d].

test(get_abstract_parttern5, blocked('the first argument apparently is nv, but IMO it should be d. Am I wrong or is this test case not defined?')) :-
    get_abstract_pattern(foo([A,B,C|_E],_D), Pattern, aenv([A], [B,C], [], [])), !,
    Pattern == [d, d].

:- end_tests(get_abstract_pattern).

/* TO DO: the variables which are list_nv are not yet propagated */
get_arg_sd_vals([],[],_,_,_,_).
get_arg_sd_vals([H|T],[SD|TSD],SV,LnvV,LV,NV) :-
	term_variables(H,Vars),
	(exact_subset(Vars,SV) -> SD = s
	   ; ((list_skel_end(H,End),exact_subset_of_three(End,LV,LnvV,SV) /* list = list_skel or static */ )
           -> ((exact_subset_of_two(End,SV,LnvV), /* list end is static or list_nv */
                nv_list_els(H,NVLEls), exact_subset_of_four(NVLEls,SV,LnvV,LV,NV)) /* all list_els are nonvar or better */
                 -> SD=list_nv ; SD=list
              )
	       ;  ((nonvar(H) ; exact_subset([H],NV))
	            -> SD = nv ; SD = d)
	     )
	),
	get_arg_sd_vals(T,TSD,SV,LnvV,LV,NV).
		   
		
list_skel_end(X,[X]) :- var(X),!.
list_skel_end([],[]).
list_skel_end([_|T],End) :- list_skel_end(T,End).

:- begin_tests(list_skel_end).

test(list_skel_end1) :-
    list_skel_end(X, [X]).

test(list_skel_end2) :-
    list_skel_end([], []).

test(list_skel_end3) :-
    list_skel_end([a, b|X], [X]).

test(list_skel_end4) :-
    list_skel_end([a, b, c], []).

test(list_skel_end5) :-
    list_skel_end([_A, _B|X], [X]).

test(list_skel_end6) :-
    list_skel_end([_A, _B, _C], []).

:- end_tests(list_skel_end).

nv_list_els(X,R) :- var(X),!,R=[].
nv_list_els([],[]).
nv_list_els([H|T],Res) :-
     (nonvar(H) -> nv_list_els(T,Res)
                 ; Res=[H|R],nv_list_els(T,R)).

/* update_abstract_environment(BindingTypeSuccessPatternList,ConcreteCallPatternList, AbstractEnv, UpdatedAbstractEnv) */
/* predicate is called to update an abstract environment based on a success pattern inferred by the analysis */
update_abstract_environment(bot,_,_,_) :- fail. % bot makes all args static; probably better to fail ???
update_abstract_environment([],[],R,R).
update_abstract_environment([s|T],[S|TT],aenv(InSV,LnvV,LV,NV),Res) :-  !,
   term_variables(S,Vars), % all Vars must be static
   l_insert(Vars,InSV,In2SV), % add them to the list SV of static variables
   % TO DO ? remove Vars from LnvV, LV, NV ?
   update_abstract_environment(T,TT,aenv(In2SV,LnvV,LV,NV),Res).
update_abstract_environment([list_nv|T],[S|TT],aenv(SV,InvLV,LV,NV),Res) :- !,
   term_variables(S,Vars),
   exact_rem(SV,Vars,ListVars), % do not add the variables which are already static
   l_insert(ListVars,InvLV,Inv2LV),
   update_abstract_environment(T,TT,aenv(SV,Inv2LV,LV,NV),Res).
update_abstract_environment([list|T],[S|TT],aenv(SV,LnvV,InLV,NV),Res) :- !,
   term_variables(S,Vars),
   exact_rem(SV,Vars,V1),   % do not add variables which are already static
   exact_rem(LnvV,V1,ListVars), % do not add list(nonvar) variables
   l_insert(ListVars,InLV,In2LV),
   update_abstract_environment(T,TT,aenv(SV,LnvV,In2LV,NV),Res).
update_abstract_environment([nv|T],[S|TT],aenv(SV,LnvV,LV,InNV),Res) :- !,
  % term_variables(S,Vars),
    (var(S) -> (Vars=[S],
               exact_rem(SV,Vars,V1),
               exact_rem(LnvV,V1,V2),
               exact_rem(LV,V2,NVVars),
               l_insert(NVVars,InNV,In2NV))
            ; In2NV=InNV),
   update_abstract_environment(T,TT,aenv(SV,LnvV,LV,In2NV),Res).
update_abstract_environment([_|T],[_|TT],In,Out) :-
   update_abstract_environment(T,TT,In,Out).


:- begin_tests(update_abstract_environment).

test(abstract_env1) :-
    update_abstract_environment([s, d], [X, _Y], aenv([], [], [], []), Res), !,
    Res == aenv([X], [], [], []).

test(abstract_env2) :-
    update_abstract_environment([s, d], [X, X], aenv([], [], [], []), Res), !,
    Res == aenv([X], [], [], []).

test(abstract_env3) :-
    update_abstract_environment([s, s], [X, X], aenv([], [], [], []), Res), !,
    Res == aenv([X], [], [], []).

test(abstract_env4) :-
    update_abstract_environment([s, s], [X, Y], aenv([], [], [], []), Res), !,
    Res == aenv([X, Y], [], [], []).

test(abstract_env5) :-
    update_abstract_environment([s, nv], [X, Y], aenv([], [], [], []), Res), !,
    Res == aenv([X], [], [], [Y]).

test(abstract_env6) :-
    update_abstract_environment([s, list_nv], [X, Y], aenv([], [], [], []), Res), !,
    Res == aenv([X], [Y], [], []).

test(abstract_env7) :-
    update_abstract_environment([s, list_nv], [X, X], aenv([], [], [], []), Res), !,
    Res == aenv([X], [], [], []).

test(abstract_env8) :-
    update_abstract_environment([s, list_nv, list], [X, Y, Z], aenv([], [], [], []), Res), !,
    Res == aenv([X], [Y], [Z], []).

test(abstract_env9) :-
    update_abstract_environment([s, list_nv, list], [X, Y, Y], aenv([], [], [], []), Res), !,
    Res == aenv([X], [Y], [], []).

test(abstract_env10) :-
    update_abstract_environment([s, list_nv, list], [X, X, X], aenv([], [], [], []), Res), !,
    Res == aenv([X], [], [], []).

test(abstract_env11) :-
    update_abstract_environment([s, list_nv, list, nv], [X, Y, Z, U], aenv([], [], [], []), Res), !,
    Res == aenv([X], [Y], [Z], [U]).

test(abstract_env12) :-
    update_abstract_environment([s, list_nv, list, nv], [X, Y, Z, Y], aenv([], [], [], []), Res), !,
    Res == aenv([X], [Y], [Z], []).

test(abstract_env13, blocked('unclear semantics')) :-
    update_abstract_environment([nv, list, list_nv, s], [X, Y, Z, Y], aenv([], [], [], []), Res), !,
    Res == aenv([Y], [Z], [], [X]).

:- end_tests(update_abstract_environment).

