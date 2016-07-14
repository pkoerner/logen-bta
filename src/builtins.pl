:- module(builtins, [builtin_calls_answers/5,
                     side_effect_builtin/2,
                     is_built_in/2]).


/* pure: no side-effects and not propagation sensitive,
   sensitive: no side-effects but propagation sensitive,
   side-effect: side-effect, but not prop. sensitive,
   impure: both side-effects and propagation sensitive */
builtin_calls_answers(is,2,pure,[_,s],[s,s]).
builtin_calls_answers(=,2,pure,[X,Y],[GLB,GLB]) :- glb(X,Y,GLB).
builtin_calls_answers('=:=',2,pure,[s,s],[s,s]).
builtin_calls_answers(length,2,pure,[s,_],[s,s]).
builtin_calls_answers(length,2,pure,[list_nv,_],[list_nv,s]).
builtin_calls_answers(length,2,pure,[list,_],[list,s]).
builtin_calls_answers(length,2,pure,[nv,s],[list,s]).
builtin_calls_answers(length,2,pure,[d,s],[list,s]).
builtin_calls_answers(reverse,2,pure,[s,_],[s,s]).
builtin_calls_answers(reverse,2,pure,[list_nv,X],[R,R]) :- glb(X,list_nv,R).
builtin_calls_answers(reverse,2,pure,[list,X],[R,R]) :- glb(X,list,R).
builtin_calls_answers(append,3,pure,[s,s,_],[s,s,s]).
builtin_calls_answers(append,3,pure,[s,X,s],[s,s,s]) :- X\=s.
builtin_calls_answers(append,3,pure,[s,list_nv,X],[s,list_nv,list_nv]) :- X\=s.
builtin_calls_answers(append,3,pure,[s,list,list_nv],[s,list_nv,list_nv]).
builtin_calls_answers(append,3,pure,[s,d,X],[s,d,R]) :- X\=s, glb(X,nv,R).
builtin_calls_answers(append,3,pure,[list_nv,s,Y],[list_nv,s,R]) :- glb(Y,list_nv,R).
builtin_calls_answers(append,3,pure,[list_nv,list_nv,Y],[list_nv,list_nv,R]) :- glb(Y,list_nv,R).
builtin_calls_answers(append,3,pure,[list_nv,list,Y],[list_nv,list,R]) :- glb(Y,list,R).  /* a bit imprecise: improve */
builtin_calls_answers(append,3,pure,[list,_,s],[s,s,s]). 
builtin_calls_answers(append,3,pure,[list,X,list_nv],[s,R,list_nv]) :- glb(X,list_nv,R). 
builtin_calls_answers(append,3,pure,[list,X,Y],[list,X,RY]) :- Y\=s, Y\=list_nv, glb(Y,list,RY). /* a bit imprecise: improve */
builtin_calls_answers(member,2,pure,[s,s],[s,s]).
builtin_calls_answers(member,2,pure,[s,list],[s,list]).
builtin_calls_answers(member,2,pure,[d,s],[s,s]).
builtin_calls_answers(member,2,pure,[d,list_nv],[nv,list_nv]).
builtin_calls_answers(empty_assoc,1,pure,[_],[s]).
builtin_calls_answers(get_assoc,3,pure,[s,s,_],[s,s,s]).
builtin_calls_answers(put_assoc,4,pure,[s,s,s,_],[s,s,s,s]).
builtin_calls_answers(new_array,1,pure,[_],[s]).
builtin_calls_answers(aref,3,pure,[s,s,_],[s,s,s]).
builtin_calls_answers(aset,4,pure,[s,s,s,_],[s,s,s,s]).
builtin_calls_answers(empty_avl,1,pure,[_],[s]).

builtin_calls_answers(\=,2,sensitive,[s,s],[s,s]).
builtin_calls_answers(\==,2,sensitive,[s,s],[s,s]).
builtin_calls_answers(==,2,sensitive,[s,s],[s,s]).
builtin_calls_answers(functor,3,pure,[s,_,_],[s,s,s]).
builtin_calls_answers(functor,3,pure,[list,_,_],[list,s,s]).
builtin_calls_answers(functor,3,pure,[list_nv,_,_],[list_nv,s,s]).
builtin_calls_answers(functor,3,pure,[nv,_,_],[nv,s,s]).
builtin_calls_answers(functor,3,pure,[d,s,s],[nv,s,s]).
builtin_calls_answers(arg,3,pure,[s,s,_],[s,s,s]).
builtin_calls_answers(arg,3,pure,[s,list_nv,X],[s,list_nv,R]) :- glb(X,nv,R). 
builtin_calls_answers(arg,3,pure,[s,list,X],R) :- builtin_calls_answers(arg,3,pure,[s,nv,X],R).
builtin_calls_answers(arg,3,pure,[s,nv,s],[s,nv,s]).
builtin_calls_answers(arg,3,pure,[s,nv,list],[s,nv,list]).
builtin_calls_answers(arg,3,pure,[s,nv,nv],[s,nv,nv]).
builtin_calls_answers(arg,3,pure,[s,nv,d],[s,nv,nv]).
builtin_calls_answers('=..',2,pure,[s,_],[s,s]).
builtin_calls_answers('=..',2,pure,[X,s],[s,s]) :- X\=s.
builtin_calls_answers('=..',2,pure,[list_nv,X],[list_nv,list_nv]) :- X \= s.
builtin_calls_answers('=..',2,pure,[list,X],[list,R]) :- X \= s, glb(X,list,R).
builtin_calls_answers('=..',2,pure,[nv,X],[s,list]) :- X\=s.
builtin_calls_answers('=..',2,pure,[d,list_nv],[nv,list_nv]).
builtin_calls_answers('=..',2,pure,[d,list],[nv,list]).
builtin_calls_answers(number,1,sensitive,[s],[s]).
builtin_calls_answers(ground,1,sensitive,[s],[s]).
builtin_calls_answers(nonvar,1,sensitive,[X],[X]) :- (X=s ; X=list_nv ; X=list ; X=nv).
builtin_calls_answers(atom_concat,3,pure,[s,s,_],[s,s,s]).
builtin_calls_answers('<',2,pure,[s,s],[s,s]).
builtin_calls_answers('=<',2,pure,[s,s],[s,s]).
builtin_calls_answers('>',2,pure,[s,s],[s,s]).
builtin_calls_answers('>=',2,pure,[s,s],[s,s]).


  /* those built-ins that are never ever called by the PE */
side_effect_builtin(!,0).
side_effect_builtin(call,_).
side_effect_builtin(print,1).
side_effect_builtin(write,1).
side_effect_builtin(format,2).
side_effect_builtin(format,3).
side_effect_builtin(nl,0).
side_effect_builtin(throw,1).
side_effect_builtin(garbage_collect,0).
side_effect_builtin(statistics,2).

%sd_list([],0).
%sd_list([H|T],X) :- X>0, X1 is X-1, (H=s ; H=d), sd_list(T,X1).

is_built_in(call,N) :- N>0,!.
is_built_in('<',2) :- !.
is_built_in('=<',2) :- !.
is_built_in('>',2) :- !.
is_built_in('>=',2) :- !.
is_built_in('=..',2) :- !.
is_built_in('!',0) :- !.
is_built_in(fail,0) :- !.
is_built_in(true,0) :- !.
is_built_in(F,A) :- side_effect_builtin(F,A),!.
is_built_in(Fun,Arity) :- functor(C,Fun,Arity),
   (prolog_reader:is_user_pred(C) -> 
     (builtin_calls_answers(Fun,Arity,_,_,_) -> nl,print(redefined_builtin(Fun,Arity)),nl,fail
        ; fail )
     ; builtin_calls_answers(Fun,Arity,_,_,_) -> true
     ; otherwise -> nl, print(undefined_predicate_treating_like_built_in(Fun,Arity)),nl
     ).
   %calls_answers(Fun,Arity,built_in,_,_).
