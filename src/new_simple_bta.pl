/* A Binding-Time for Logen */
/* developed by Michael Leuschel and German Vidal */
/* (c) Michael Leuschel and German Vidal 2007-2015 */

:- module(new_simple_bta,[analyze_single_file/2,
                          bta_cli_entry/1, verbose/0, assert_verbose/0,
                          cli_option/1, vprintln/1
                         ]).

:- use_module(library(lists)).
 
:- use_module(library(sets)).
%:- use_module(size_change_analysis_simplerfixpoint).

%:- use_module(size_change_analysis_without_labels_with_sccs).
%:- use_module(sca_wo_labels_with_sccs_simpler).
:- use_module(sca_wo_labels_with_sccs_even_simpler).

%%:- use_module(size_change_analysis_with_SCC).
%%:- use_module(size_change_analysis).
%%:- use_module(size_change_analysis_without_labels).
%%:- use_module('obsolete/new_size_change_analysis').
:- use_module(library(plunit)).

:- dynamic verbose/0. 
assert_verbose :- verbose -> true ; assert(verbose).
vprintln(X) :- (verbose -> (print(X),nl) ; true).
vvprintln(X) :- (cli_option(very_verbose) -> (print(X),nl) ; true).
println(X) :- print(X),nl.

:- dynamic nr_errors_occured/1.
nr_errors_occured(0).
reset_errors :- retractall(nr_errors_occured(_)), assert(nr_errors_occured(0)).
inc_errors :- retract(nr_errors_occured(X)), X1 is X+1,
  assert(nr_errors_occured(X1)).
print_error(Msg,Term) :- nl, print('### '), print(Msg), print(' '), print(Term),nl,
  inc_errors.
print_nr_errors :- nr_errors_occured(X),
  (X=0 -> true ; nl,print('### '), print(X), print(' ERROR(S) occured !'),nl).


print_bt_message(Msg) :- vvprintln(Msg).
print_bt_message(Msg) :- vvprintln(backtrack(Msg)),fail.

:- dynamic output_ann/1.
aprint(X) :- (output_ann(S)
              -> (write_term(S,X,[])) ; print(X)).
%             -> (write_term(S,X,[quoted(true),ignore_ops(true)])) ; true).
aqprint(X) :- (output_ann(S)
%              -> (write_term(S,X,[quoted(true)])) ; print(X)).
             -> (write_term(S,X,[quoted(true),ignore_ops(true),numbervars(true)])) ; true).
anl :- (output_ann(S) -> nl(S) ; nl).

:- dynamic cli_option/1.


check_inputs :- nl,vprintln('Checking User Inputs in File'),
                prolog_reader:get_clause('$MEMOANN'(Pred,Arity,Pat),Body,_Ref),
                vprintln(('$MEMOANN'(Pred,Arity,Pat):-Body)),
                check_pat(Pat),
                (length(Pat,Arity) -> true
                  ; print_error('Arity of $MEMOANN incorrect:',Arity)),
                Call =.. [Pred|Pat],
                (is_user_pred(Call) -> true
                 ; print_error('$MEMOANN refers to predicate that does not exist:',Call)
                ),
                fail.
check_inputs :- nl,
                prolog_reader:get_clause('$MEMOCALLS'(Call),Cond,_Ref),
                vprintln(('$MEMOCALLS'(Call):-Cond)),
                (is_user_pred(Call) -> true
                 ; print_error('$MEMOCALLS refers to predicate that does not exist:',Call)
                ),fail.
%check_inputs :- prolog_reader:get_clause(H,B,_), portray_clause((H:-B)),fail.
check_inputs.

/* --------------------------------- */
/* The dynamic calls_answers table  */
/* --------------------------------- */

:- dynamic change/0.

pp :- (change -> print(change),nl ; true),
    print('BTA Call/Answer Patterns'),
    (cli_option(summarise_calls_answers) -> print(' (summary)') ; true),nl,
    prolog_reader:is_user_pred(Call),
    functor(Call,A,B),
    (cli_option(summarise_calls_answers)
      -> calls_answers_summary(A,B,user,P,Ans) ; calls_answers(A,B,user,P,Ans)),
    print(A/B), print(' '), print(P),
	print(' -> '), print(Ans),
	nl,
    fail.
pp :- verbose,print('Memo: '),logen_memo(PP), print(PP), print(' '),fail.
pp :- verbose,nl,print('Rescall: '),logen_rescall(PP), print(PP), print(' '),fail.
pp :- nl.


calls_answers_summary(A,B,Module,EntrySummary,SuccessSummary) :-
   findall(Entry,calls_answers(A,B,Module,Entry,_),EL),
   findall(Success,calls_answers(A,B,Module,_,Success),SL),
   l_lub_pat(EL,EntrySummary),
   l_lub_pat(SL,SuccessSummary).

l_lub_pat([H|T],Res) :- llub2(T,H,Res).
l_lub_pat([],[]).

llub2([],A,A).
llub2([H|T],Acc,Res) :- lub_pat(H,Acc,NA), llub2(T,NA,Res).

%calls(app,3,[s,s,s]).
%answers(app,3,[s,s,s]).

:- dynamic calls_answers/5.

%calls_answers(dapp,4,user,[s,s,s,d],[s,s,s,s]).
%calls_answers(test,3,user,[s,d,d],[s,s,s]).
%calls_answers(test,1,user,[d],[s]).
%calls_answers(test_memo,2,user,[d,s],[s,s]).

:- dynamic bta_cli_entry/1.
:- dynamic memo_entry/3.



init_calls_answers :-
  retractall(memo_entry(_,_,_)),
  prolog_reader:get_clause(bta_entry(Pred,Arity,Pat),true,_),
  add_entry_point(Pred,Arity,Pat),
  fail.
init_calls_answers :-
  bta_cli_entry(CLIGOALTerm), print(bta_cli_entry(CLIGOALTerm)),nl,
  nonvar(CLIGOALTerm),
  functor(CLIGOALTerm,Pred,Arity),
  CLIGOALTerm =.. [Pred|Pat],
  add_entry_point(Pred,Arity,Pat),
  fail.
init_calls_answers.


add_entry_point(Pred,Arity,Pat) :-
   check_pat(Pat),
   generalise_memo_pattern(Pred,Arity,Pat,GPat),
   print(memo_entry(Pred,Arity,GPat)),nl,
   assert_new_calls_answers(Pred,Arity,user,GPat,memo_entry(Pred,Arity,GPat)),
   assertz(memo_entry(Pred,Arity,GPat)).
 


my_global_binding_times(Pred,Arity,ActualPat,Pattern) :-  
    compute_global_binding_times_without_labels(Pred,Arity,ActualPat,GTPattern),
    ((prolog_reader:get_clause('$MEMOANN'(Pred,Arity,UserPattern),true,_Ref),
      \+ cli_option(ignorehints))
      -> %print(user(UserPattern)),nl,
         glb_pat(GTPattern,UserPattern,Pattern) % Note : GLB not LUB !!
          
      ;  Pattern = GTPattern
    ).

% generalise_memo_pattern/4: original version
generalise_memo_pattern(Pred,Arity,ActualPat,GeneralisedPat) :-
   ((my_global_binding_times(Pred,Arity,ActualPat,GTPattern),\+ cli_option(no_global_termination) )
    ->  /* predicate is potentially globally not terminating */
        /* we need to abstract the entries marked by d in GTPattern */
        /* CHECK with German:: is it correct to keep list and nv positions as they are if the GTPattern says s? */
        gen_memo_pat(GTPattern,ActualPat,GeneralisedPat),
        vprintln(lub_memo_pattern(Pred,Arity,GTPattern,ActualPat,GeneralisedPat))
     ;  GeneralisedPat = ActualPat
   ).

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


/*  prolog_reader:is_user_pred */

/* --------------------------------- */
/*    The program to be analyzed     */
/* --------------------------------- */
:- use_module(prolog_reader).
:- use_module(dot_view).

analyze_single_file(File,Options) :-
    reset_errors,
    vprintln(load_file(File)),
    flush_output(user),
    prolog_reader:load_file(File),
    vprintln(finished_loading_file(File)),
    flush_output(user),
    
    (cli_option(dependency_graph(DF))
      -> print_dep_graph_for_dot(DF) ; true),
    
    check_inputs,
    init_calls_answers,
    statistics(runtime,[T1,_]),
    my_size_change_analysis,
    /* BTA */
    flush_output(user),
    statistics(runtime,[T2,_]),
    nl,print('Starting BTA (Binding-Time Analysis)'),nl,
    bta_analyze,
    statistics(runtime,[T3,_]),
    TA is T2-T1,
    print('% Size Change Graph Analysis time: '), print(TA), print(' ms'),nl,
    TB is T3-T2,
    print('% BTA Analysis time: '), print(TB), print(' ms'),nl,
    flush_output(user),
    nl,print('% Writing LOGEN annotation file to '),
    (member(output(F),Options) -> open(F,write,Stream) ; (F=Stream,Stream = user_output)),
    print(F),nl,
    assert(output_ann(Stream)),
    print_imports,
    print_logen_filters,
    annotate,
    (member(output(F),Options) -> close(Stream) ; true),
    retractall(output_ann(_)),!,
    print_nr_errors.
analyze_single_file(File,_Options) :-
    print_error('Analyzing file failed: ',File),
    print_nr_errors.
    
my_size_change_analysis :- 
    (\+ cli_option(no_global_termination); \+ cli_option(no_local_termination)), !,
    size_change_analysis_without_labels.
my_size_change_analysis :- print('**************** SKIPPING SIZE-CHANGE ANALYSIS ****************'),nl.

/* --------------------------------- */

needs_module(M) :- cli_option(used_module(M)).
needs_module(M) :- 
  prolog_reader:get_clause('$USE_MODULE'(M),true,_Ref).

print_imports :- anl,
   needs_module(M),
   aprint(' :- use_module('), aqprint(M), aprint(').'),anl,
   fail.
print_imports.
   
print_logen_filters :- anl,
   memo_entry(Fun,Arity,Pat),
   vprintln(memo_entry(Fun,Arity,Pat)),
   aprint(' :- filter '),
   convert_pat(Pat,FiltPat),
   Filter =.. [Fun|FiltPat],
   aqprint(Filter), aprint('.'),anl,
   fail.
print_logen_filters.

% convert a bta pattern into one that can be used by logen:
convert_pat(X,_) :- var(X),!, print('*** INTERNAL ERROR: variable as pattern !'),nl,fail.
convert_pat([],[]).
convert_pat([s|T],[static|FT]) :- convert_pat(T,FT).
convert_pat([d|T],[R|FT]) :- (cli_option(allow_online_memo) -> R=online ; R=(dynamic)),convert_pat(T,FT).
convert_pat([nv|T],[nonvar|FT]) :- convert_pat(T,FT).
convert_pat([list|T],[(static ; type(list(dynamic)))|FT]) :- convert_pat(T,FT). %% replace  by list(dynamic) ??
convert_pat([list_nv|T],[(static ; type(list(nonvar)))|FT]) :- convert_pat(T,FT).

/* --------------------------------- */

debug_this_call(X) :- nonvar(X), X = eval(Y,_,_), nonvar(Y), Y=apply(_,_).


/* The main loop of the analysis */
bta_analyze :- (verbose -> pp ; true),
   retractall(change),
   reset_before_loop,
   print_bt_message(bta_analyze),
   prolog_reader:get_clause(Call,Body,Ref),
   % <--- TO DO: extract annotations '$MEMO'()
   %trace,
   functor(Call,Fun,Arity),
   calls_answers(Fun,Arity,user,Pattern,AnsPat),
  %nl,nl,portray_clause((Call :- Body)),nl,
   Call =.. [Fun|Args],
   top_env(EmptyEnv),
   update_abstract_environment(Pattern,Args,EmptyEnv,InEnv),
 %  (debug_this_call(Call) -> println(update_abstract_environment(Pattern,Args,EmptyEnv,InEnv)) ; true),
   vvprintln(call_pattern(Call,InEnv)),
  % (debug_this_call(Call) -> println(call_pattern(Call,Pattern,InEnv,AnsPat)) ; true),
   print_bt_message(check_body(Body)),
   (Body=true -> OutSV=InEnv
              ; check_body(Body,InEnv,OutSV,Ref)
   ),
   vvprintln(exit_pattern(Call,static_vars(OutSV))),
 %  (debug_this_call(Call) -> println(exit_pattern(Call,InEnv)) ; true),
   /* check that answer is ok */
   get_abstract_pattern(Call,NewAnsPattern,OutSV),
   lub_pat(AnsPat,NewAnsPattern,Lub),
   vvprintln(ans_lub(AnsPat,NewAnsPattern,Lub)),
%   (debug_this_call(Call) -> println(ans_lub(AnsPat,NewAnsPattern,Lub)) ; true),
   (Lub=AnsPat
    -> true ; (assert_change, vvprintln('CHANGE in Answer Pattern'),
	       retract(calls_answers(Fun,Arity,user,Pattern,AnsPat)), 
	       assert(calls_answers(Fun,Arity,user,Pattern,Lub)))),
   fail.
bta_analyze :- (change -> bta_analyze ; 
    print('BTA Analysis finished'),nl,vprintln('-----------'),pp).

:- use_module(library(varnumbers)).
annotate :- 
   prolog_reader:get_clause(Call,Body,Ref),
   functor(Call,Fun,Arity),
   (calls_answers(Fun,Arity,user,_Pattern,_AnsPat)->true;fail),
  %nl,nl,portray_clause((Call :- Body)),nl,
   Call =.. [Fun|_Args],
   numbervars(c(Call,Body)),
   aq_print_logen(Fun,Call),
   (Body=true -> true
   ; ( aprint(' :- '), anl, aprint('   '),
       ann_body(Body,Ref) )
   ),
   aprint('.'),anl,
   fail.
annotate :- vprintln('Annotation generated'),vprintln('-----------').

assert_change :- change -> true ; assert(change).

ann_body(true,_Path) :- !,aprint(logen(call,true)).
ann_body(Module:(A,B),Path) :- !,  ann_body((Module:A,Module:B),Path). % these annotations appear sometimes inside findall
%ann_body(call(A),Path) :- nonvar(A),A=prolog_reader:C,!, ann_body(call(C),Path).
ann_body((A,B),Path) :- !,
	ann_body(A,and1(Path)),
	aprint(', '),
	ann_body(B,and2(Path)).
ann_body(resdisj(A,B),Path) :- !, 
    /* this corresponds to a residual_disj ? */
        aprint('resdisj('),
	ann_body(A,resdisj1(Path)), aprint(', '),
	ann_body(B,resdisj2(Path)), aprint(') ').
ann_body((A->B),Path) :- !, 
    /* this corresponds to a static_local_cut ; */
	aprint('( '),
	ann_body(A,lcut1(Path)), aprint(' -> '),
	ann_body(B,lcut2(Path)), aprint(') ').
ann_body((A;B),Path) :- !, 
    /* this corresponds to a static_or ; */
	aprint('( '),
	ann_body(A,disj1(Path)), aprint('; '),
	ann_body(B,disj2(Path)), aprint(') ').
/* to do: add more cases:  if-then-else, ... */
ann_body('\\+'(X),Path) :- !,
    aprint('resnot( ('),
    ann_body(X,not(Path)),
    aprint(') )').
ann_body(findall(T,PX,L),Path) :- !, peel_prolog_reader(PX,X), %nl,print(findall(T,X,L)),nl,nl,
    aprint('resfindall('),
    aqprint(T), aprint(', '),
    ann_body(X,Path), aprint(', '),
    aqprint(L), 
    aprint(')').
ann_body(T,Path) :- transparent(T,InnerT,_INST),!,
         /* to do: print annotations */
         ann_body(InnerT,Path).
ann_body('$MEMO'(Call),Path) :- !, ann_body(Call,Path).
ann_body('$UNFOLD'(Call),Path) :- !, ann_body(Call,Path).
ann_body(Call_,Path) :-
     Call_ = Call,
	(logen_memo(Path)
	 -> ((cli_option(allow_semi_unfold), logen_unfold(Path))
	      -> aq_print_logen(online,Call)  /* TO DO: change into conditional unfold */
	      ;  aq_print_logen(memo,Call))
	 ;   (logen_unfold(Path)
	       -> aq_print_logen(unfold,Call)
	       ;  (logen_rescall(Path)
	            -> ((cli_option(allow_semi_call)
	                 %%, logen_call(Path)  % comment in to generate semicall only if at least one path does a call
	                 )
	                -> aq_print_logen(semicall,Call)
	                ;  aq_print_logen(rescall,Call)
	                )
	            ;  (logen_call(Path) -> aq_print_logen(call,Call)
	                 ;  print('/* INTERNAL ERROR: built-in neither call nor rescall: '),
	                    print(Call), print(' : '), print(Path), print(' ; assuming rescall */'),nl,
	                    (verbose -> pp_table ; true),
	                    aq_print_logen(rescall,Call)
	               )
	          )
	     )
	).

aq_print_logen(Ann,Call) :- strip(Call,SC), aqprint(logen(Ann,SC)).

strip(X,R) :- var(X),!,R=X.
strip(prolog_reader:X,R) :- !,R=X.
strip(call(X),call(R)) :- !, strip(X,R).
strip(ensure_loaded(X),ensure_loaded(R)) :- !, strip(X,R).
strip(R,R).

/* check_body(BodyOfClause,ListofStaticVars,ListofStaticVarsAfterExecutingBody) */
check_body(true,In,In,_Path) :- !.
check_body(Module:(A,B),StaticVars,OutSV2,Path) :- !,  check_body((Module:A,Module:B),StaticVars,OutSV2,Path).
check_body((A,B),StaticVars,OutSV2,Path) :- !, 
  %  print_bt_message(conj1(A)),
	check_body(A,StaticVars,OutSV1,and1(Path)),
  %  print_bt_message(conj2(B)),
	check_body(B,OutSV1,OutSV2,and2(Path)).
check_body(resdisj(A,B),StaticVars,OutSV,Path) :- !, 
    /* this corresponds to a residual_disj ? */
	check_body(A,StaticVars,OutSV1,resdisj1(Path)),
	check_body(B,StaticVars,OutSV2,resdisj2(Path)),
	exact_inter(OutSV1,OutSV2,OutSV).
check_body((A->B),StaticVars,OutSV,Path) :- !, 
    check_body(A,StaticVars,OutSV1,lcut1(Path)), % TO DO ?: check that we can fully eval A
    check_body(B,OutSV1,OutSV,lcut2(Path)).
check_body((A;B),StaticVars,OutSV,Path) :- !, 
    /* this corresponds to a static_or ; */
  ( %print_bt_message(disj_left),
	  check_body(A,StaticVars,OutSV,disj1(Path))
	 %,print_bt_message(disj_left_res(OutSV)) 
	 ;  %vvprintln(disj_right),
	  check_body(B,StaticVars,OutSV,disj2(Path))
  ).
check_body('\\+'(X),InSV,OutSV,Path) :- !,
    check_body(X,InSV,_,not(Path)),
    OutSV=InSV. /* negation does no instantiation */
/* to do: add more cases:  if-then-else, ... */
check_body(T,InSV,OutSV,Path) :- transparent(T,InnerT,INST),!,
         check_body(InnerT,InSV,II,Path),
	 (INST=instantiate -> OutSV = II ; OutSV = InSV).
check_body('$MEMO'(Call),InSV,OutSV,Path) :- 
	 cli_option(ignorehints),!,check_body(Call,InSV,OutSV,Path).
check_body('$UNFOLD'(Call),InSV,OutSV,Path) :- 
	 cli_option(ignorehints),!,check_body(Call,InSV,OutSV,Path).
check_body('$MEMO'(Call_),InSV,OutSV,Path) :- !,  /* USER PROVIDED ANNOTATION */
   Call_ = Call,
	functor(Call,Fun,Arity),
    get_abstract_pattern(Call,CallPattern,InSV),
    memo_program_point(Path,Fun,Arity,CallPattern),
	OutSV=InSV.
check_body('$UNFOLD'(Call_),InSV,OutSV,Path) :- !,  /* USER PROVIDED ANNOTATION */
   Call_ = Call,
	functor(Call,Fun,Arity),
    get_abstract_pattern(Call,CallPattern,InSV),
    check_unfold_call(Call,CallPattern,Fun,Arity,InSV,OutSV,Path).
check_body(Call_,InSV,OutSV,Path) :-
   Call_ = Call,
    functor(Call,Fun,Arity),
    get_abstract_pattern(Call,CallPattern,InSV),
    %println(is_not_terminating(Fun,Arity,CallPattern)),
	(memoise_this_call(Path,Fun,Arity,CallPattern,Call)
	 ->  memo_program_point(Path,Fun,Arity,CallPattern),
         OutSV=InSV
	 ;   check_unfold_call(Call,CallPattern,Fun,Arity,InSV,OutSV,Path)
	).



:- begin_tests(check_body).

test(check_body1) :-
    check_body(true, X, Y, _), !, X == Y.

test(check_body2) :-
    check_body((true, true), X, Y, _), !, X == Y.


:- end_tests(check_body).

% check whether a call should be memoised or not
%memoise_this_call/5: original version
memoise_this_call(_Path,_Fun,_Arity,_CallPattern,Call) :- %println(memo_check(Call)),
   \+ cli_option(ignorehints),
   prolog_reader:get_clause('$UNFOLDCALLS'(Call),Cond,_Ref),
   call(Cond),!,fail.
memoise_this_call(_Path,_Fun,_Arity,_CallPattern,Call) :- %println(memo_check(Call)),
   \+ cli_option(ignorehints),
   prolog_reader:get_clause('$MEMOCALLS'(Call),Cond,_Ref),call(Cond).
memoise_this_call(Path,_,_,_,_) :- contains_dangerous_construct(Path).
memoise_this_call(_,Fun,Arity,_,_) :- side_effect_builtin(Fun,Arity).
memoise_this_call(Path,_Fun,_Arity,_CallPattern,_Call) :-  \+ cli_option(no_local_termination), 
   \+ cli_option(allow_semi_unfold) , logen_memo(Path).  % we should memo: some other path requests it to be memoed (and we don't allow semi_unfold)
memoise_this_call(_Path,Fun,Arity,CallPattern,_Call) :-  \+ cli_option(no_local_termination), 
   call_is_not_terminating(Fun,Arity,CallPattern). % we should memo if the call is potentially not terminating

contains_dangerous_construct(not(_)) :- !.
contains_dangerous_construct(X) :- nonvar(X),X=..[_,A], contains_dangerous_construct(A).

%memo_program_point/4 and memo_program_point2/4: original versions
memo_program_point(Path,Fun,Arity,CallPattern) :-
   cli_option(monovariant_bta), retract(memo_entry(Fun,Arity,PrevCallPattern)),!,
   lub_pat(CallPattern,PrevCallPattern,NewCallPattern),
   memo_program_point2(Path,Fun,Arity,NewCallPattern).
memo_program_point(Path,Fun,Arity,CallPattern) :- memo_program_point2(Path,Fun,Arity,CallPattern).

memo_program_point2(Path,Fun,Arity,_CallPattern) :-
   is_built_in(Fun,Arity),!,
   assert_rescall(Path).
memo_program_point2(Path,Fun,Arity,CallPattern) :-
   generalise_memo_pattern(Fun,Arity,CallPattern,MemoPattern),
   assert_memo(Path,Fun,Arity,MemoPattern),
   vvprintln(memo(Path,MemoPattern)),
   check_memo_call_pattern(Fun,Arity,MemoPattern,_AnswPat,Path).


% keep track which program points are annotated how:
:- dynamic logen_memo/1, logen_unfold/1, logen_call/1, logen_rescall/1.
reset_all :- reset_before_loop, retractall(logen_memo(_)), retractall(logen_rescall(_)).
reset_before_loop :- retractall(logen_unfold(_)), retractall(logen_rescall(_)).
assert_memo(PP,Fun,Arity,CallPattern) :- 
	(logen_memo(PP) -> true ; (assert(logen_memo(PP)), vvprintln(memo(PP,Fun,Arity,CallPattern)))),
	vvprintln(memo_entry(Fun,Arity,CallPattern)),
	(memo_entry(Fun,Arity,CallPattern) -> true ;
	    assertz(memo_entry(Fun,Arity,CallPattern))).
assert_unfold(PP) :- logen_unfold(PP) -> true ; assert(logen_unfold(PP)).
assert_call(PP) :- logen_call(PP) -> true ; assert(logen_call(PP)).
assert_rescall(PP) :- logen_rescall(PP) -> true ; assert(logen_rescall(PP)).

pp_table :- print('logen_unfold: '),nl, logen_unfold(X), print('  '),print(X),nl,fail.
pp_table :- print('logen_memo: '),nl, logen_memo(X), print('  '),print(X),nl,fail.
pp_table :- print('logen_call: '),nl, logen_call(X), print('  '),print(X),nl,fail.
pp_table :- print('logen_rescall: '),nl, logen_rescall(X), print('  '),print(X),nl,fail.
pp_table.

%spy_unfold(remove_channels,4).
%check_unfold_call(Call,CallPattern,Fun,Arity,_InSV,_OutSV,_Path) :- spy_unfold(Fun,Arity),
%    print(unfolding(Fun,Arity,CallPattern,CallArity)),nl, print_path_clause(Path),fail.
check_unfold_call(Call,CallPattern,Fun,Arity,InSV,OutSV,Path) :-
	check_call_pattern_for_unfold(Fun,Arity,CallPattern,AnswPat,Path,Call),
	Call =.. [Fun|Args],
	update_abstract_environment(AnswPat,Args,InSV,OutSV),
	vvprintln(unfold_call_out_aenv(Call,AnswPat,Args,InSV,OutSV,Path)).
check_memo_call_pattern(Fun,Arity,CallPattern,AnswPat,Path) :-
	(calls_answers(Fun,Arity,_Module,CallPattern,AnswPat)  
	 -> true /* we already have an entry for this call pattern */
         ;  vvprintln(no_calls_answers_for_memo(Fun,Arity)), assert_change,
	        assert_new_calls_answers(Fun,Arity,user,CallPattern,memo(Path))
	).


check_call_pattern_for_unfold(Fun,Arity,CallPattern,AnswPat,Path,_Call) :-
	(calls_answers(Fun,Arity,_Module,CallPattern,AnswPat)  
	 -> assert_unfold(Path) /* we already have an entry for this call pattern */
	 ;  (is_built_in(Fun,Arity)
	      -> (builtin_calls_answers(Fun,Arity,_Pure,CallPattern,AnswPat)
		      /* this assumes semi_call annotations where required; otherwise
		      * we also need to add a check \+ logen_rescall(Path) here */
	           ->  vvprintln(call_builtin(Fun,CallPattern,Path)),
	               assert_call(Path)
	           ;   vvprintln(illegal_call_to_builtin(Fun,Arity,CallPattern,Path)),
		           /* to do: make rescall or use semi-call at spectime */
	      	       assert_rescall(Path),
	      	       AnswPat = CallPattern
		     ) 
	      ;  vvprintln(no_calls_answers_for_unfold(Fun,Arity)), assert_change,
	         assert_new_calls_answers(Fun,Arity,user,CallPattern,unfold(Path)),
	         fail /* as we initially assume that the Answer patter is bot and the atom is unfolded */
	    )
	).

assert_new_calls_answers(Fun,Arity,Module,CallPattern,Path) :-
   %set_static(CallPattern,AnswPat), /* set output pattern to static; we start by assuming predicate makes everything static on exit (we could also store a bottom value instead; this would detect e.g. that p :- p. has no success pattern */
   AnswPat = bot,
   ((\+ cli_option(ignorehints),
     prolog_reader:get_clause('$MEMOANN'(Fun,Arity,UserPat),true,_))
     -> (less_eq_pat(CallPattern,UserPat) -> true
          ;  print_error('UNEXPECTED Call Pattern: ',Fun/Arity),
             print('### PATTERN: '), print(CallPattern),nl,
             print('### EXPECTED at least $MEMOANN: '), print(UserPat),nl,
             print('### Path: '), print_path_clause(Path)
         )
     ; true
   ),
   (is_built_in(Fun,Arity)
      -> print_error('Storing calls/answers for built-in or unknown predicate: ',Fun/Arity),
         print('### '),print(calls_answers(Fun,Arity,Module,CallPattern,Path)),nl
      ;  true),
   assert(calls_answers(Fun,Arity,Module,CallPattern,AnswPat)).

print_path_clause(Path) :- print_path(Path),nl,
             get_path_clause(Path,Head,Body),
             print('### Clause: '),portray_clause(( Head:-Body )),nl.

print_path('$ref'(X,Y)) :- prolog_reader:get_clause(Head,_Body,'$ref'(X,Y)),!,
   functor(Head,F,N), print(F),print('/'), print(N).
print_path(X) :- X=..[F,A],!, print_path(A), print(' -> '),print(F).
print_path(X) :- print(X).
  
% get the clause that is embedded in a path:
%get_path_clause(P,H,B) :- print(get_path_clause(P,H,B)),nl,trace,fail.
get_path_clause('$ref'(X,Y),Head,Body) :- !, %functor(Head,Fun,Arity),
     (prolog_reader:get_clause(Head,Body,'$ref'(X,Y))
      -> true ; print(cannot_get_clause(Head)),nl).
get_path_clause('not'(X),H,B) :-  !, get_path_clause(X,H,B).
get_path_clause('and1'(X),H,B) :-  !, get_path_clause(X,H,B).
get_path_clause('and2'(X),H,B) :-  !, get_path_clause(X,H,B).
get_path_clause('disj1'(X),H,B) :-  !, get_path_clause(X,H,B).
get_path_clause('disj2'(X),H,B) :-  !, get_path_clause(X,H,B).
get_path_clause('lcut1'(X),H,B) :-  !, get_path_clause(X,H,B).
get_path_clause('lcut2'(X),H,B) :-  !, get_path_clause(X,H,B).
get_path_clause('resdisj1'(X),H,B) :-  !, get_path_clause(X,H,B).
get_path_clause('resdisj2'(X),H,B) :-  !, get_path_clause(X,H,B).
get_path_clause('memo'(X),H,B) :-  !, get_path_clause(X,H,B).
get_path_clause('unfold'(X),H,B) :-  !, get_path_clause(X,H,B).
get_path_clause(X,H,B) :- X =..[_,Y], !, get_path_clause(Y,H,B).

transparent(when(_,X),X,instantiate).
transparent(findall(_,PX,_),X,no) :- peel_prolog_reader(PX,X).
transparent(\+(X),X,no).
%transparent('->'(X,Y),(X,Y),instantiate).
transparent(pp_cll(X),X,instantiate).  % PROB/ecce/... self-check meta-predicates
transparent(pp_mnf(X),X,instantiate).
transparent(pp_cll(X),X,instantiate).
transparent(mnf(X),X,instantiate).
transparent(iso_body(X),X,instantiate).

% peel off prolog_reader module declaration
peel_prolog_reader(PX,R) :- nonvar(PX),prolog_reader:X=PX,!,R=X.
peel_prolog_reader(X,X).

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


top_env(aenv([],[],[],[])).

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

:- use_module(library(terms)).





/* update_abstract_environment(BindingTypeSuccessPatternList,ConcreteCallPatternList, AbstractEnv, UpdatedAbstractEnv) */
/* predicate is called to update an abstract environment based on a success pattern inferred by the analysis */
update_abstract_environment(bot,_,_,_) :- fail. % bot makes all args static; probably better to fail ???
update_abstract_environment([],[],R,R).
update_abstract_environment([s|T],[S|TT],aenv(InSV,LnvV,LV,NV),Res) :-  !,
   term_variables(S,Vars),
   l_insert(Vars,InSV,In2SV),
   update_abstract_environment(T,TT,aenv(In2SV,LnvV,LV,NV),Res).
update_abstract_environment([list_nv|T],[S|TT],aenv(SV,InvLV,LV,NV),Res) :- !,
   term_variables(S,Vars),
   exact_rem(SV,Vars,ListVars),
   l_insert(ListVars,InvLV,Inv2LV),
   update_abstract_environment(T,TT,aenv(SV,Inv2LV,LV,NV),Res).
update_abstract_environment([list|T],[S|TT],aenv(SV,LnvV,InLV,NV),Res) :- !,
   term_variables(S,Vars),
   exact_rem(SV,Vars,V1),
   exact_rem(LnvV,V1,ListVars),
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







/* take a pattern and set all arguments as static */
set_static([],[]).
set_static([_|T],[s|ST]) :- set_static(T,ST).

l_insert([],R,R).
l_insert([V|T],In,Out) :- insert(In,V,In2),
  l_insert(T,In2,Out).

insert([],X,[X]).
insert([H|T],X,R) :- (H==X -> R=[H|T] ; R=[H|R2],insert(T,X,R2)).

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
