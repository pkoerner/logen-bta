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


:- use_module(abstract_interp).
:- use_module(exact_sets).
:- use_module(builtins).


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

:- begin_tests(memoise_this_call).

test(memoise_this_call1, fail) :-
    % foo :- true.
    memoise_this_call(9001, true, 0, [], true).

test(memoise_this_call2, fail) :-
    % foo :- bar(A), true.
    memoise_this_call(and1(9001), bar, 1, [s], bar(_)).

test(memoise_this_call3) :-
    % foo :- \+ bar(A).
    memoise_this_call(not(9001), bar, 1, [s], bar(_)).


test(memoise_this_call4) :-
    % foo :- nl. (random side effect)
    memoise_this_call(9001, nl, 0, [], nl).

:- end_tests(memoise_this_call).

contains_dangerous_construct(not(_)) :- !.
contains_dangerous_construct(X) :- nonvar(X),X=..[_,A], contains_dangerous_construct(A).

%memo_program_point/4 and memo_program_point2/4: original versions
memo_program_point(Path,Fun,Arity,CallPattern) :-
   cli_option(monovariant_bta), retract(memo_entry(Fun,Arity,PrevCallPattern)),!,
   lub_pat(CallPattern,PrevCallPattern,NewCallPattern),
   memo_program_point2(Path,Fun,Arity,NewCallPattern).
memo_program_point(Path,Fun,Arity,CallPattern) :- memo_program_point2(Path,Fun,Arity,CallPattern).

memo_program_point2(Path,Fun,Arity,_CallPattern) :-
   is_built_in(Fun,Arity),!, assert_rescall(Path).
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

:- begin_tests(check_unfold_call).

test(check_unfold_call1, [fail, cleanup((prolog_reader:retract(':-'(foo(_A,_B), true)),
                                         retractall(calls_answers(foo, 2, _, _, _))))]) :-
    prolog_reader:assert(':-'(foo(_A,_B), true)),
    check_unfold_call(foo(_A, _B), [d, d], foo, 2, aenv([], [], [], []), _OutSv, _Path).

test(check_unfold_call2, [ %block('I have no idea what is happening here'),
                          cleanup((prolog_reader:retract(':-'(foo(_A,_B), true)),
                                   retractall(calls_answers(foo, 2, _, _, _)),
                                   retractall(logen_unfold(9001))))]) :-
    prolog_reader:assert(':-'(foo(_A,_B), true)),
    \+ check_unfold_call(foo(_A, _B), [d, d], foo, 2, aenv([], [], [], []), _OutSv, 9001),
    calls_answers(foo, 2, user, [d,d], bot),
    \+ logen_unfold(9001),
    \+ check_unfold_call(foo(_A, _B), [d, d], foo, 2, aenv([], [], [], []), _OutSv, _Path),
    calls_answers(foo, 2, user, [d,d], bot),
    logen_unfold(9001).




:- end_tests(check_unfold_call).

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













/* take a pattern and set all arguments as static */
set_static([],[]).
set_static([_|T],[s|ST]) :- set_static(T,ST).


