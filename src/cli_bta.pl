/* A Binding-Time for Logen */
/* developed by Michael Leuschel and German Vidal */
/* (c) Michael Leuschel and German Vidal 2007-2016 */

/* --------------------------------- */
/*    The Command Line Interface     */
/* --------------------------------- */

portray_message(informational, _).

:- use_module(library(lists)).
:- use_module(new_simple_bta).

% comment in for profiling:
%:- use_module(library(gauge)).  % comment in if you want to profile
%:- prolog_flag(compiling,_,profiledcode). 
 
:- use_module(library(timeout),[time_out/3]).
analyze_files([],_Opt) :- !. %analyze_single_file('sample_input.pl',Opt).
analyze_files([H|T],Opt) :-
    member(F,[H|T]), 
    vprintln(analyze_single_file(F,Opt)),
    (member(time_out(TO),Opt)
      -> (arg_is_number(TO,TONr)
         -> time_out(analyze_single_file(F,Opt),TONr,TimeOutRes),
               (TimeOutRes==time_out -> nl,print('### TIME-OUT OCCURED : '), print(TO), print(' ms'),nl ; true)
         ;  print('### --time_out parameter must be a number: '), print(TO),nl,
            analyze_single_file(F,Opt)
         )
       ; analyze_single_file(F,Opt)
    ),
    vprintln(finished_analyze_single_file(F,Opt)),fail.
analyze_files(_,_).

 go_cli :- 
    prolog_flag(argv,ArgV),
    get_options(ArgV,Options,RemArgV), !,
    (member(verbose,Options)
     -> assert_verbose, print('Options: '),print(Options),nl
      ; (member(very_verbose,Options)
         -> assert_verbose, print('Options: '),print(Options),nl ; true)),
    ((member(entry(N),Options),convert_cli_goal_to_term(N,NT),assert(bta_cli_entry(NT)),fail)
      ; true),
    ((member(help,Options) ; RemArgV=[], \+ member(version,Options)) -> print_help ; true),
    (member(version,Options) -> print_version ; true),
        trace,
    analyze_files(RemArgV,Options),
    (member(profile,Options) -> (view([ size_change_analysis:_, new_size_change_analysis:_])) ; true).




runtime_entry(start) :- go_cli.


get_options([],Rec,Rem) :- !,Rec=[],Rem=[].
get_options(Inputs,RecognisedOptions,RemOptions) :-
   (recognise_option(Inputs,Flag,RemInputs)
     -> (RecognisedOptions = [Flag|RecO2], 
         assert(cli_option(Flag)), %print(Flag),nl,
         RemO2 = RemOptions)
     ;  (Inputs = [H|RemInputs], RemOptions = [H|RemO2], RecO2 = RecognisedOptions)
   ),
   get_options(RemInputs,RecO2,RemO2).

recognise_option(Inputs,Flag,RemInputs) :-
   recognised_option(Heads,Flag),
   append(Heads,RemInputs,Inputs).
   
recognised_option(['--entry',Goal],entry(Goal)).
recognised_option(['-e',N],entry(N)).
recognised_option(['--lib',Goal],used_module(library(Goal))).
recognised_option(['-v'],verbose).
recognised_option(['--verbose'],verbose).
recognised_option(['-vv'],very_verbose).
recognised_option(['-vp'],show_terminating_patterns).
recognised_option(['--summarise'],summarise_calls_answers).
recognised_option(['-sc'],allow_semi_call).
recognised_option(['--semicall'],allow_semi_call).
recognised_option(['-su'],allow_semi_unfold).
recognised_option(['--semiunfold'],allow_semi_unfold).
recognised_option(['-om'],allow_online_memo).
recognised_option(['-ng'],no_global_termination).
recognised_option(['-nl'],no_local_termination).
recognised_option(['-mv'],monovariant_bta).
recognised_option(['--monovariant'],monovariant_bta).
recognised_option(['--ignorehints'],ignorehints).
recognised_option(['-ih'],ignorehints).
recognised_option(['-ll'],allow_list_length_norm).
recognised_option(['-lg'],labeled_graphs).
%recognised_option(['--nolabels'],use_old_size_change_analysis).
recognised_option(['--profile'],profile).
%%recognised_option(['-es'],extended_sca).
recognised_option(['-o',F],output(F)).
recognised_option(['--help'],help).
recognised_option(['-help'],help).
recognised_option(['--version'],version).
recognised_option(['-version'],version).
recognised_option(['--time_out',T],time_out(T)). % :- arg_is_number(T,TNr).
recognised_option(['-d',F],dependency_graph(F)).
recognised_option(['-d2',F],dependency_graph2(F)).
recognised_option(['-scc'],use_sccs). % :- assert(cli_option(use_old_size_change_analysis)).
recognised_option(['--scc'],use_sccs).% :- assert(cli_option(use_old_size_change_analysis)).
recognised_option(['--oneloop'],first_select_nodes_which_appear_in_one_loop).

arg_is_number(Arg,Nr) :- name(Arg,Str),name(Nr,Str),number(Nr).

:- use_module(library(codesio)).

convert_cli_goal_to_term(CLIGOAL,Term) :-
   on_exception(Exception,
      (atom_codes(CLIGOAL,Codes),
       read_from_codes(Codes,Term)),
      (nl,print('### Illegal Command-Line Goal: "'), print(CLIGOAL),print('"'),nl,
       format("### Use following format: \"Goal.\"~n",[]),
       print('### Exception: '), print(Exception),nl,
       halt)
     ).
     

print_help :- format("Size Change BTA for LOGEN~n",[]),
              format("Usage: bta [Options] PLFILE~n Possible options:~n",[]),
              format("   --help: prints this message~n",[]),
              format("   --entry \"GOAL.\": use GOAL as entry point for bta~n",[]),
              format("                    GOAL = pred(a1,...,an) where ai = s,list_nv,list,nv or d~n",[]),
              format("   -o FILE: write annotated program into FILE~n",[]),
              format("   -sc: Allow semicall annotations~n",[]),
              format("   -su: Allow semiunfold annotations~n",[]),
              format("   -om: Allow online memo annotations~n",[]),
              format("   -mv: Monovariant Analysis (max. 1 filter decl. per predicate)~n",[]),
              format("   -ng: Do not try to ensure global termination~n",[]),
              format("   -nl: Do not try to ensure local termination~n",[]),
              format("   -ih: ignore $MEMOANN + $MEMOCALL hints~n",[]),
              format("   -ll: Allow List-Length norm~n",[]),
              format("   --scc: use scc preprocessing (--oneloop)~n",[]),
              format("   --time_out T:    max runtime per file (in ms)~n",[]),
              format("   -d FILE:    display dependency graph~n",[]),
              format("   -v, --verbose: print debugging messages~n",[]),
              format("   -vv: print even more debugging messages~n",[]),
              format("   --version: print version information~n~n",[]).


print_version :- 
   format("Logen-BTA Version from May 2016~n",[]).

create_size_change_graphs:-
    prolog_reader:get_clause(Call,Body,_Ref),
    %nl,print(prolog_reader:get_clause(Call,Body,_Ref)),
    add_sc_graphs(Body,Call),
    fail.
create_size_change_graphs.

