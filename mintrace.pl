% _______________ determinism checks _______________

:- dynamic detchecked/1.

det(Functor/Arity) :-
        ignore(retract(detchecked(Functor/Arity))),
        assert(detchecked(Functor/Arity)),
        length(Args, Arity),
        Head =.. [Functor | Args],
        atom_concat('__detcheck$', Functor, MangledFunctor),
        MangledHead =.. [MangledFunctor | Args],
        ignore(retract((Head :- _))),
        assert((Head :- (MangledHead, ! ;
                        deterror(Head)))).

deterror(Head) :-
        tell(user_error),
        nl,
        write('*** Predicate call should not have failed:'),
        nl,
        writeq(Head),
        nl,
        assertion(fail).


term_expansion((Head :- Body), (MangledHead :- Body)) :-
        !,
        term_expansion(Head, MangledHead).

term_expansion(Head, MangledHead) :-
        Head =.. [Functor | Args],
        length(Args, Arity),
        detchecked(Functor/Arity),
        !,
        atom_concat('__detcheck$', Functor, MangledFunctor),
        MangledHead =.. [MangledFunctor | Args].

% _______________ helpers _______________

% lookup(Name, Env, Res) lookup a variable Name in an environment Env and return
% result Res. The environment is a list of Name/Value terms.

:- det(lookup/3).
lookup(X, [], _) :- throw(key_not_found(X)).
lookup(Name, [Name/Value | _], Value) :- !.
lookup(Name, [_ | Rest], Value) :- lookup(Name, Rest, Value).

% write(Env, Var, Val, NEnv) set the binding of variable Var in an
% environment Env to value Val and return a new environment NEnv.
:- det(store/4).
store([], X, V, [X/V]).
store([Name/_ | Rest], Name, Value, [Name/Value | Rest]) :- !.
store([Pair | Rest], Name, Value, [Pair | NewRest]) :- store(Rest, Name, Value, NewRest).

remove_from_env(_, [], []).
remove_from_env(X, [X/_ | T], T) :- !.
remove_from_env(X, [A/B | T1], [A/B | T2]) :-
    remove_from_env(X, T1, T2).

% resolve(Arg, IState, Val) turn an argument Arg (which can be either a variable
% or a constant) into a value Val, either by just unwrapping a constant or by
% doing a lookup in the environment.
:- det(resolve/3).
resolve(const(X), _IState, X).
resolve(var(X), IState, Y) :-
    get_env(IState, Env),
    lookup(X, Env, Y).

:- det(resolve_args/3).

resolve_args([], _, []).
resolve_args([Arg|T1], Env, [RArg|T2]) :-
    resolve(Arg, Env, RArg),
    resolve_args(T1, Env, T2).


% execute operations
:- det(do_op/4).
do_op(mul, X, Y, Z) :- Z is X * Y.
do_op(add, X, Y, Z) :- Z is X + Y.
do_op(sub, X, Y, Z) :- Z is X - Y.
do_op(eq, X, Y, Z) :- X == Y -> Z = 1; Z = 0.
do_op(ge, X, Y, Z) :- X >= Y -> Z = 1; Z = 0.
do_op(readlist, L, I, X) :- nth0(I, L, X).
do_op(assign, A, _, A).
do_op(Op, _, _, _) :- throw(missing_op(Op)).


% ensure(Goal) makes sure that goal Goal succeeds, otherwise throws an
% exception (like an assert statement in C and similar languages)
ensure(Goal) :-
    call(Goal) -> true; throw(assertion_failed(Goal)).

% _______________ interpreter _______________

% check_syntax_interp(Labels) to check whether the argument is a syntactically valid program.
:- det(check_syntax_interp/1).
check_syntax_interp(Functions) :-
    check_syntax_interp(Functions, Functions).
:- det(check_syntax_interp/2).
check_syntax_interp([], _).
check_syntax_interp([Name/func(Args, _, Labels) | Rest], AllFuncs) :-
    atom(Name),
    write(checking(Name)), nl,
    check_syntax_interp_allargs(Args),
    check_syntax_interp_labels(Labels, code(Labels, AllFuncs)),
    write(ok(Name)), nl,
    check_syntax_interp(Rest, AllFuncs).

check_syntax_interp_allargs([]).
check_syntax_interp_allargs([H|T]) :-
    atom(H),
    check_syntax_interp_allargs(T).

:- det(check_syntax_interp_labels/2).

check_syntax_interp_labels([], _).
check_syntax_interp_labels([Name/Op | Rest], Code) :-
    atom(Name),
    check_syntax_interp_op(Op, Code),
    check_syntax_interp_labels(Rest, Code).

:- det(check_syntax_interp_op/2).

check_syntax_interp_op(op(Res, Op, Arg1, Arg2, Rest), Code) :-
    atom(Res), member(Op, [mul, add, sub, ge, eq, assign, readlist]),
    check_syntax_interp_arg(Arg1),
    check_syntax_interp_arg(Arg2),
    check_syntax_interp_op(Rest, Code).

check_syntax_interp_op(new(Res, Shape, Rest), Code) :-
    atom(Res),
    atom(Shape),
    check_syntax_interp_op(Rest, Code).

check_syntax_interp_op(set(Arg, Field, ArgValue, Rest), Code) :-
    check_syntax_interp_arg(Arg),
    check_syntax_interp_arg(ArgValue),
    atom(Field),
    check_syntax_interp_op(Rest, Code).

check_syntax_interp_op(get(Res, Arg, Field, Rest), Code) :-
    atom(Res),
    check_syntax_interp_arg(Arg),
    atom(Field),
    check_syntax_interp_op(Rest, Code).

check_syntax_interp_op(if_class(Arg, Shape, L1, L2), Code) :-
    atom(Shape),
    check_syntax_interp_arg(Arg),
    check_label_exists(L1, Code),
    check_label_exists(L2, Code).

check_syntax_interp_op(promote(Arg, L1), Code) :-
    check_syntax_interp_arg(Arg),
    check_label_exists(L1, Code).

check_syntax_interp_op(call(Res, FuncName, Args, L), Code) :-
    atom(Res),
    check_syntax_interp_args(Args),
    check_label_exists(L, Code),
    check_function_exists(FuncName, Code).

check_syntax_interp_op(if(Arg, L1, L2), Code) :-
    check_syntax_interp_arg(Arg),
    check_label_exists(L1, Code),
    check_label_exists(L2, Code).

check_syntax_interp_op(jump(L), Code) :-
    check_label_exists(L, Code).

check_syntax_interp_op(error(Reason), _) :-
    atom(Reason).

check_syntax_interp_op(return(Arg), _) :-
    check_syntax_interp_arg(Arg).

check_syntax_interp_args([]).
check_syntax_interp_args([Arg|T]) :-
    check_syntax_interp_arg(Arg),
    check_syntax_interp_args(T).

check_syntax_interp_arg(var(Name)) :- atom(Name).
check_syntax_interp_arg(const(_)).

check_label_exists(L, Code) :-
    lookup_label(L, Code, _).

check_function_exists(FuncName, code(_, Functions)) :-
    lookup(FuncName, Functions, _).

% _______________


interp_function(FuncName, Functions, Args, Res) :-
    lookup_function(FuncName, code([], Functions), ArgNames, Code, FirstLabel),
    ensure(same_length(ArgNames, Args)),
    create_start_env(ArgNames, Args, Env),
    interp_label(FirstLabel, Code, Env, [], Res).

lookup_label(Label, code(Labels, _), Block) :-
    lookup(Label, Labels, Block).

lookup_function(FuncName, Code, ArgNames, FuncCode, FirstLabel) :-
    lookup_function(FuncName, Code, ArgNames, _, FuncCode, FirstLabel).

lookup_function(FuncName, code(_, Functions), ArgNames, Loopy, code(Labels, Functions), FirstLabel) :-
    lookup(FuncName, Functions, func(ArgNames, Loopy, Labels)),
    Labels = [FirstLabel/ _| _].

interp_state(Env, Heap, Stack, Res, interpstate(Env, Heap, Stack, Res)).

:- det(get_result/2).
get_result(interpstate(_Env, _Heap, _Stack, Res), Res).
:- det(get_env/2).
:- discontiguous get_env/2.
get_env(interpstate(Env, _Heap, _Stack, _Res), Env).
:- det(set_result/3).
set_env(interpstate(_Env, Heap, Stack, Res), NEnv, interpstate(NEnv, Heap, Stack, Res)).
:- det(get_heap/2).
get_heap(interpstate(_Env, Heap, _Stack, _Res), Heap).
:- det(set_heap/3).
set_heap(interpstate(Env, _Heap, Stack, Res), NHeap, interpstate(Env, NHeap, Stack, Res)).
:- det(get_stack/2).
get_stack(interpstate(_Env, _Heap, Stack, _Res), Stack).
:- det(set_stack/3).
set_stack(interpstate(Env, Heap, _Stack, Res), NStack, interpstate(Env, Heap, NStack, Res)).

:- det(write_env/4).
write_env(IState, Var, Value, NIState) :-
    get_env(IState, Env),
    store(Env, Var, Value, NEnv),
    set_env(IState, NEnv, NIState).

create_start_env([], [], []).
create_start_env([Name|T1], [Val|T2], [Name/Val|T3]) :-
    create_start_env(T1, T2, T3).

interp_label(Label, Code, Env, Stack, Res) :-
    interp_label(Label, Code, Env, [], Stack, Res).

interp_label(Label, Code, Env, Heap, Stack, Res) :-
    interp_state(Env, Heap, Stack, Res, IState),
    interp_label(Label, Code, IState).

interp_label(Label, Code, IState) :-
    lookup_label(Label, Code, Block),
    interp(Block, Code, IState).

interp_jump(L, Code, IState) :-
    lookup_label(L, Code, Block),
    interp(Block, Code, IState).

% interp(Block, Code, IState) executes flow graph program Block
:- det(interp/3).
interp(op(ResultVar, Op, Arg1, Arg2, NextOp), Code, IState) :-
    interp_op(ResultVar, Op, Arg1, Arg2, IState, NIState),
    interp(NextOp, Code, NIState).

interp(promote(_, L), Code, IState) :-
    interp_jump(L, Code, IState).

interp(jump(L), Code, IState) :-
    interp_jump(L, Code, IState).

interp(if(Arg, L1, L2), Code, IState) :-
    resolve(Arg, IState, RArg),
    (RArg == 0 ->
        L = L2
    ;
        L = L1
    ),
    interp_jump(L, Code, IState).

interp(return(Arg), _, IState) :-
    resolve(Arg, IState, Val),
    get_stack(IState, Stack),
    interp_return(Stack, Val, IState).

interp_return([], Val, IState) :-
    get_result(IState, Val),
    print(Val), nl.

interp_return([frame(L, Code, Env, ResultVar)| Stack], Val, IState) :-
    store(Env, ResultVar, Val, NEnv),
    set_env(IState, NEnv, IState1),
    set_stack(IState1, Stack, NIState),
    interp_jump(L, Code, NIState).

% object operations

interp(new(ResultVar, Class, NextOp), Code, IState) :-
    new_object(ResultVar, Class, IState, NIState),
    interp(NextOp, Code, NIState).

interp(get(ResultVar, Arg, Field, NextOp), Code, IState) :-
    resolve(Arg, IState, RArg),
    get_object(RArg, IState, Obj),
    get_field(Obj, Field, Value),
    write_env(IState, ResultVar, Value, NIState),
    interp(NextOp, Code, NIState).

interp(set(Arg, Field, ValueArg, NextOp), Code, IState) :-
    resolve(Arg, IState, Address),
    resolve(ValueArg, IState, Value),
    set_field(Address, Field, Value, IState, NIState),
    interp(NextOp, Code, NIState).

interp(if_class(Arg, Cls, L1, L2), Code, IState) :-
    resolve(Arg, IState, RArg),
    get_object(RArg, IState, obj(Cls1, _)),
    (Cls == Cls1 ->
        L = L1
    ;
        L = L2
    ),
    lookup_label(L, Code, Block),
    interp(Block, Code, IState).

% call

interp(call(ResultVar, FuncName, Args, L), Code, IState) :-
    lookup_function(FuncName, Code, ArgNames, NCode, Label),
    resolve_args(Args, IState, RArgs),
    create_start_env(ArgNames, RArgs, StartEnv),
    get_env(IState, Env),
    get_stack(IState, Stack),
    NStack = [frame(L, Code, Env, ResultVar) | Stack],
    set_env(IState, StartEnv, IState1),
    set_stack(IState1, NStack, NIState),
    interp_label(Label, NCode, NIState).

interp_op(ResultVar, Op, Arg1, Arg2, IState, NIState) :-
    resolve(Arg1, IState, RArg1),
    resolve(Arg2, IState, RArg2),
    do_op(Op, RArg1, RArg2, Res),
    write_env(IState, ResultVar, Res, NIState).

% heap manipulation

new_object_heap(Class, Heap, [NewObj/obj(Class, [])|Heap], NewObj) :-
    gensym(Class, NewObj). % invent address

new_object(ResultVar, Class, IState, NIState) :-
    get_heap(IState, Heap),
    new_object_heap(Class, Heap, NHeap, NewObj),
    set_heap(IState, NHeap, IState1),
    write_env(IState1, ResultVar, NewObj, NIState).

get_object(Address, IState, Object) :-
    get_heap(IState, Heap),
    lookup(Address, Heap, Object).

get_field(obj(_, Fields), Field, Value) :-
    lookup(Field, Fields, Value).

set_field(Address, Field, Value, IState, NIState) :-
    get_heap(IState, Heap),
    lookup(Address, Heap, obj(Cls, Fields)),
    store(Fields, Field, Value, NFields),
    store(Heap, Address, obj(Cls, NFields), NHeap),
    set_heap(IState, NHeap, NIState).



% _______________ simple tracer _______________

% do_trace(Label, Env) start tracing of code at label Label with environment Env
do_trace(FuncName, L, Functions, Env, Res) :-
    lookup(FuncName, Functions, func(_, _, Labels)),
    interp_state(Env, [], [], Res, IState),
    do_trace(L, code(Labels, Functions), IState).
do_trace(L, Code, IState) :-
    lookup_label(L, Code, StartCode),
    trace(StartCode, Code, IState, ProducedTrace, tstate(L, ProducedTrace)).

check_syntax_trace(op(_, _, _, _, T), Labels) :-
    check_syntax_trace(T, Labels).
check_syntax_trace(new(_, _, T), Labels) :-
    check_syntax_trace(T, Labels).
check_syntax_trace(get(_, _, _, T), Labels) :-
    check_syntax_trace(T, Labels).
check_syntax_trace(set(_, _, _, T), Labels) :-
    check_syntax_trace(T, Labels).
check_syntax_trace(guard(_, _, L, T), Labels) :-
    lookup(L, Labels, _),
    check_syntax_trace(T, Labels).
check_syntax_trace(guard_class(_, _, L, T), Labels) :-
    lookup(L, Labels, _),
    check_syntax_trace(T, Labels).
check_syntax_trace(enter(L, Labels, _, _, T), Labels) :-
    lookup(L, Labels, _),
    check_syntax_trace(T, Labels).
check_syntax_trace(return(_, T), Labels) :-
    check_syntax_trace(T, Labels).
check_syntax_trace(loop, _).

% trace(Code, Labels, Env, Trace, TState) trace the code Code in environment Env
% yielding trace Trace. The TState contains information about where to end
% tracing and the full trace.
:- det(trace/8).

trace(op(ResultVar, Op, Arg1, Arg2, Rest), Code, IState,
      op(ResultVar, Op, Arg1, Arg2, T), TState) :-
    interp_op(ResultVar, Op, Arg1, Arg2, IState, NIState),
    trace(Rest, Code, NIState, T, TState).

trace(promote(Arg, L), Code, IState, guard(Arg, Val, L, Code, T), TState) :-
    resolve(Arg, IState, Val),
    trace_jump(L, Code, IState, T, TState).

trace(return(Arg), _, IState, return(Arg, T), TState) :-
    resolve(Arg, IState, Val),
    get_stack(IState, Stack),
    trace_return(Stack, Val, IState, T, TState).

trace(jump(L), Code, IState, T, TState) :-
    trace_jump(L, Code, IState, T, TState).

trace(if(Arg, L1, L2), Code, IState, guard(Arg, Val, OL, Code, T), TState) :-
    resolve(Arg, IState, Val),
    (Val == 0 ->
        L = L2, OL = L1
    ;
        ensure(Val == 1),
        L = L1, OL = L2
    ),
    trace_jump(L, Code, IState, T, TState).

trace(new(ResultVar, Class, NextOp), Code, IState, new(ResultVar, Class, T), TState) :-
    new_object(ResultVar, Class, IState, NIState),
    trace(NextOp, Code, NIState, T, TState).

trace(get(ResultVar, Arg, Field, NextOp), Code, IState, get(ResultVar, Arg, Field, T), TState) :-
    resolve(Arg, IState, RArg),
    get_object(RArg, IState, Obj),
    get_field(Obj, Field, Value),
    write_env(IState, ResultVar, Value, NIState),
    trace(NextOp, Code, NIState, T, TState).

trace(set(Arg, Field, ValueArg, NextOp), Code, IState, set(Arg, Field, ValueArg, T), TState) :-
    resolve(Arg, IState, Address),
    resolve(ValueArg, IState, Value),
    set_field(Address, Field, Value, IState, NIState),
    trace(NextOp, Code, NIState, T, TState).

trace(if_class(Arg, Cls, L1, L2), Code, IState, guard_class(Arg, Cls, OL, Code, T), TState) :-
    resolve(Arg, IState, RArg),
    get_object(RArg, IState, obj(Cls1, _)),
    (Cls == Cls1 ->
        L = L1, OL = L2
    ;
        L = L2, OL = L1
    ),
    trace_jump(L, Code, IState, T, TState).

trace(call(ResultVar, FuncName, Args, L), Code, IState, call(ResultVar, FuncName, Args, T), TState) :-
    lookup_function(FuncName, Code, ArgNames, Loopy, NewCode, FirstLabel),
    Loopy = loop, !,
    trace,
    xxx.

trace(call(ResultVar, FuncName, Args, L), Code, IState,
      enter(L, Code, ResultVar, Mapping, T), TState) :-
    lookup_function(FuncName, Code, ArgNames, Loopy, NCode, Label),
    Loopy = noloop, !,

    resolve_args(Args, IState, RArgs),
    create_start_env(ArgNames, RArgs, StartEnv),
    get_env(IState, Env),
    get_stack(IState, Stack),
    NStack = [frame(L, Code, Env, ResultVar) | Stack],
    set_env(IState, StartEnv, IState1),
    set_stack(IState1, NStack, NIState),

    create_start_env(ArgNames, Args, Mapping),
    trace_jump(Label, NCode, NIState, T, TState).

trace_jump(L, _Code, IState, loop, tstate(L, FullTrace)) :-
    !, % prevent more tracing
    write(trace), nl, write_trace(FullTrace), nl, % --
    %check_syntax_trace(FullTrace, Labels),
    get_env(IState, Env),
    do_optimize(FullTrace, Env, OptTrace),
    write(opttrace), nl, write_trace(OptTrace), nl, % --
    runtrace_opt(OptTrace, IState, OptTrace).

trace_jump(L, Code, IState, T, TState) :-
    lookup_label(L, Code, Block),
    trace(Block, Code, IState, T, TState).

trace_return([], Val, IState) :-
    get_result(IState, Val),
    print(Val), nl.

trace_return([frame(L, Code, Env, ResultVar)|Stack], Val, IState, T, TState) :-
    store(Env, ResultVar, Val, NEnv),
    set_env(IState, NEnv, IState1),
    set_stack(IState1, Stack, NIState),
    trace_jump(L, Code, NIState, T, TState).


% write_trace(Trace) print trace Trace in a readable way
write_trace(loop) :- !, write('  loop'), nl.
write_trace(loop(V)) :- !, write('  loop'), write(V), nl.
write_trace(Op) :-
    Op =.. L,
    append(L0, [NextOp], L),
    SOp =.. L0,
    write('  '), write(SOp), nl,
    write_trace(NextOp).



% _______________ run traces _______________


% runtrace_opt(Trace, IState, TraceFromStart) execute a trace Trace in environment Env
% with the full trace being also given as argument TraceFromStart

:- det(runtrace_opt/3).
runtrace_opt(op(ResultVar, Op, Arg1, Arg2, Rest), IState, TraceFromStart) :-
    interp_op(ResultVar, Op, Arg1, Arg2, IState, NIState),
    runtrace_opt(Rest, NIState, TraceFromStart).

runtrace_opt(guard(Arg, C, OState, L, Code, Rest), IState, TraceFromStart) :-
    resolve(Arg, IState, Val),
    (Val == C ->
        runtrace_opt(Rest, IState, TraceFromStart)
    ;
        execute_fallback(OState, IState, NIState),
        interp_label(L, Code, NIState)
    ).

runtrace_opt(new(ResultVar, Class, Rest), IState, TraceFromStart) :-
    new_object(ResultVar, Class, IState, NIState),
    runtrace_opt(Rest, NIState, TraceFromStart).

runtrace_opt(get(ResultVar, Arg, Field, Rest), IState, TraceFromStart) :-
    resolve(Arg, IState, RArg),
    get_object(RArg, IState, Obj),
    get_field(Obj, Field, Value),
    write_env(IState, ResultVar, Value, NIState),
    runtrace_opt(Rest, NIState, TraceFromStart).

runtrace_opt(set(Arg, Field, ValueArg, Rest), IState, TraceFromStart) :-
    resolve(Arg, IState, Address),
    resolve(ValueArg, IState, Value),
    set_field(Address, Field, Value, IState, NIState),
    runtrace_opt(Rest, NIState, TraceFromStart).

runtrace_opt(guard_class(Arg, Class, OState, L, Code, Rest), IState, TraceFromStart) :-
    resolve(Arg, IState, Val),
    get_object(Val, IState, obj(Class1, _)),
    (Class == Class1 ->
        runtrace_opt(Rest, IState, TraceFromStart)
    ;
        execute_fallback(OState, IState, NIState),
        interp_label(L, Code, NIState)
    ).

runtrace_opt(loop(Renames), IState, TraceFromStart) :-
    get_env(IState, Env),
    execute_phi(Renames, Env, NEnv),
    set_env(IState, NEnv, NIState),
    runtrace_opt(TraceFromStart, NIState, TraceFromStart).

execute_fallback(OState, IState, NIState) :-
    write(OState), nl,
    write(IState), nl,
    get_env(OState, SSAEnv),
    get_stack(OState, ResumeStack),
    get_heap(OState, AbsHeap),
    get_env(IState, Env),
    get_heap(IState, Heap),
    get_stack(IState, Stack),
    execute_fallback(SSAEnv, ResumeStack, Env, AbsHeap, InterpEnv, Heap, InterpHeap, Stack, InterpStack),
    get_result(IState, Res),
    interp_state(InterpEnv, InterpHeap, InterpStack, Res, NIState).

execute_fallback(ResumeEnv, ResumeStack, Env, AbsHeap, InterpEnv, Heap, InterpHeap, Stack, InterpStack) :-
    write(ResumeEnv), nl,
    execute_fallback(ResumeEnv, Env, NEnv, AbsHeap, NAbsHeap, InterpEnv, Heap, Heap1),
    execute_fallback_rebuild_stack(ResumeStack, Stack, InterpStack, NEnv, NAbsHeap, Heap1, InterpHeap).


execute_fallback([], Env, Env, AbsHeap, AbsHeap, [], H, H).
execute_fallback([Var/Val | T], Env, NEnv, AbsHeap, NAbsHeap, [Var/NVal | T1], Heap, NHeap) :-
    execute_escape(Val, Env, Env1, AbsHeap, AbsHeap1, Heap, Heap2, NVal),
    execute_fallback(T, Env1, NEnv, AbsHeap1, NAbsHeap, T1, Heap2, NHeap).

execute_fallback_rebuild_stack([], Stack, Stack, _Env, _AbsHeap, Heap, Heap).
execute_fallback_rebuild_stack([frame(L, Code, SSAEnv, ResultVar) | T], Stack, [frame(L, Code, InterpEnv, ResultVar) | InterpStack], Env, AbsHeap, Heap, InterpHeap) :-
    execute_fallback(SSAEnv, Env, NEnv, AbsHeap, NAbsHeap, InterpEnv, Heap, NHeap),
    execute_fallback_rebuild_stack(T, Stack, InterpStack, NEnv, NAbsHeap, NHeap, InterpHeap).

execute_escape(const(C), Env, Env, AbsHeap, AbsHeap, Heap, Heap, C).
execute_escape(var(Var), Env, Env, AbsHeap, AbsHeap, Heap, Heap, Val) :-
    maybe_get_object_heap(Var, AbsHeap, not_virtual), !, lookup(Var, Env, Val).
execute_escape(var(Var), Env, NEnv, AbsHeap, NAbsHeap, Heap, NHeap, NewObj) :-
    maybe_get_object_heap(Var, AbsHeap, obj(Cls, Fields)),
    new_object_heap(Cls, Heap, Heap1, NewObj),
    store(Env, Var, NewObj, Env1),
    remove_from_env(Var, AbsHeap, AbsHeap1),
    execute_escape_fields(Fields, NewObj, Env1, NEnv, AbsHeap1, NAbsHeap, Heap1, NHeap).

execute_escape_fields([], _, Env, Env, AbsHeap, AbsHeap, Heap, Heap).
execute_escape_fields([Field/Value|Rest], Obj, Env, NEnv, AbsHeap, NAbsHeap, Heap, NHeap) :-
    execute_escape(Value, Env, Env1, AbsHeap, AbsHeap1, Heap, Heap1, Val),
    set_field(Obj, Field, Val, Heap1, Heap2),
    execute_escape_fields(Rest, Obj, Env1, NEnv, AbsHeap1, NAbsHeap, Heap2, NHeap).



% _______________ optimization _______________
%
% do_optimize(Trace, Env, OptimizedTrace) optimize a trace Trace, returning
% OptimizedTrace
do_optimize(Trace, Env, OptimizedTrace) :-
    initialize_ssa_env(Env, SSAEnv, DefinedVars),
    optimize_state(SSAEnv, [], DefinedVars, [], OState),
    optimize(Trace, OState, OptimizedTrace).

optimize_state(SSAEnv, AbsHeap, DefinedVars, Stack,
               ostate(SSAEnv, AbsHeap, DefinedVars, Stack)).
get_definedvars(ostate(_SSAEnv, _AbsHeap, DefinedVars, _Stack), DefinedVars).
get_env(ostate(SSAEnv, _, _, _), SSAEnv).
set_env(ostate(_SSAEnv, AbsHeap, DefinedVars, Stack), NEnv, ostate(NEnv, AbsHeap, DefinedVars, Stack)).
get_heap(ostate(_Env, Heap, _DefinedVars, _Stack), Heap).
set_heap(ostate(Env, _Heap, DefinedVars, Stack), NHeap,
         ostate(Env, NHeap, DefinedVars, Stack)).
get_stack(ostate(_Env, _Heap, _DefinedVars, Stack), Stack).
set_stack(ostate(Env, Heap, DefinedVars, _Stack), NStack,
          ostate(Env, Heap, DefinedVars, NStack)).

invent_new_var(Var, NewVar) :- gensym(Var, NewVar).

initialize_ssa_env([], [], []).
initialize_ssa_env([Var/_ | Rest1], [Var/var(Var) | Rest2], [Var | Rest3]) :-
    initialize_ssa_env(Rest1, Rest2, Rest3).

sresolve(const(X), _OState, const(X)).
sresolve(var(V), OState, X) :-
    get_env(OState, SSAEnv), lookup(V, SSAEnv, X).

% optimize(Trace, SSAEnv, DefinedVars, Stack, NewTrace) optimize trace Trace under SSA-environment SSAEnv

execute_phi([], _, []).
execute_phi([Var/Val | T], Env, [Var/NVal | T1]) :-
    (Val = const(C) ->
        NVal = C
    ;
        Val = var(IVar),
        lookup(IVar, Env, NVal)
    ),
    execute_phi(T, Env, T1).

:- det(optimize/3).
optimize(op(ResultVar, Op, Arg1, Arg2, Rest), OState, NewTrace) :-
    sresolve(Arg1, OState, RArg1),
    sresolve(Arg2, OState, RArg2),
    (RArg1 = const(C1), RArg2 = const(C2) ->
        do_op(Op, C1, C2, Res),
        Result = const(Res),
        NewTrace = RestTrace
    ;
        invent_new_var(ResultVar, Res),
        Result = var(Res),
        NewTrace = op(Res, Op, RArg1, RArg2, RestTrace)
    ),
    write_env(OState, ResultVar, Result, NOState),
    optimize(Rest, NOState, RestTrace).

optimize(enter(L, Code, ResultVar, Renames, Rest), OState, NewTrace) :-
    get_env(OState, SSAEnv),
    execute_phi(Renames, SSAEnv, NEnv),
    set_env(OState, NEnv, OState1),
    get_stack(OState1, Stack),
    set_stack(OState1, [frame(L, Code, SSAEnv, ResultVar) | Stack], NOState),
    optimize(Rest, NOState, NewTrace).

optimize(return(Res, RestTrace), OState, NewTrace) :-
    get_stack(OState, [frame(_, _, TargetSSAEnv, ResVar)| Stack]),
    sresolve(Res, OState, RRes),
    store(TargetSSAEnv, ResVar, RRes, NEnv),
    set_env(OState, NEnv, OState1),
    set_stack(OState1, Stack, NOState),
    optimize(RestTrace, NOState, NewTrace).

optimize(loop, OState, Trace) :-
    get_stack(OState, Stack),
    ensure(Stack = []),
    get_definedvars(OState, DefinedVars),
    get_env(OState, SSAEnv),
    get_heap(OState, AbsHeap),
    phis_and_escapes(DefinedVars, SSAEnv, AbsHeap, PhiNodes, Trace, loop(PhiNodes)).

phis_and_escapes([], _, _, [], Trace, Trace).
phis_and_escapes([Var | Rest], SSAEnv, AbsHeap, [Var/Val | Rest2], Trace, EndTrace) :-
    lookup(Var, SSAEnv, Val),
    escape(Val, AbsHeap, NHeap, Trace, NewTrace),
    phis_and_escapes(Rest, SSAEnv, NHeap, Rest2, NewTrace, EndTrace).


optimize(guard(Arg, C, L, Code, Rest), OState, NewTrace) :-
    sresolve(Arg, OState, Val),
    (Val = const(C1) ->
        ensure(C1 = C), % -- otherwise the loop is invalid
        NOState = OState,
        NewTrace = RestTrace
    ;
        Arg = var(OrigVar),
        write_env(OState, OrigVar, const(C), NOState),
        NewTrace = guard(Val, C, OState, L, Code, RestTrace)
    ),
    optimize(Rest, NOState, RestTrace).

% abstract heap maps SSAVar -> obj(Cls, Fields)
% Fields are var(SSAVar) or const(...)
optimize(new(ResultVar, Class, Rest), OState, NewTrace) :-
    get_heap(OState, AbsHeap),
    new_object_heap(Class, AbsHeap, NHeap, NewObj),
    set_heap(OState, NHeap, OState1),
    write_env(OState1, ResultVar, var(NewObj), NOState),
    optimize(Rest, NOState, NewTrace).

:- det(maybe_get_object/3).
maybe_get_object(Address, OState, Res) :-
    get_heap(OState, AbsHeap),
    maybe_get_object_heap(Address, AbsHeap, Res).
maybe_get_object_heap(_, [], not_virtual).
maybe_get_object_heap(Address, [Address/Value | _], Res) :- !, Res = Value.
maybe_get_object_heap(Address, [_ | Rest], Value) :- maybe_get_object_heap(Address, Rest, Value).

optimize(get(ResultVar, Arg, Field, Rest), OState, NewTrace) :-
    sresolve(Arg, OState, RArg),
    ensure(RArg = var(Address)),
    maybe_get_object(Address, OState, Obj),
    (Obj = obj(_, _) ->
        get_field(Obj, Field, Value),
        NewTrace = RestTrace
    ;
        ensure(Obj == not_virtual),
        invent_new_var(ResultVar, Res),
        Value = var(Res),
        NewTrace = get(Res, RArg, Field, RestTrace)
    ),
    write_env(OState, ResultVar, Value, NOState),
    optimize(Rest, NOState, RestTrace).

optimize(set(Arg, Field, ValueArg, Rest), OState, NewTrace) :-
    sresolve(Arg, OState, RArg),
    ensure(RArg = var(Address)),
    sresolve(ValueArg, OState, RValueArg),
    maybe_get_object(Address, OState, Obj),
    (Obj = obj(_, _) ->
        set_field(Address, Field, RValueArg, OState, NOState),
        NewTrace = RestTrace
    ;
        get_heap(OState, AbsHeap),
        escape(RValueArg, AbsHeap, NHeap, NewTrace, NewTrace2),
        set_heap(OState, NHeap, NOState),
        NewTrace2 = set(RArg, Field, RValueArg, RestTrace)
    ),
    optimize(Rest, NOState, RestTrace).

optimize(guard_class(Arg, Class, L, Code, Rest), OState, NewTrace) :-
    sresolve(Arg, OState, RArg),
    ensure(RArg = var(Address)),
    maybe_get_object(Address, OState, Obj),
    (Obj = obj(Class1, _), Class = Class1 ->
        NOState = OState,
        NewTrace = RestTrace
    ;
        get_heap(OState, AbsHeap),
        escape(RArg, AbsHeap, NHeap, NewTrace, NewTrace2),
        set_heap(OState, NHeap, NOState),
        NewTrace2 = guard_class(RArg, Class, NOState, L, Code, RestTrace)
    ),
    optimize(Rest, NOState, RestTrace).

escape(const(_), Heap, Heap, Trace, Trace) :- !.
escape(var(X), AbsHeap, NHeap, Trace, NewTrace) :-
    maybe_get_object_heap(X, AbsHeap, Obj),
    (Obj = obj(Cls, Fields) ->
        Trace = new(X, Cls, Trace2),
        remove_from_env(X, AbsHeap, AbsHeap1),
        escape_fields(Fields, X, AbsHeap1, NHeap, Trace2, NewTrace)
    ;
        NHeap = AbsHeap, Trace = NewTrace
    ).

escape_fields([], _, AbsHeap, AbsHeap, Trace, Trace).
escape_fields([FieldName/Value | RestFields], X, AbsHeap, NHeap, Trace, NewTrace) :-
    escape(Value, AbsHeap, AbsHeap1, Trace, set(var(X), FieldName, Value, Trace1)),
    escape_fields(RestFields, X, AbsHeap1, NHeap, Trace1, NewTrace).


% _______________ example programs _______________


% power computes x ** y

functions([
power/func([x, y], loop, [
    power/
        op(res, assign, const(1), const(0),
        op(c, ge, var(y), const(1),
        if(var(c), power_rec, power_done))),
    power_rec/
        op(res, mul, var(res), var(x),
        op(y, sub, var(y), const(1),
        op(c, ge, var(y), const(1),
        if(var(c), power_rec, power_done)))),
    power_done/
        return(var(res))
]),

% promotion example
% while i >= 0
%    i -= promote(x) * 2 + 1

loop/func([i, x], loop, [
    l/
        op(c, ge, var(i), const(0),
        if(var(c), b, l_done)),
    l_done/
        return(var(i)),
    b/
        promote(var(x), b2),
    b2/
        op(x2, mul, var(x), const(2),
        op(x3, add, var(x2), const(1),
        op(i, sub, var(i), var(x3),
        jump(l))))
]),

callloop/func([i, x], loop, [
    l/
        op(c, ge, var(i), const(0),
        if(var(c), b, l_done)),
    l_done/
        return(var(i)),
    b/
        call(x3, timestwoplus1, [var(x)], b2),
    b2/
        op(i, sub, var(i), var(x3),
        jump(l))
]),

timestwoplus1/func([arg], noloop, [
    start/
        op(arg, mul, var(arg), const(2),
        op(arg, add, var(arg), const(1),
        return(var(arg))))
]),



% arithmetic example
% while i >= 0
%    i -= x * 2 + 1

boxedloop/func([startval, xval], loop, [
    start/
        new(i, int,
        set(var(i), value, var(startval),
        new(x, int,
        set(var(x), value, var(xval),
        new(const2, int,
        set(var(const2), value, const(2),
        new(const1, int,
        set(var(const1), value, const(1),
        new(const0, int,
        set(var(const0), value, const(0),
        jump(l))))))))))),
    l/
        call(c, ge, [var(i), var(const0)], l_ge),
    l_ge/
        if(var(c), b, l_done),
    l_done/
        get(ival, var(i), value,
        return(var(ival))),
    b/
        call(x2, mul, [var(x), var(const2)], b_add),
    b_add/
        call(x2, add, [var(x), var(const1)], b_sub),
    b_sub/
        call(i, sub, [var(i), var(x2)], l),
    error/
        return(const(-1000))
]),

add/func([a, b], noloop, [
    start/
        if_class(var(a), int, aint, error),
    aint/
        if_class(var(b), int, bothint, error),
    bothint/
        get(aval, var(a), value,
        get(bval, var(b), value,
        op(resval, add, var(aval), var(bval),
        new(res, int,
        set(var(res), value, var(resval),
        return(var(res))))))),
    error/
        error(not_int)
]),

sub/func([a, b], noloop, [
    start/
        if_class(var(a), int, aint, error),
    aint/
        if_class(var(b), int, bothint, error),
    bothint/
        get(aval, var(a), value,
        get(bval, var(b), value,
        op(resval, sub, var(aval), var(bval),
        new(res, int,
        set(var(res), value, var(resval),
        return(var(res))))))),
    error/
        error(not_int)
]),

ge/func([a, b], noloop, [
    start/
        if_class(var(a), int, aint, error),
    aint/
        if_class(var(b), int, bothint, error),
    bothint/
        get(aval, var(a), value,
        get(bval, var(b), value,
        op(res, ge, var(aval), var(bval),
        if(var(res), returntrue, returnfalse)))),
    returntrue/
        return(const(1)),
    returnfalse/
        return(const(0)),
    error/
        error(not_int)
]),

mul/func([a, b], noloop, [
    start/
        if_class(var(a), int, aint, error),
    aint/
        if_class(var(b), int, bothint, error),
    bothint/
        get(aval, var(a), value,
        get(bval, var(b), value,
        op(resval, mul, var(aval), var(bval),
        new(res, int,
        set(var(res), value, var(resval),
        return(var(res))))))),
    error/
        error(not_int)
]),

plus1/func([a], noloop, [
    start/
        op(res, add, var(a), const(1),
        return(var(res)))
]),

callplus1/func([res], noloop, [
    start/
        call(a, plus1, [var(res)], done),
    done/
        op(res, add, var(a), var(res),
        return(var(res)))
]),


interp/func([bytecode, a], loop, [
    setup/
        op(pc, assign, const(0), const(0),
        op(r0, assign, const(0), const(0),
        op(r1, assign, const(0), const(0),
        op(r2, assign, const(0), const(0),
        jump(bytecode_loop))))),
    % dispatch loop
    bytecode_loop/
        promote(var(bytecode), bytecode_loop_promote_bytecode),
    bytecode_loop_promote_bytecode/
        promote(var(pc), bytecode_loop_promote_pc),
    bytecode_loop_promote_pc/
        op(opcode, readlist, var(bytecode), var(pc),
        op(pc, add, var(pc), const(1),
        op(c, eq, var(opcode), const(jump_if_a),
        if(var(c), op_jump_if_a, not_jump_if_a)))),

    % chain of ifs to emulate a switch
    not_jump_if_a/
          op(c, eq, var(opcode), const(mov_a_r0),
          if(var(c), op_mov_a_r0, not_mov_a_r0)),
    not_mov_a_r0/
          op(c, eq, var(opcode), const(mov_a_r1),
          if(var(c), op_mov_a_r1, not_mov_a_r1)),
    not_mov_a_r1/
          op(c, eq, var(opcode), const(mov_a_r2),
          if(var(c), op_mov_a_r2, not_mov_a_r2)),
    not_mov_a_r2/
          op(c, eq, var(opcode), const(mov_r0_a),
          if(var(c), op_mov_r0_a, not_mov_r0_a)),
    not_mov_r0_a/
          op(c, eq, var(opcode), const(mov_r1_a),
          if(var(c), op_mov_r1_a, not_mov_r1_a)),
    not_mov_r1_a/
          op(c, eq, var(opcode), const(mov_r2_a),
          if(var(c), op_mov_r2_a, not_mov_r2_a)),
    not_mov_r2_a/
          op(c, eq, var(opcode), const(add_r0_to_a),
          if(var(c), op_add_r0_to_a, not_add_r0_to_a)),
    not_add_r0_to_a/
          op(c, eq, var(opcode), const(add_r1_to_a),
          if(var(c), op_add_r1_to_a, not_add_r1_to_a)),
    not_add_r1_to_a/
          op(c, eq, var(opcode), const(add_r2_to_a),
          if(var(c), op_add_r2_to_a, not_add_r2_to_a)),
    not_add_r2_to_a/
          op(c, eq, var(opcode), const(decr_a),
          if(var(c), op_decr_a, not_decr_a)),
    not_decr_a/
          if(const(1), op_return_a, op_return_a),

    % bytecode implementation
    op_jump_if_a/
          op(c, eq, var(a), const(0),
          op(target, readlist, var(bytecode), var(pc),
          op(pc, add, var(pc), const(1),
          if(var(c), bytecode_loop, op_jump_if_a_jump)))),
    op_jump_if_a_jump/
          op(pc, assign, var(target), const(0),
          jump(bytecode_loop)),
    op_mov_a_r0/
          op(r0, assign, var(a), const(0), jump(bytecode_loop)),
    op_mov_a_r1/
          op(r1, assign, var(a), const(0), jump(bytecode_loop)),
    op_mov_a_r2/
          op(r2, assign, var(a), const(0), jump(bytecode_loop)),
    op_mov_r0_a/
          op(a, assign, var(r0), const(0), jump(bytecode_loop)),
    op_mov_r1_a/
          op(a, assign, var(r1), const(0), jump(bytecode_loop)),
    op_mov_r2_a/
          op(a, assign, var(r2), const(0), jump(bytecode_loop)),
    op_add_r0_to_a/
          op(a, add, var(a), var(r0), jump(bytecode_loop)),
    op_add_r1_to_a/
          op(a, add, var(a), var(r1), jump(bytecode_loop)),
    op_add_r2_to_a/
          op(a, add, var(a), var(r2), jump(bytecode_loop)),
    op_decr_a/
          op(a, sub, var(a), const(1), jump(bytecode_loop)),
    op_return_a/
        return(var(a))
])

]).

run_callplus1(X, Res) :-
    functions(Functions),
    interp_function(callplus1, Functions, [X], Res).

run_boxedloop(X, Res) :-
    functions(Functions),
    interp_function(boxedloop, Functions, [X, 3], Res).

trace_boxedloop(X, Res) :-
    functions(Functions),
    lookup(boxedloop, Functions, func(_, _, Labels)),
    Env = [startval/X, xval/3, i/i, x/x, const0/const0, const1/const1, const2/const2],
    Heap = [i/obj(int, [value/X]), x/obj(int, [value/3]),
                const0/obj(int, [value/0]), const1/obj(int, [value/1]), const2/obj(int, [value/2])],
    Stack = [],
    interp_state(Env, Heap, Stack, Res, IState),
    do_trace(l, code(Labels, Functions), IState).

trace_callloop(I, X, Res) :-
    functions(Functions),
    do_trace(callloop, l, Functions, [i/I, x/X], Res).

% bytecode interpreter


% an example bytecode, computing the square of the accumulator
bytecode_square([
        mov_a_r0,     % i = a
        mov_a_r1,     % copy of 'a'
        % 2:
        mov_r0_a,     % i--
        decr_a,
        mov_a_r0,
        mov_r2_a,     % res += a
        add_r1_to_a,
        mov_a_r2,
        mov_r0_a,     % if i!=0: goto 2
        jump_if_a, 2,
        mov_r2_a,     % return res
        return_a
        ]).

% helper predicates to start off all the examples

power(X, Y, Res) :-
    functions(Functions),
    interp_function(power, Functions, [X, Y], Res).

trace_power(X, Y, Res) :-
    functions(Functions),
    do_trace(power, power_rec, Functions, [x/X, y/Y, res/1], Res).

loop(X, Res) :-
    functions(Functions),
    interp_function(loop, Functions, [X, 3], Res).

trace_loop(X, Res) :-
    functions(Functions),
    do_trace(loop, l, Functions, [i/X, x/3], Res).


run_interp(A, Res) :-
    bytecode_square(B),
    functions(Functions),
    interp_function(interp, Functions, [B, A], Res).

metatrace_interp(A, Res) :-
    bytecode_square(B),
    Env = [bytecode/B, pc/11, a/A, r0/A, r1/A, r2/0, target/2],
    program(bytecode_interpreter, Code),
    do_trace(op_jump_if_a_jump, Code, Env, Res).

trace_interp(A, Res) :-
    bytecode_square(B),
    Env = [bytecode/B, pc/2, a/A, r0/A, r1/A, r2/0],
    program(bytecode_interpreter, Code),
    do_trace(bytecode_loop, Code, Env, Res).


compare_traces(loop(X), O) :-
    !,
    (O = loop(X) ->
        true
    ;
        throw(difference(loop(X), O))
    ).
compare_traces(T1, T2) :-
    T1 =.. L1,
    append(LN1, [NextOp1], L1),
    SOp1 =.. LN1,
    T2 =.. L2,
    append(LN2, [NextOp2], L2),
    SOp2 =.. LN2,
    (SOp1 = SOp2 ->
        true
    ;
        throw(difference(SOp1, SOp2))
    ),
    compare_traces(NextOp1, NextOp2).


:- begin_tests(mintrace).

test(check_functions) :-
    functions(P),
    check_syntax_interp(P).

test(power, true(Res = 1024)) :-
    power(2, 10, Res).

test(loop, true(Res = -5)) :-
    loop(100, Res).

test(interp, true(Res = 256)) :-
    run_interp(16, Res).

test(call, true(Res = 13)) :-
    run_callplus1(6, Res).

test(boxedloop, true(Res = -4)) :-
    run_boxedloop(100, Res).

%test(optimize) :-
%    Trace = guard(var(x), 3, b2,
%            op(x2, mul, var(x), const(2),
%            op(x3, add, var(x2), const(1),
%            op(i, sub, var(i), var(x3),
%            op(c, ge, var(i), const(0),
%            guard(var(c), 1, l_done, loop)))))),
%    optimize(Trace, [i/var(i), x/var(x), x2/var(x2), x3/var(x3), c/var(c)], [], [i, x, x2, x3, c], Res),
%    Res =   guard(var(x), 3, [i/var(i), x/var(x), x2/var(x2), x3/var(x3), c/var(c)], b2,
%            op(I1, sub, var(i), const(7),
%            op(C1, ge, var(I1), const(0),
%            guard(var(C1), 1, [i/var(I1), x/const(3), x2/const(6), x3/const(7), c/var(C1)], l_done,
%            loop([i/var(I1), x/const(3), x2/const(6), x3/const(7), c/const(1)]))))).
%
%test(optimize_guard_bug) :-
%    Trace = op(pc, add, var(source), const(0),
%            guard(var(pc), 1, l_done,
%            op(pc, add, var(pc), const(1),
%            loop))),
%    optimize(Trace, [source/var(source), pc/var(pc)], [], [source, pc], Res),
%    Res1 =   op(PC1, add, var(source), const(0),
%            guard(var(PC1), 1, [source/var(source), pc/var(PC1)], l_done,
%            loop([source/var(source), pc/const(2)]))),
%    compare_traces(Res, Res1).


%test(execute_phi, true(Res = [i/ -1, x/3, x2/6, x3/7, c/0])) :-
%    execute_phi([i/var(i2), x/const(3), x2/const(6), x3/const(7), c/var(c2)], [i/6, x/3, x2/6, x3/7, c/1, i2/ -1, c2/0], Res).
%
test(escape_const) :-
    escape(const(1), [], [], x, x).

test(escape_nonvirtual, true([H, T] = [[], loop])) :-
    escape(var(x), [], H, T, loop).

test(escape_virtual_no_fields) :-
    escape(var(x), [x/obj(type, [])], NH, Trace, loop),
    Trace = new(x, type, loop),
    NH = [].

test(escape_virtual_1_field) :-
    escape(var(x), [x/obj(type, [f/const(1)]), y/obj(type2, [])], NH, Trace, loop),
    Trace = new(x, type,
            set(var(x), f, const(1),
            loop)),
    NH = [y/obj(type2, [])].

test(escape_virtual_virtual) :-
    escape(var(x), [x/obj(type, [f/var(y)]), y/obj(type2, [g/const(1)])], NH, Trace, loop),
    Trace = new(x, type,
            new(y, type2,
            set(var(y), g, const(1),
            set(var(x), f, var(y),
            loop)))),
    NH = [].

test(escape_virtual_virtual_recursive) :-
    escape(var(x), [x/obj(type, [f/var(y)]), y/obj(type2, [g/var(x)])], NH, Trace, loop),
    Trace = new(x, type,
            new(y, type2,
            set(var(y), g, var(x),
            set(var(x), f, var(y),
            loop)))),
    NH = [].

test(trace_loop, true(Res = -5)) :-
    trace_loop(100, Res).
%
%test(trace_newsetguardget, true(Res = 5)) :-
%    Labels = [
%    start/
%        new(x, int,
%        set(var(x), value, const(5),
%        if_class(var(x), int, b, e))),
%    b/
%        get(y, var(x), value,
%        return(var(y))),
%    e/
%        return(const(-5))],
%    do_trace(start, Labels, [], Res).
%
%test(optimize_newsetguardget) :-
%    Trace =
%        new(x, int,
%        set(var(x), value, var(i),
%        get(i, var(x), value,
%        loop))),
%    optimize(Trace, [i/var(i)], [], [i], NewTrace).
%

test(trace_callloop, true(Res = -10)) :-
    trace_callloop(100, 5, Res).

test(trace_boxedloop, true(Res = -4)) :-
    trace_boxedloop(100, Res).

test(trace_power, true(Res = 1024)) :-
     trace_power(2, 10, Res).
%%
%%test(trace_interp, true(Res = 256)) :-
%%    trace_interp(16, Res).
%%
%test(metatrace_interp, true(Res = 256)) :-
%    metatrace_interp(16, Res).

:- end_tests(mintrace).
