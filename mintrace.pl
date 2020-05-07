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

% write_env(Env, Var, Val, NEnv) set the binding of variable Var in an
% environment Env to value Val and return a new environment NEnv.
:- det(write_env/3).
write_env([], X, V, [X/V]).
write_env([Name/_ | Rest], Name, Value, [Name/Value | Rest]) :- !.
write_env([Pair | Rest], Name, Value, [Pair | NewRest]) :- write_env(Rest, Name, Value, NewRest).

% resolve(Arg, Env, Val) turn an argument Arg (which can be either a variable
% or a constant) into a value Val, either by just unwrapping a constant or by
% doing a lookup in the environment.
:- det(resolve/3).
resolve(const(X), _, X).
resolve(var(X), Env, Y) :- lookup(X, Env, Y).

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
check_syntax_interp(Labels) :-
    check_syntax_interp(Labels, Labels).
:- det(check_syntax_interp/2).
check_syntax_interp([], _).
check_syntax_interp([Name/Op | Rest], AllLabels) :-
    atom(Name),
    check_syntax_interp_op(Op, AllLabels),
    check_syntax_interp(Rest, AllLabels).

check_syntax_interp_op(op(Res, Op, Arg1, Arg2, Rest), Labels) :-
    atom(Res), member(Op, [mul, add, sub, ge, eq, assign, readlist]),
    check_syntax_interp_arg(Arg1),
    check_syntax_interp_arg(Arg2),
    check_syntax_interp_op(Rest, Labels).

check_syntax_interp_op(new(Res, Shape, Rest), Labels) :-
    atom(Res),
    atom(Shape),
    check_syntax_interp_op(Rest, Labels).

check_syntax_interp_op(set(Arg, Field, ArgValue, Rest), Labels) :-
    check_syntax_interp_arg(Arg),
    check_syntax_interp_arg(ArgValue),
    atom(Field),
    check_syntax_interp_op(Rest, Labels).

check_syntax_interp_op(get(Res, Arg, Field, Rest), Labels) :-
    atom(Res),
    check_syntax_interp_arg(Arg),
    atom(Field),
    check_syntax_interp_op(Rest, Labels).

check_syntax_interp_op(if_class(Arg, Shape, L1, L2), Labels) :-
    atom(Shape),
    check_syntax_interp_arg(Arg),
    check_label_exists(L1, Labels),
    check_label_exists(L2, Labels).

check_syntax_interp_op(promote(Arg, L1), Labels) :-
    check_syntax_interp_arg(Arg),
    check_label_exists(L1, Labels).

check_syntax_interp_op(if(Arg, L1, L2), Labels) :-
    check_syntax_interp_arg(Arg),
    check_label_exists(L1, Labels),
    check_label_exists(L2, Labels).

check_syntax_interp_op(jump(L), Labels) :-
    check_label_exists(L, Labels).

check_syntax_interp_op(return(Arg), _) :-
    check_syntax_interp_arg(Arg).

check_syntax_interp_arg(var(Name)) :- atom(Name).
check_syntax_interp_arg(const(_)).

check_label_exists(L, Labels) :-
    lookup(L, Labels, _).

interp_label(Label, Labels, Env, Res) :-
    interp_label(Label, Labels, Env, [], Res).

interp_label(Label, Labels, Env, Heap, Res) :-
    lookup(Label, Labels, Op),
    interp(Op, Labels, Env, Heap, Res).

% interp(Code, Labels, Env, Res) executes flow graph program Code in environment Env
:- det(interp/4).
interp(op(ResultVar, Op, Arg1, Arg2, NextOp), Labels, Env, Heap, Res) :-
    interp_op(ResultVar, Op, Arg1, Arg2, Env, NEnv),
    interp(NextOp, Labels, NEnv, Heap, Res).

interp(promote(_, L), Labels, Env, Heap, Res) :-
    lookup(L, Labels, Code),
    interp(Code, Labels, Env, Heap, Res).

interp(jump(L), Labels, Env, Heap, Res) :-
    lookup(L, Labels, Code),
    interp(Code, Labels, Env, Heap, Res).

interp(if(Arg, L1, L2), Labels, Env, Heap, Res) :-
    resolve(Arg, Env, RArg),
    (RArg == 0 ->
        L = L2
    ;
        L = L1
    ),
    lookup(L, Labels, Code),
    interp(Code, Labels, Env, Heap, Res).

interp(return(Arg), _, Env, _, Val) :-
    resolve(Arg, Env, Val),
    print(Val), nl.

interp(new(ResultVar, Class, NextOp), Labels, Env, Heap, Res) :-
    new_object(Class, Heap, NHeap, NewObj),
    write_env(Env, ResultVar, NewObj, NEnv),
    interp(NextOp, Labels, NEnv, NHeap, Res).

interp(get(ResultVar, Arg, Field, NextOp), Labels, Env, Heap, Res) :-
    resolve(Arg, Env, RArg),
    get_object(RArg, Heap, Obj),
    get_field(Obj, Field, Value),
    write_env(Env, ResultVar, Value, NEnv),
    interp(NextOp, Labels, NEnv, Heap, Res).

interp(set(Arg, Field, ValueArg, NextOp), Labels, Env, Heap, Res) :-
    resolve(Arg, Env, Address),
    resolve(ValueArg, Env, Value),
    set_field(Address, Field, Value, Heap, NHeap),
    interp(NextOp, Labels, Env, NHeap, Res).

interp(if_class(Arg, Cls, L1, L2), Labels, Env, Heap, Res) :-
    resolve(Arg, Env, RArg),
    get_object(RArg, Heap, obj(Cls1, _)),
    (Cls == Cls1 ->
        L = L1
    ;
        L = L2
    ),
    lookup(L, Labels, Code),
    interp(Code, Labels, Env, Heap, Res).


interp_op(ResultVar, Op, Arg1, Arg2, Env, NEnv) :-
    resolve(Arg1, Env, RArg1),
    resolve(Arg2, Env, RArg2),
    do_op(Op, RArg1, RArg2, Res),
    write_env(Env, ResultVar, Res, NEnv).

% heap manipulation

new_object(Class, Heap, [NewObj/obj(Class, [])|Heap], NewObj) :-
    gensym(Class, NewObj). % invent address

get_object(Address, Heap, Object) :-
    lookup(Address, Heap, Object).

get_field(obj(_, Fields), Field, Value) :-
    lookup(Field, Fields, Value).

set_field(Address, Field, Value, Heap, NHeap) :-
    lookup(Address, Heap, obj(Cls, Fields)),
    write_env(Fields, Field, Value, NFields),
    write_env(Heap, Address, obj(Cls, NFields), NHeap).



% _______________ simple tracer _______________

% do_trace(Label, Env) start tracing of code at label Label with environment Env
do_trace(L, Labels, Env, Res) :-
    do_trace(L, Labels, Env, [], Res).
do_trace(L, Labels, Env, Heap, Res) :-
    lookup(L, Labels, StartCode),
    trace(StartCode, Labels, Env, Heap, ProducedTrace, traceanchor(L, ProducedTrace), Res).

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
check_syntax_trace(loop, _).

% trace(Code, Labels, Env, Trace, TraceAnchor) trace the code Code in environment Env
% yielding trace Trace. The TraceAnchor contains information about where to end
% tracing and the full trace.
trace(op(ResultVar, Op, Arg1, Arg2, Rest), Labels, Env, Heap,
      op(ResultVar, Op, Arg1, Arg2, T), TraceAnchor, Res) :-
    interp_op(ResultVar, Op, Arg1, Arg2, Env, NEnv),
    trace(Rest, Labels, NEnv, Heap, T, TraceAnchor, Res).

trace(promote(Arg, L), Labels, Env, Heap, guard(Arg, Val, L, T), TraceAnchor, Res) :-
    resolve(Arg, Env, Val),
    trace_jump(L, Labels, Env, Heap, T, TraceAnchor, Res).

trace(return(V), _, Env, _,
      return(V), _, Val) :-
    resolve(V, Env, Val),
    print(Val), nl.

trace(jump(L), Labels, Env, Heap, T, TraceAnchor, Res) :-
    trace_jump(L, Labels, Env, Heap, T, TraceAnchor, Res).

trace(if(Arg, L1, L2), Labels, Env, Heap, guard(Arg, Val, OL, T), TraceAnchor, Res) :-
    resolve(Arg, Env, Val),
    (Val == 0 ->
        L = L2, OL = L1
    ;
        ensure(Val == 1),
        L = L1, OL = L2
    ),
    trace_jump(L, Labels, Env, Heap, T, TraceAnchor, Res).

trace(new(ResultVar, Class, NextOp), Labels, Env, Heap, new(ResultVar, Class, T), TraceAnchor, Res) :-
    new_object(Class, Heap, NHeap, NewObj),
    write_env(Env, ResultVar, NewObj, NEnv),
    trace(NextOp, Labels, NEnv, NHeap, T, TraceAnchor, Res).

trace(get(ResultVar, Arg, Field, NextOp), Labels, Env, Heap, get(ResultVar, Arg, Field, T), TraceAnchor, Res) :-
    resolve(Arg, Env, RArg),
    get_object(RArg, Heap, Obj),
    get_field(Obj, Field, Value),
    write_env(Env, ResultVar, Value, NEnv),
    trace(NextOp, Labels, NEnv, Heap, T, TraceAnchor, Res).

trace(set(Arg, Field, ValueArg, NextOp), Labels, Env, Heap, set(Arg, Field, ValueArg, T), TraceAnchor, Res) :-
    resolve(Arg, Env, Address),
    resolve(ValueArg, Env, Value),
    set_field(Address, Field, Value, Heap, NHeap),
    trace(NextOp, Labels, Env, NHeap, T, TraceAnchor, Res).

trace(if_class(Arg, Cls, L1, L2), Labels, Env, Heap, guard_class(Arg, Cls, OL, T), TraceAnchor, Res) :-
    resolve(Arg, Env, RArg),
    get_object(RArg, Heap, obj(Cls1, _)),
    (Cls == Cls1 ->
        L = L1, OL = L2
    ;
        L = L2, OL = L1
    ),
    trace_jump(L, Labels, Env, Heap, T, TraceAnchor, Res).


trace_jump(L, Labels, Env, Heap, loop, traceanchor(L, FullTrace), Res) :-
    !, % prevent more tracing
    write(trace), nl, write_trace(FullTrace), nl, % --
    trace,
    check_syntax_trace(FullTrace, Labels),
    do_optimize(FullTrace, Labels, Env, OptTrace),
    write(opttrace), nl, write_trace(OptTrace), nl, % --
    runtrace_opt(OptTrace, Labels, Env, Heap, OptTrace, Res).

trace_jump(L, Labels, Env, Heap, T, TraceAnchor, Res) :-
    lookup(L, Labels, Code),
    trace(Code, Labels, Env, Heap, T, TraceAnchor, Res).


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


% runtrace_opt(Trace, Labels, Env, Heap, TraceFromStart) execute a trace Trace in environment Env
% with the full trace being also given as argument TraceFromStart
runtrace_opt(op(ResultVar, Op, Arg1, Arg2, Rest), Labels, Env, Heap, TraceFromStart, Res) :-
    interp_op(ResultVar, Op, Arg1, Arg2, Env, NEnv),
    runtrace_opt(Rest, Labels, NEnv, Heap, TraceFromStart, Res).

runtrace_opt(guard(Arg, C, SSAEnv, L, Rest), Labels, Env, Heap, TraceFromStart, Res) :-
    resolve(Arg, Env, Val),
    (Val == C ->
        runtrace_opt(Rest, Labels, Env, Heap, TraceFromStart, Res)
    ;
        execute_phi(SSAEnv, Env, InterpEnv),
        interp_label(L, Labels, InterpEnv, Heap, Res)
    ).

runtrace_opt(loop(Renames), Labels, Env, Heap, TraceFromStart, Res) :-
    execute_phi(Renames, Env, NewEnv),
    runtrace_opt(TraceFromStart, Labels, NewEnv, Heap, TraceFromStart, Res).

execute_phi([], _, []).
execute_phi([Var/Val | T], Env, [Var/NVal | T1]) :-
    (Val = const(C) ->
        NVal = C
    ;
        Val = var(IVar),
        lookup(IVar, Env, NVal)
    ),
    execute_phi(T, Env, T1).

% _______________ optimization _______________
%
% do_optimize(Trace, Labels, Env, OptimizedTrace) optimize a trace Trace, returning
% OptimizedTrace
do_optimize(Trace, Labels, Env, OptimizedTrace) :-
    initialize_ssa_env(Env, SSAEnv, DefinedVars),
    optimize(Trace, SSAEnv, [], DefinedVars, OptimizedTrace).

invent_new_var(Var, NewVar) :- gensym(Var, NewVar).

initialize_ssa_env([], [], []).
initialize_ssa_env([Var/_ | Rest1], [Var/var(Var) | Rest2], [Var | Rest3]) :-
    initialize_ssa_env(Rest1, Rest2, Rest3).

sresolve(const(X), _, const(X)).
sresolve(var(V), PEnv, X) :- lookup(V, PEnv, X).

generate_phi_nodes([], _, []).
generate_phi_nodes([Var | Rest], SSAEnv, [Var/Val | Rest2]) :-
    lookup(Var, SSAEnv, Val),
    generate_phi_nodes(Rest, SSAEnv, Rest2).


% optimize(Trace, SSAEnv, DefinedVars, NewTrace) optimize trace Trace under SSA-environment SSAEnv

:- det(optimize/5).
optimize(op(ResultVar, Op, Arg1, Arg2, Rest), SSAEnv, AbsHeap, DefinedVars, NewTrace) :-
    sresolve(Arg1, SSAEnv, RArg1),
    sresolve(Arg2, SSAEnv, RArg2),
    (RArg1 = const(C1), RArg2 = const(C2) ->
        do_op(Op, C1, C2, Res),
        write_env(SSAEnv, ResultVar, const(Res), NEnv),
        NewTrace = RestTrace
    ;
        invent_new_var(ResultVar, Res),
        write_env(SSAEnv, ResultVar, var(Res), NEnv),
        NewTrace = op(Res, Op, RArg1, RArg2, RestTrace)
    ),
    optimize(Rest, NEnv, AbsHeap, DefinedVars, RestTrace).

optimize(loop, SSAEnv, AbsHeap, DefinedVars, Trace) :-
    trace,
    phis_and_escapes(DefinedVars, SSAEnv, AbsHeap, PhiNodes, Trace, loop(PhiNodes)).

phis_and_escapes([], _, _, [], Trace, Trace).
phis_and_escapes([Var | Rest], SSAEnv, AbsHeap, [Var/Val | Rest2], Trace, EndTrace) :-
    lookup(Var, SSAEnv, Val),
    escape(Val, AbsHeap, NHeap, Trace, NewTrace),
    phis_and_escapes(Rest, SSAEnv, NHeap, Rest2, NewTrace, EndTrace).


optimize(guard(Arg, C, L, Rest), SSAEnv, AbsHeap, DefinedVars, NewTrace) :-
    sresolve(Arg, SSAEnv, Val),
    (Val = const(C1) ->
        ensure(C1 = C), % -- otherwise the loop is invalid
        NEnv = SSAEnv,
        NewTrace = RestTrace
    ;
        Arg = var(OrigVar),
        Val = var(SSAVar),
        write_env(SSAEnv, OrigVar, const(C), NEnv),
        generate_phi_nodes(DefinedVars, SSAEnv, PhiNodes),
        NewTrace = guard(Val, C, PhiNodes, L, RestTrace)
    ),
    optimize(Rest, NEnv, AbsHeap, DefinedVars, RestTrace).

% abstract heap maps SSAVar -> obj(Cls, Fields)
% Fields are var(SSAVar) or const(...)
optimize(new(Var, Class, Rest), SSAEnv, AbsHeap, DefinedVars, NewTrace) :-
    new_object(Class, AbsHeap, NHeap, NewObj),
    write_env(SSAEnv, Var, var(NewObj), NEnv),
    optimize(Rest, NEnv, NHeap, DefinedVars, NewTrace).

maybe_get_object(_, [], not_virtual).
maybe_get_object(Address, [Address/Value | _], Value) :- !.
maybe_get_object(Address, [_ | Rest], Value) :- maybe_get_object(Address, Rest, Value).

optimize(get(Var, Arg, Field, Rest), SSAEnv, AbsHeap, DefinedVars, NewTrace) :-
    sresolve(Arg, SSAEnv, RArg),
    ensure(RArg = var(Address)),
    maybe_get_object(Address, AbsHeap, Obj),
    (Obj = obj(_, _) ->
        get_field(Obj, Field, Value),
        write_env(SSAEnv, Var, Value, NEnv),
        NewTrace = RestTrace
    ;
        ensure(Obj == not_virtual),
        invent_new_var(Var, Res),
        write_env(SSAEnv, Var, var(Res), NEnv),
        NewTrace = get(Res, RArg, Field, RestTrace)
    ),
    optimize(Rest, NEnv, AbsHeap, DefinedVars, RestTrace).

optimize(set(Arg, Field, ValueArg, Rest), SSAEnv, AbsHeap, DefinedVars, NewTrace) :-
    sresolve(Arg, SSAEnv, RArg),
    ensure(RArg = var(Address)),
    sresolve(ValueArg, SSAEnv, RValueArg),
    maybe_get_object(Address, AbsHeap, Obj),
    (Obj = obj(_, _) ->
        set_field(Address, Field, RValueArg, AbsHeap, NHeap),
        NewTrace = RestTrace,
        NEnv = SSAEnv
    ;
        escape(RValueArg, AbsHeap, NHeap, NewTrace, NewTrace2),
        NewTrace2 = set(RArg, Field, RValueArg, RestTrace)
    ),
    optimize(Rest, NEnv, NHeap, DefinedVars, RestTrace).

optimize(guard_class(Arg, Class, L, Rest), SSAEnv, AbsHeap, DefinedVars, NewTrace) :-
    sresolve(Arg, SSAEnv, RArg),
    ensure(RArg = var(Address)),
    maybe_get_object(Address, AbsHeap, Obj),
    (Obj = obj(Class1, _), Class = Class1 ->
        NewTrace = RestTrace
    ;
        escape(RArg, AbsHeap, NHeap, NewTrace, NewTrace2),
        generate_phi_nodes(DefinedVars, SSAEnv, PhiNodes),
        NewTrace2 = guard_class(RArg, Class, PhiNodes, L, RestTrace)
    ),
    optimize(Rest, SSAEnv, NHeap, DefinedVars, RestTrace).

escape(const(_), Heap, Heap, Trace, Trace) :- !.
escape(var(X), AbsHeap, NHeap, Trace, NewTrace) :-
    maybe_get_object(X, AbsHeap, Obj),
    (Obj = obj(Cls, Fields) ->
        trace,
        Trace = new(X, Cls, Trace2),
        remove_from_env(X, AbsHeap, AbsHeap1),
        escape_fields(Fields, X, AbsHeap1, NHeap, Trace2, NewTrace)
    ;
        NHeap = AbsHeap, Trace = NewTrace
    ).

remove_from_env(_, [], []).
remove_from_env(X, [X/_ | T], T) :- !.
remove_from_env(X, [A/B | T1], [A/B | T2]) :-
    remove_from_env(X, T1, T2).

escape_fields([], _, AbsHeap, AbsHeap, Trace, Trace).
escape_fields([FieldName/Value | RestFields], X, AbsHeap, NHeap, Trace, NewTrace) :-
    escape(Value, AbsHeap, AbsHeap1, Trace, set(var(X), FieldName, Value, Trace1)),
    escape_fields(RestFields, X, AbsHeap1, NHeap, Trace1, NewTrace).


% _______________ example programs _______________


% power computes x ** y

program(power, [power/
                    op(res, assign, const(1), const(0),
                    op(c, ge, var(y), const(1),
                    if(var(c), power_rec, power_done))),
                power_rec/
                    op(res, mul, var(res), var(x),
                    op(y, sub, var(y), const(1),
                    op(c, ge, var(y), const(1),
                    if(var(c), power_rec, power_done)))),
                power_done/
                    return(var(res))]).

% promotion example
% while i >= 0
%    i -= promote(x) * 2 + 1

program(loop, [
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
        jump(l))))]).

% arithmetic example
% while i >= 0
%    i -= x * 2 + 1

program(boxedloop, [
    start/
        new(i, int,
        set(var(i), value, var(startval),
        new(x, int,
        set(var(x), value, var(xval),
        jump(l))))),
    l/
        if_class(var(i), int, l_ge, error),
    l_ge/
        get(ival, var(i), value,
        op(c, ge, var(ival), const(0),
        if(var(c), b, l_done))),
    l_done/
        get(ival, var(i), value,
        return(var(ival))),
    b/
        if_class(var(x), int, b_mul, error),
    b_mul/
        get(xval, var(x), value,
        op(x2val, mul, var(xval), const(2),
        new(x2, int,
        set(var(x2), value, var(x2val),
        if_class(var(x2), int, b_add, error))))),
    b_add/
        get(x2val, var(x2), value,
        op(x2val, add, var(x2val), const(1),
        new(x2, int,
        set(var(x2), value, var(x2val),
        if_class(var(x2), int, b_sub, error))))),
    b_sub/
        if_class(var(i), int, b_sub2, error),
    b_sub2/
        get(x2val, var(x2), value,
        get(ival, var(i), value,
        op(ival, sub, var(ival), var(x2val),
        new(i, int,
        set(var(i), value, var(ival),
        jump(l)))))),
    error/
        return(const(-1000))
]).

run_boxedloop(X, Res) :-
    program(boxedloop, Code),
    interp_label(l, Code, [startval/X, xval/3], Res).

trace_boxedloop(X, Res) :-
    program(boxedloop, Code),
    do_trace(l, Code, [startval/X, xval/3, i/i, x/x],  [i/obj(int, [value/X]), x/obj(int, [value/3])], Res).

% bytecode interpreter

program(bytecode_interpreter, [
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
        return(var(a))]).

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
    program(power, Code),
    interp_label(power, Code, [x/X, y/Y], Res).

trace_power(X, Y, Res) :-
    program(power, Code),
    do_trace(power_rec, Code, [x/X, y/Y, res/1], Res).

power_pe(X, Y) :-
    do_pe(power, [y/Y], Label),
    block(Label, Code),
    interp(Code, [x/X]).

loop(X, Res) :-
    program(loop, Code),
    interp_label(b, Code, [i/X, x/3], Res).

trace_loop(X, Res) :-
    program(loop, Code),
    do_trace(b, Code, [i/X, x/3], Res).


run_interp(A, Res) :-
    bytecode_square(B),
    Env = [bytecode/B, pc/0, a/A, r0/0, r1/0, r2/0],
    program(bytecode_interpreter, Code),
    interp_label(bytecode_loop, Code, Env, Res).

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

test(check_power) :-
    program(power, P),
    check_syntax_interp(P).

test(power, true(Res = 1024)) :-
    power(2, 10, Res).

test(check_loop) :-
    program(loop, P),
    check_syntax_interp(P).

test(check_boxed_loop, true(Res = -5)) :-
    program(boxedloop, P),
    check_syntax_interp(P).

test(loop, true(Res = -5)) :-
    loop(100, Res).

test(check_interp) :-
    program(bytecode_interpreter, P),
    check_syntax_interp(P).

test(interp, true(Res = 256)) :-
    run_interp(16, Res).

test(boxedloop) :-
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


test(execute_phi, true(Res = [i/ -1, x/3, x2/6, x3/7, c/0])) :-
    execute_phi([i/var(i2), x/const(3), x2/const(6), x3/const(7), c/var(c2)], [i/6, x/3, x2/6, x3/7, c/1, i2/ -1, c2/0], Res).

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

%test(trace_loop, true(Res = -5)) :-
%    trace_loop(100, Res).

test(trace_newsetguardget, true(Res = 5)) :-
    Labels = [
    start/
        new(x, int,
        set(var(x), value, const(5),
        if_class(var(x), int, b, e))),
    b/
        get(y, var(x), value,
        return(var(y))),
    e/
        return(const(-5))],
    do_trace(start, Labels, [], Res).

test(optimize_newsetguardget) :-
    Trace = 
        new(x, int,
        set(var(x), value, var(i),
        get(i, var(x), value,
        loop))),
    trace,
    optimize(Trace, [i/var(i)], [], [i], NewTrace).


test(trace_boxedloop, true(Res = -5)) :-
    trace_boxedloop(100, Res).

%test(trace_power, true(Res = 1024)) :-
%     trace_power(2, 10, Res).
%
%test(trace_interp, true(Res = 256)) :-
%    trace_interp(16, Res).
%
%test(metatrace_interp, true(Res = 256)) :-
%    metatrace_interp(16, Res).

:- end_tests(mintrace).
