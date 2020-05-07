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

:- det(check_syntax_interp_op/2).
check_syntax_interp_op(op(Res, Op, Arg1, Arg2, Rest), Labels) :-
    atom(Res), member(Op, [mul, add, sub, ge, eq, assign, readlist]),
    check_syntax_interp_arg(Arg1),
    check_syntax_interp_arg(Arg2),
    check_syntax_interp_op(Rest, Labels).

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
    lookup(Label, Labels, Op),
    interp(Op, Labels, Env, Res).

% interp(Code, Labels, Env, Res) executes flow graph program Code in environment Env
:- det(interp/4).
interp(op(ResultVar, Op, Arg1, Arg2, NextOp), Labels, Env, Res) :-
    interp_op(ResultVar, Op, Arg1, Arg2, Env, NEnv),
    interp(NextOp, Labels, NEnv, Res).

interp(promote(_, L), Labels, Env, Res) :-
    lookup(L, Labels, Code),
    interp(Code, Labels, Env, Res).

interp(jump(L), Labels, Env, Res) :-
    lookup(L, Labels, Code),
    interp(Code, Labels, Env, Res).

interp(if(Arg, L1, L2), Labels, Env, Res) :-
    resolve(Arg, Env, RArg),
    (RArg == 0 ->
        L = L2
    ;
        L = L1
    ),
    lookup(L, Labels, Code),
    interp(Code, Labels, Env, Res).

interp(return(Arg), _, Env, Val) :-
    resolve(Arg, Env, Val),
    print(Val), nl.

interp_op(ResultVar, Op, Arg1, Arg2, Env, NEnv) :-
    resolve(Arg1, Env, RArg1),
    resolve(Arg2, Env, RArg2),
    do_op(Op, RArg1, RArg2, Res),
    write_env(Env, ResultVar, Res, NEnv).


% _______________ simple tracer _______________

% do_trace(Label, Env) start tracing of code at label Label with environment Env
do_trace(L, Labels, Env, Res) :-
    lookup(L, Labels, StartCode),
    trace(StartCode, Labels, Env, ProducedTrace, traceanchor(L, ProducedTrace), Res).

check_syntax_trace(op(_, _, _, _, T), Labels) :-
    check_syntax_trace(T, Labels).
check_syntax_trace(guard(_, _, L, T), Labels) :-
    lookup(L, Labels, _),
    check_syntax_trace(T, Labels).
check_syntax_trace(loop, _).

% trace(Code, Labels, Env, Trace, TraceAnchor) trace the code Code in environment Env
% yielding trace Trace. The TraceAnchor contains information about where to end
% tracing and the full trace.
trace(op(ResultVar, Op, Arg1, Arg2, Rest), Labels, Env,
      op(ResultVar, Op, Arg1, Arg2, T), TraceAnchor, Res) :-
    interp_op(ResultVar, Op, Arg1, Arg2, Env, NEnv),
    trace(Rest, Labels, NEnv, T, TraceAnchor, Res).

trace(promote(Arg, L), Labels, Env, guard(Arg, Val, L, T), TraceAnchor, Res) :-
    resolve(Arg, Env, Val),
    trace_jump(L, Labels, Env, T, TraceAnchor, Res).

trace(return(V), _, Env,
      return(V), _, Val) :-
    resolve(V, Env, Val),
    print(Val), nl.

trace(jump(L), Labels, Env, T, TraceAnchor, Res) :-
    trace_jump(L, Labels, Env, T, TraceAnchor, Res).

trace(if(Arg, L1, L2), Labels, Env, guard(Arg, Val, OL, T), TraceAnchor, Res) :-
    resolve(Arg, Env, Val),
    (Val == 0 ->
        L = L2, OL = L1
    ;
        ensure(Val == 1),
        L = L1, OL = L2
    ),
    trace_jump(L, Labels, Env, T, TraceAnchor, Res).

trace_jump(L, Labels, Env, loop, traceanchor(L, FullTrace), Res) :-
    check_syntax_trace(FullTrace, Labels),
    !, % prevent more tracing
    write(trace), nl, write_trace(FullTrace), nl, % --
    do_optimize(FullTrace, Labels, Env, OptTrace),
    write(opttrace), nl, write_trace(OptTrace), nl, % --
    runtrace_opt(OptTrace, Labels, Env, OptTrace, Res).

trace_jump(L, Labels, Env, T, TraceAnchor, Res) :-
    lookup(L, Labels, Code),
    trace(Code, Labels, Env, T, TraceAnchor, Res).


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


% runtrace_opt(Trace, Labels, Env, TraceFromStart) execute a trace Trace in environment Env
% with the full trace being also given as argument TraceFromStart
runtrace_opt(op(ResultVar, Op, Arg1, Arg2, Rest), Labels, Env, TraceFromStart, Res) :-
    interp_op(ResultVar, Op, Arg1, Arg2, Env, NEnv),
    runtrace_opt(Rest, Labels, NEnv, TraceFromStart, Res).

runtrace_opt(guard(Arg, C, SSAEnv, L, Rest), Labels, Env, TraceFromStart, Res) :-
    resolve(Arg, Env, Val),
    (Val == C ->
        runtrace_opt(Rest, Labels, Env, TraceFromStart, Res)
    ;
        execute_phi(SSAEnv, Env, InterpEnv),
        interp_label(L, Labels, InterpEnv, Res)
    ).

runtrace_opt(loop(Renames), Labels, Env, TraceFromStart, Res) :-
    execute_phi(Renames, Env, NewEnv),
    runtrace_opt(TraceFromStart, Labels, NewEnv, TraceFromStart, Res).

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
    optimize(Trace, SSAEnv, DefinedVars, OptimizedTrace).

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

:- det(optimize/4).
optimize(op(ResultVar, Op, Arg1, Arg2, Rest), SSAEnv, DefinedVars, NewTrace) :-
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
    optimize(Rest, NEnv, DefinedVars, RestTrace).

optimize(loop, SSAEnv, DefinedVars, loop(PhiNodes)) :-
    generate_phi_nodes(DefinedVars, SSAEnv, PhiNodes).

optimize(guard(Arg, C, L, Rest), SSAEnv, DefinedVars, NewTrace) :-
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
        NewTrace = guard(var(SSAVar), C, PhiNodes, L, RestTrace)
    ),
    optimize(Rest, NEnv, DefinedVars, RestTrace).


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


:- begin_tests(mintrace).

test(check_power) :-
    program(power, P),
    check_syntax_interp(P).

test(power, true(Res = 1024)) :-
    power(2, 10, Res).

test(check_loop) :-
    program(loop, P),
    check_syntax_interp(P).


test(loop, true(Res = -5)) :-
    loop(100, Res).

test(check_interp) :-
    program(bytecode_interpreter, P),
    check_syntax_interp(P).

test(interp, true(Res = 256)) :-
    run_interp(16, Res).

test(optimize) :-
    Trace = guard(var(x), 3, b2,
            op(x2, mul, var(x), const(2),
            op(x3, add, var(x2), const(1),
            op(i, sub, var(i), var(x3),
            op(c, ge, var(i), const(0),
            guard(var(c), 1, l_done, loop)))))),
    trace,
    optimize(Trace, [i/var(i), x/var(x), x2/var(x2), x3/var(x3), c/var(c)], [i, x, x2, x3, c], Res),
    Res =   guard(var(x), 3, [i/var(i), x/var(x), x2/var(x2), x3/var(x3), c/var(c)], b2,
            op(I1, sub, var(i), const(7),
            op(C1, ge, var(I1), const(0),
            guard(var(C1), 1, [i/var(I1), x/const(3), x2/const(6), x3/const(7), c/var(C1)], l_done,
            loop([i/var(I1), x/const(3), x2/const(6), x3/const(7), c/const(1)]))))).

test(optimize_guard_bug) :-
    Trace = op(pc, add, var(source), const(0),
            guard(var(pc), 1, l_done,
            op(pc, add, var(pc), const(1),
            loop))),
    optimize(Trace, [source/var(source), pc/var(pc)], [source, pc], Res),
    Res =   op(PC1, add, var(source), const(0),
            guard(var(PC1), 1, [source/var(source), pc/var(PC1)], l_done,
            loop([sourve/var(source), pc/const(2)]))).


test(execute_phi, true(Res = [i/ -1, x/3, x2/6, x3/7, c/0])) :-
    execute_phi([i/var(i2), x/const(3), x2/const(6), x3/const(7), c/var(c2)], [i/6, x/3, x2/6, x3/7, c/1, i2/ -1, c2/0], Res).

test(trace_loop, true(Res = -5)) :-
    trace_loop(100, Res).

test(trace_power, true(Res = 1024)) :-
     trace_power(2, 10, Res).

test(trace_interp, true(Res = 256)) :-
    trace_interp(16, Res).

test(metatrace_interp, true(Res = 256)) :-
    trace,
    metatrace_interp(16, Res).

:- end_tests(mintrace).
