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

% remove_env(Env, Var, NEnv) remove the binding of variable Var from an
% environment Env and return a new environment NEnv.
:- det(remove_env/3).
remove_env([], _, []).
remove_env([Name/_ | Rest], Name, Rest) :- !.
remove_env([Pair | Rest], Name, [Pair | NewRest]) :- remove_env(Rest, Name, NewRest).

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
check_syntax_interp([_/Op | Rest], AllLabels) :-
    check_syntax_interp_op(Op, AllLabels),
    check_syntax_interp(Rest, AllLabels).

:- det(check_syntax_interp_op/2).
check_syntax_interp_op(op(_, _, _, _, Rest), Labels) :-
    check_syntax_interp_op(Rest, Labels).

check_syntax_interp_op(promote(_, L1), Labels) :-
    check_label_exists(L1, Labels).

check_syntax_interp_op(if(_, L1, L2), Labels) :-
    check_label_exists(L1, Labels),
    check_label_exists(L2, Labels).

check_syntax_interp_op(return(_), _).

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
check_syntax_trace(guard(_, _, C, T), Labels) :-
    check_syntax_interp([compensation/C | Labels]),
    check_syntax_trace(T, Labels).
check_syntax_trace(loop).


% trace(Code, Labels, Env, Trace, TraceAnchor) trace the code Code in environment Env
% yielding trace Trace. The TraceAnchor contains information about where to end
% tracing and the full trace.
trace(op(ResultVar, Op, Arg1, Arg2, Rest), Labels, Env,
      op(ResultVar, Op, Arg1, Arg2, T), TraceAnchor, Res) :-
    interp_op(ResultVar, Op, Arg1, Arg2, Env, NEnv),
    trace(Rest, Labels, NEnv, T, TraceAnchor, Res).

trace(promote(Arg, L), Labels, Env, guard(Arg, Val, if(const(1), L, L), T), TraceAnchor, Res) :-
    resolve(Arg, Env, Val),
    trace_jump(L, Labels, Env, T, TraceAnchor, Res).

trace(return(V), _, Env,
      return(V), _, Val) :-
    resolve(V, Env, Val),
    print(Val), nl.

trace(if(Arg, L1, L2), Labels, Env, guard(Arg, Val, if(const(1), OL, OL), T), TraceAnchor, Res) :-
    resolve(Arg, Env, Val),
    (Val == 0 ->
        L = L2, OL = L1
    ;
        ensure(Val == 1),
        L = L1, OL = L2
    ),
    trace_jump(L, Labels, Env, T, TraceAnchor, Res).

trace_jump(L, Labels, Env, loop, traceanchor(L, FullTrace), Res) :-
    check_syntax_trace(FullTrace),
    write(trace), nl, write_trace(FullTrace), nl, % --
    do_optimize(FullTrace, Labels, Env, OptTrace),
    write(opttrace), nl, write_trace(OptTrace), nl, % --
    runtrace(OptTrace, Labels, Env, OptTrace, Res).

trace_jump(L, Labels, Env, T, TraceAnchor, Res) :-
    lookup(L, Labels, Code),
    trace(Code, Labels, Env, T, TraceAnchor, Res).


% write_trace(Trace) print trace Trace in a readable way
write_trace(loop) :- !, write('  loop'), nl.
write_trace(Op) :-
    Op =.. L,
    append(L0, [NextOp], L),
    SOp =.. L0,
    write('  '), write(SOp), nl,
    write_trace(NextOp).



% _______________ run traces _______________

% runtrace(Trace, Labels, Env, TraceFromStart) execute a trace Trace in environment Env
% with the full trace being also given as argument TraceFromStart
runtrace(op(ResultVar, Op, Arg1, Arg2, Rest), Labels, Env, TraceFromStart, Res) :-
    interp_op(ResultVar, Op, Arg1, Arg2, Env, NEnv),
    runtrace(Rest, Labels, NEnv, TraceFromStart, Res).

runtrace(guard(Arg, C, CompensationCode, Rest), Labels, Env, TraceFromStart, Res) :-
    resolve(Arg, Env, Val),
    (Val == C ->
        runtrace(Rest, Labels, Env, TraceFromStart, Res)
    ;
        interp(CompensationCode, Labels, Env, Res)
    ).

runtrace(loop, Labels, Env, TraceFromStart, Res) :-
    runtrace(TraceFromStart, Labels, Env, TraceFromStart, Res).



% _______________ optimization _______________

% generate_assignments(PEnv, Trace) generate assignments from the partial
% environment PEnv, returning Trace
generate_assignments([], LastOp, LastOp).
generate_assignments([Var/Val | Tail], LastOp, op(Var, assign, const(Val), const(0), T)) :-
    generate_assignments(Tail, LastOp, T).

% optimize(Trace, PEnv, NewTrace) optimize trace Trace under partial
% environment PEnv returning a new trace NewTrace
optimize(op(ResultVar, Op, Arg1, Arg2, Rest), PEnv, NewTrace) :-
    pe_op(ResultVar, Op, Arg1, Arg2, PEnv, NEnv, NewTrace, RestTrace),
    optimize(Rest, NEnv, RestTrace).

optimize(loop, PEnv, T) :-
    generate_assignments(PEnv, loop, T).

optimize(guard(Arg, C, CompensationCode, Rest), PEnv, NewTrace) :-
    presolve(Arg, PEnv, Val),
    (Val = const(C1) ->
        ensure(C1 = C), % --
        NewTrace = RestTrace,
        NEnv = PEnv
    ;
        Val = var(V),
        write_env(PEnv, V, C, NEnv),
        generate_assignments(PEnv, CompensationCode, NCompensationCode),
        NewTrace = guard(Arg, C, NCompensationCode, RestTrace)
    ),
    optimize(Rest, NEnv, RestTrace).


% _______________ optimization _______________

% plookup(Name, PEnv, Res) lookup a variable Name in a partial environment Env
% and return either var(Name), when the value of the variable is unknown in the
% environment, or const(Value), when it is known. The environment is a list of
% Name/Value terms.
plookup(Name, [], var(Name)).
plookup(Name, [Name/Value | _], const(Value)) :- !.
plookup(Name, [_ | Rest], Value) :- plookup(Name, Rest, Value).

% presolve(Arg, Env, Val) turn an argument Arg (which can be either a variable
% or a constant) into either var(Name), when the value of the variable is
% unknown in the environment, or const(Value), when it is known or the argument
% is a constant.
presolve(const(X), _, const(X)).
presolve(var(V), PEnv, X) :- plookup(V, PEnv, X).

pe_op(ResultVar, Op, Arg1, Arg2, PEnv, NEnv, Residual, RestResidual) :-
    presolve(Arg1, PEnv, RArg1),
    presolve(Arg2, PEnv, RArg2),
    (RArg1 = const(C1), RArg2 = const(C2) ->
        do_op(Op, C1, C2, Res),
        write_env(PEnv, ResultVar, Res, NEnv),
        RestResidual = Residual
    ;
        remove_env(PEnv, ResultVar, NEnv),
        Residual = op(ResultVar, Op, RArg1, RArg2, RestResidual)
    ).

% do_optimize(Trace, Labels, Env, OptimizedTrace) optimize a trace Trace, returning
% OptimizedTrace
do_optimize(Trace, Labels, Env, Trace).

%OptimizedTrace) :-
%    initialize_ssa_env(Env, SSAEnv),
%    ssaify(Trace, SSAEnv, SSATrace, SSAEnv),
%    optimize(SSATrace, [], OptimizedTrace).

invent_new_var(Var, NewVar) :- gensym(var, NewVar).

initialize_ssa_env([], []).
initialize_ssa_env([Var/_ | Rest1], [Var/var(Var) | Rest2]) :-
    initialize_ssa_env(Rest1, Rest2).


ssaify(op(ResultVar, Op, Arg1, Arg2, Rest), SSAEnv, op2(Res, Op, RArg1, RArg2, T), OrigEnv) :-
    presolve(Arg1, SSAEnv, RArg1),
    presolve(Arg2, SSAEnv, RArg2),
    invent_new_var(ResultVar, Res),
    write_env(SSAEnv, ResultVar, var(Res), NEnv),
    ssaify(Rest, NEnv, T, OrigEnv).

ssaify(guard(V, C, CompensationCode, Rest), SSAEnv, NewTrace, OrigEnv) :-
    ensure(ResumeVars == []),
    lookup(V, SSAEnv, Val),
    (Val == const(C) ->
        ensure(C \= 0),
        NewTrace = T
    ;
        Val = var(NV),
        NewTrace = guard_true(NV, SSAEnv, L, T)
    ),
    ssaify(Rest, SSAEnv, T, OrigEnv).

ssaify(loop, SSAEnv, NewTrace, OrigEnv) :-
    generate_assignments(OrigEnv, SSAEnv, NewTrace).


% generate_assignments(PEnv, Trace) generate assignments from the partial
% environment PEnv, returning Trace
generate_assignments([], _, loop).
generate_assignments([Var/_ | Tail], SSAEnv, T) :-
    presolve(var(Var), SSAEnv, Arg),
    (Arg == var(Var) ->
        NT = T
    ;
        T = assign(Var, Arg, NT)
    ),
    generate_assignments(Tail, SSAEnv, NT).

% optimize(Trace, PEnv, NewTrace) optimize trace Trace under partial
% environment PEnv returning a new trace NewTrace
optimize(op2(ResultVar, Op, Arg1, Arg2, Rest), PEnv, NewTrace) :-
    presolve(Arg1, PEnv, RArg1),
    presolve(Arg2, PEnv, RArg2),
    (RArg1 = const(C1), RArg2 = const(C2) ->
        do_op(Op, C1, C2, Res),
        write_env(PEnv, ResultVar, Res, NEnv),
        NewTrace = RestResidual
    ;
        remove_env(PEnv, ResultVar, NEnv),
        NewTrace = op2(ResultVar, Op, RArg1, RArg2, RestResidual)
    ),
    optimize(Rest, NEnv, RestResidual).

optimize(loop, _, loop).

optimize(guard_value(V, C, ResumeVars, L, Rest), PEnv, NewTrace) :-
    plookup(V, PEnv, Val),
    (Val = const(C1) ->
        ensure(C1 = C), % --
        NewTrace = RestResidual,
        NEnv = PEnv
    ;
        write_env(PEnv, V, C, NEnv),
        update_resumevars(ResumeVars, PEnv, NResumeVars),
        NewTrace = guard_value(V, C, NResumeVars, L, RestResidual)
    ),
    optimize(Rest, NEnv, RestResidual).

update_resumevars([], _, []).
update_resumevars([Var/Val1 | T1], PEnv, [Var/Val2 | T2]) :-
    presolve(Val1, PEnv, Val2),
    update_resumevars(T1, PEnv, T2).
% _______________ example programs _______________


% power computes x ** y

:- discontiguous power/2.

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
        if(const(1), l, l))))]).


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
          if(const(1), bytecode_loop, bytecode_loop)),
    op_mov_a_r0/
          op(r0, assign, var(a), const(0), if(const(1), bytecode_loop, bytecode_loop)),
    op_mov_a_r1/
          op(r1, assign, var(a), const(0), if(const(1), bytecode_loop, bytecode_loop)),
    op_mov_a_r2/
          op(r2, assign, var(a), const(0), if(const(1), bytecode_loop, bytecode_loop)),
    op_mov_r0_a/
          op(a, assign, var(r0), const(0), if(const(1), bytecode_loop, bytecode_loop)),
    op_mov_r1_a/
          op(a, assign, var(r1), const(0), if(const(1), bytecode_loop, bytecode_loop)),
    op_mov_r2_a/
          op(a, assign, var(r2), const(0), if(const(1), bytecode_loop, bytecode_loop)),
    op_add_r0_to_a/
          op(a, add, var(a), var(r0), if(const(1), bytecode_loop, bytecode_loop)),
    op_add_r1_to_a/
          op(a, add, var(a), var(r1), if(const(1), bytecode_loop, bytecode_loop)),
    op_add_r2_to_a/
          op(a, add, var(a), var(r2), if(const(1), bytecode_loop, bytecode_loop)),
    op_decr_a/
          op(a, sub, var(a), const(1), if(const(1), bytecode_loop, bytecode_loop)),
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

trace_loop(X) :-
    do_trace(b, [i/X, x/3]).


run_interp(A, Res) :-
    bytecode_square(B),
    Env = [bytecode/B, pc/0, a/A, r0/0, r1/0, r2/0],
    program(bytecode_interpreter, Code),
    interp_label(bytecode_loop, Code, Env, Res).

pe_interp(A) :-
    bytecode_square(B),
    Env = [bytecode/B, pc/0],
    do_pe(bytecode_loop, Env, Label),
    REnv = [a/A, r0/0, r1/0, r2/0],
    block(Label, Code),
    interp(Code, REnv).

metatrace_interp(A) :-
    bytecode_square(B),
    Env = [bytecode/B, pc/11, a/A, r0/A, r1/A, r2/0, target/2],
    do_trace(op_jump_if_a_jump, Env).

trace_interp(A) :-
    bytecode_square(B),
    Env = [bytecode/B, pc/2, a/A, r0/A, r1/A, r2/0],
    do_trace(bytecode_loop, Env).

all :-
    write('power should all give 1024 '), nl,
    write('interp: '),
    power(2, 10),
    write('trace: '),
    power_trace(2, 10),
    write('PE: '),
    power_pe(2, 10),
    nl,nl,
    write('loop should all give -5 '), nl,
    write('interp: '),
    loop(100),
    write('trace: '),
    traceloop(100),
    nl,nl,
    write('interp should all give 256 '), nl,
    write('interp: '),
    run_interp(16),
    write('trace: '),
    trace_interp(16),
    write('metatrace: '),
    metatrace_interp(16),
    write('PE: '),
    pe_interp(16).

:- begin_tests(mintrace).

test(check_power) :-
    program(power, P),
    check_syntax_interp(P).

test(power, true(Res = 1024)) :-
    power(2, 10, Res).

test(trace_power, true(Res = 1024)) :-
    trace_power(2, 10, Res).

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


:- end_tests(mintrace).
