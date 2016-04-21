%%===========================================================================================
%% @doc
%% Functions for generating macro and definitions (resp function definitions) that are
%% expanded (resp returned) to any element of a given type. At the moment only a subset
%% of the Erlang types are supported, but more types can be added easily.
%%
%% This module is not purely functional, as each generator tracks the function
%% and macro calls being generated, so it can subsequently return the
%% corresponding definitions.
%%
%% <strong>Important:</strong> Each code generator relies on a {@link freshname_generator}
%% that must be created before and passed to the code generator via the
%% {@link set_freshgen/2} function.
%%
%% See [http://erlang.org/doc/reference_manual/typespec.html Erlang Type and function
%% specifications] for more details.
%% @end
%%
%% @author Francisco Javier López-Fraguas <fraguas@sip.ucm.es>
%% @author Manuel Montenegro <montenegro@fdi.ucm.es>
%% @author Juan Rodríguez-Hortalá <juanrh@fdi.ucm.es>
%% @author Gorka Suárez García <gorka.suarez@ucm.es>
%% @copyright 2015
%%===========================================================================================
-module(macrocall_generator).
-author("Francisco Javier López-Fraguas").
-author("Manuel Montenegro").
-author("Juan Rodríguez-Hortalá").
-author("Gorka Suárez García").
-export([
    init/1, handle_call/3, handle_cast/2, handle_info/2, terminate/2, code_change/3,
    new/0, stop/1, gen_code/3, get_generated_code/1, set_freshgen/2
]).
-import(erl_syntax, [
    abstract/1, application/2, macro/2, variable/1, tuple/1, nil/0, integer/1, atom/1,
    function/2, clause/3, fun_expr/1, add_ann/2, attribute/2, receive_expr/1, cons/2,
    block_expr/1, match_expr/2, operator/1, infix_expr/3
]).
-behaviour(gen_server).

%%===========================================================================================
%% Types
%%===========================================================================================

-type code_gen() :: pid().

-type gen_specifier() ::
    none_closure | integer | float | number | {integer, integer()} |
    {atom, atom()} | any | alt | nil | nonempty_list | {'fun', integer()} |
    pos_integer | tuple_any | non_neg_integer | atom | string.


-type ast_expr() :: term().
-type ast_form() :: term().

%%===========================================================================================
%% Data
%%===========================================================================================

% The generator is implemented as a gen_server, whose state contains the
% fresh name generator and the list of gen_specifiers() generated so far.
-record(st, { fresh_gen :: freshname_generator:fn_gen(),
              generated :: gen_specifier()}).

%%===========================================================================================
%% Interface
%%===========================================================================================

%%-------------------------------------------------------------------------------------------
%% @doc
%% It creates a new code generator.
%%
%% <strong>Important:</strong> Each code generator relies on a {@link freshname_generator}
%% that has to be passed to the code generator via the {@link set_freshgen/2} function
%% before generating any call.
%% @spec
%% new() -> code_gen()
%% @end
%%-------------------------------------------------------------------------------------------
-spec new() -> code_gen().
new() ->
    {ok, P} = gen_server:start(?MODULE, none, []), P.

%%-------------------------------------------------------------------------------------------
%% @doc
%% It releases a code generator. The code generator given as parameter cannot be used
%% after the call.
%% @spec
%% stop(code_gen()) -> ok
%% @end
%%-------------------------------------------------------------------------------------------
-spec stop(code_gen()) -> ok.
stop(Gen) ->
    gen_server:cast(Gen, stop).

%%-------------------------------------------------------------------------------------------
%% @doc
%% It generates a macro or function call corresponding to the type specifier passed as
%% parameter. Some specifiers (such as `nonempty_list' or `fun') require some extra
%% parameters, which are assumed to have already been converted into Erlang expressions.
%% The list of these is passed as a third parameter.
%% @spec
%% gen_code(code_gen(), gen_specifier(), [ast_expr()]) -> ast_expr()
%% @end
%%-------------------------------------------------------------------------------------------
-spec gen_code(code_gen(), gen_specifier(), [ast_expr()]) -> ast_expr().
gen_code(Gen, Type, Components) ->
    gen_server:call(Gen, {gen_call, Type, Components}).

%%-------------------------------------------------------------------------------------------
%% @doc
%% It returns the definitions of macros and functions whose calls have been produced by
%% this generator.
%% @spec
%% get_generated_code(code_gen()) -> [ast_form()]
%% @end
%%-------------------------------------------------------------------------------------------
-spec get_generated_code(code_gen()) -> [ast_form()].
get_generated_code(Gen) ->
    gen_server:call(Gen, get_generated_code).

%%-------------------------------------------------------------------------------------------
%% @doc
%% Sets the fresh name generator associated with this code generator. The code generator
%% may rely in the latter when generating calls (for instance, when calling `?FUN').
%% @spec
%% set_freshgen(code_gen(), freshname_generator:fn_gen()) -> ok
%% @end
%%-------------------------------------------------------------------------------------------
-spec set_freshgen(code_gen(), freshname_generator:fn_gen()) -> ok.
set_freshgen(Gen, FGen) ->
    gen_server:cast(Gen, {set_freshgen, FGen}).

%%===========================================================================================
%% Callbacks
%%===========================================================================================

%%-------------------------------------------------------------------------------------------
%% @private
%% @doc
%% Initializes the server.
%% @end
%%-------------------------------------------------------------------------------------------
init(FNGen) ->
    {ok, #st{fresh_gen = FNGen, generated = sets:new()}}.

%%-------------------------------------------------------------------------------------------
%% @private
%% @doc
%% Handles the call messages.
%% @end
%%-------------------------------------------------------------------------------------------
handle_call({gen_call, none_closure, []}, _, St) ->
    % Returns: fun() -> 'NONE'() end
    {reply, {'fun', 0, {'function', 'NONE', 0}},
        add_to_generated(none, St)};

handle_call({gen_call, integer, []}, _, St) ->
    % Returns: 'INTEGER'()
    {reply, application(abstract('INTEGER'), []),
        add_to_generated(integer, St)};

handle_call({gen_call, float, []}, _, St) ->
    % Returns: 'FLOAT'()
    {reply, application(abstract('FLOAT'), []),
        add_to_generated(float, St)};

handle_call({gen_call, number, []}, _, St) ->
    % Returns: 'NUMBER'()
    {reply, application(abstract('NUMBER'), []),
        add_to_generated(number, St)};

handle_call({gen_call, tuple_any, []}, _, St) ->
    % Returns: 'TUPLE'()
    {reply, application(abstract('TUPLE'), []),
        add_to_generated(tuple_any, St)};

handle_call({gen_call, pos_integer, []}, _, St) ->
    % Returns: 'POS_INTEGER'()
    {reply, application(abstract('POS_INTEGER'), []),
        add_to_generated(pos_integer, St)};

handle_call({gen_call, non_neg_integer, []}, _, St) ->
    % Returns: 'NON_NEG_INTEGER'()
    {reply, application(abstract('NON_NEG_INTEGER'), []),
        add_to_generated(non_neg_integer, St)};

handle_call({gen_call, atom, []}, _, St) ->
    % Returns: 'ATOM'()
    {reply, application(abstract('ATOM'), []),
        add_to_generated(atom, St)};

handle_call({gen_call, string, []}, _, St) ->
    % Returns: 'STRING'()
    {reply, application(abstract('STRING'), []),
        add_to_generated(string, St)};

handle_call({gen_call, {integer, N}, []}, _, St) ->
    % Returns the given integer as an AST
    {reply, integer(N), St};

handle_call({gen_call, {atom, At}, []}, _, St) ->
    % Returns the given atom as an AST
    {reply, atom(At), St};

handle_call({gen_call, any, []}, _, St) ->
    % Returns 'ANY'()
    {reply, application(abstract('ANY'), []),
        add_to_generated(any, St)};

handle_call({gen_call, alt, Alts}, _, St) ->
    % Returns ?ALT(alt1, ..., altn) where Alts = [alt1,...,altn]
    {reply, lists:foldr(fun(Alt, []) -> Alt;
                           (Alt, Xs) -> macro(variable("ALT"), [Alt, Xs])
                        end, [], Alts),
        add_to_generated(alt, St)};

handle_call({gen_call, tuple, Comps}, _, St) ->
    % Returns {comp1, ..., compn} where Comps = [comp1,...,compn]
    {reply, tuple(Comps), St};


handle_call({gen_call, nil, []}, _, St) ->
    % Returns []
    {reply, nil(), St};

handle_call({gen_call, nonempty_list, [Head, Tail]}, _, St) ->
    % Returns ?NELIST(Head, Tail)
    {reply, macro(variable("NELIST"), [Head, Tail]),
        add_to_generated(nonempty_list, St)};

handle_call({gen_call, 'fun', Comps}, _, St) ->
    % Returns ?FUN(comp1, ..., compn, fv1, ..., fvm) where
    % fv1... fvm are fresh variables and m = n+1.
    Arity = length(Comps),
    {
        reply,
        macro(variable("FUN_" ++ list_utils:integer_to_string(Arity - 1)), Comps),
        add_to_generated({'fun' , Arity - 1}, St)
    };

handle_call({gen_call, Type, Params}, _, St) ->
    % Unknown type specifier. We return 'ANY'().
    io:format("Not recognized: ~p ~p~n", [Type, Params]),
    {reply, application(abstract('ANY'), []), add_to_generated(any, St)};

handle_call(get_generated_code, _, #st{generated = Gen} = St) ->
    ListGens = sets:to_list(Gen),
    Forms = lists:append([generate_code_for(G) || G <- ListGens]),
    {reply, Forms, St}.

%%-------------------------------------------------------------------------------------------
%% @private
%% @doc
%% Handles the cast messages.
%% @end
%%-------------------------------------------------------------------------------------------
handle_cast({set_freshgen, FGen}, St) ->
    {noreply, St#st{fresh_gen = FGen}};
handle_cast(stop, State) ->
    {stop, normal, State};
handle_cast(Request, State) ->
    io:format("Freshname generator: asynchronous request ~p~n", [Request]),
    {noreply, State}.

%%-------------------------------------------------------------------------------------------
%% @private
%% @doc
%% Handles all the non call/cast messages.
%% @end
%%-------------------------------------------------------------------------------------------
handle_info(Info, State) ->
    io:format("Freshname generator: unexpected message ~p~n", [Info]),
    {noreply, State}.

%%-------------------------------------------------------------------------------------------
%% @private
%% @doc
%% This is called by a gen_server when it is about to terminate. It should be the
%% opposite of Module:init/1 and do any necessary cleaning up. When it returns, the
%% gen_server terminates with Reason. The return value is ignored.
%% @end
%%-------------------------------------------------------------------------------------------
terminate(_, _) -> ok.

%%-------------------------------------------------------------------------------------------
%% @private
%% @doc
%% Converts the process state when the code is changed.
%% @end
%%-------------------------------------------------------------------------------------------
code_change(_, _, State) -> {ok, State}.

%%===========================================================================================
%% Private
%%===========================================================================================

%%-------------------------------------------------------------------------------------------
%% @private
%% @doc
%% Adds to the state a generated element.
%% @end
%%-------------------------------------------------------------------------------------------
-spec add_to_generated(gen_specifier(), #st{}) -> #st{}.
add_to_generated(Elem, #st{generated = Gen} = St) ->
    St#st{generated = sets:add_element(Elem, Gen)}.

%%-------------------------------------------------------------------------------------------
%% @private
%% @doc
%% Generates a function without parameters specification.
%% @end
%%-------------------------------------------------------------------------------------------
gen_add_ann(Name, Type, Number) ->
    GenType = fun(T, P) -> {type, Number, T, P} end,
    SpecBody = GenType('fun', [GenType(product, []), GenType(Type, [])]),
    SpecAbst = abstract({{Name, 0}, [SpecBody]}),
    add_ann(typespec, attribute(spec, [SpecAbst])).

%%-------------------------------------------------------------------------------------------
%% @private
%% @doc
%% Generates a function without parameters.
%% @end
%%-------------------------------------------------------------------------------------------
gen_func(Name, Body) ->
    function(abstract(Name), [clause([], none, Body)]).

%%-------------------------------------------------------------------------------------------
%% @private
%% @doc
%% Generates a receive with only one clause.
%% @end
%%-------------------------------------------------------------------------------------------
gen_recv() ->
    VX = variable("X"),
    receive_expr([clause([VX], none, [VX])]).

%%-------------------------------------------------------------------------------------------
%% @private
%% @doc
%% Generates a receive with only one clause.
%% @end
%%-------------------------------------------------------------------------------------------
gen_recv(P) when is_atom(P) ->
    VX = variable("X"),
    receive_expr([clause([VX], [application(abstract(P), [VX])], [VX])]);
gen_recv({P, OP, N}) when is_atom(P) ->
    VX = variable("X"),
    receive_expr([clause([VX], [application(abstract(P), [VX]),
        infix_expr(VX, operator(OP), abstract(N))], [VX])]).

%%-------------------------------------------------------------------------------------------
%% @private
%% @doc
%% Generates a function code to return some type of value.
%% @end
%%-------------------------------------------------------------------------------------------
generate_code_for(none) ->
    % -spec 'NONE'() -> none().
    % 'NONE'() -> fun (0) -> 0 end(1).
    [
        gen_add_ann('NONE', none, 0),
        gen_func('NONE', [application(fun_expr([clause([abstract(0)], none,
            [abstract(0)])]), [abstract(1)])])
    ];

generate_code_for(integer) ->
    % -spec 'INTEGER'() -> integer().
    % 'INTEGER'() -> receive X when is_integer(X) -> X end.
    [
        gen_add_ann('INTEGER', integer, 0),
        gen_func('INTEGER', [gen_recv(is_integer)])
    ];

generate_code_for(float) ->
    % -spec 'FLOAT'() -> float().
    % 'FLOAT'() -> receive X when is_float(X) -> X end.
    [
        gen_add_ann('FLOAT', float, 0),
        gen_func('FLOAT', [gen_recv(is_float)])
    ];

generate_code_for(number) ->
    % -spec 'NUMBER'() -> number().
    % 'NUMBER'() -> receive X when is_number(X) -> X end.
    [
        gen_add_ann('NUMBER', number, 0),
        gen_func('NUMBER', [gen_recv(is_number)])
    ];

generate_code_for(pos_integer) ->
    % -spec 'POS_INTEGER'() -> pos_integer().
    % 'POS_INTEGER'() -> receive X when is_integer(X), X >= 1 -> X end.
    [
        gen_add_ann('POS_INTEGER', pos_integer, 0),
        gen_func('POS_INTEGER', [gen_recv({is_number, ">=", 1})])
    ];

generate_code_for(non_neg_integer) ->
    % -spec 'NON_NEG_INTEGER'() -> non_neg_integer().
    % 'POS_INTEGER'() -> receive X when is_integer(X), X >= 0 -> X end.
    [
        gen_add_ann('NON_NEG_INTEGER', non_neg_integer, 0),
        gen_func('NON_NEG_INTEGER', [gen_recv({is_number, ">=", 0})])
    ];

generate_code_for(tuple_any) ->
    % -spec 'TUPLE'() -> tuple().
    % 'TUPLE'() -> receive X when is_tuple(X) -> X end.
    [
        gen_add_ann('TUPLE', tuple, 0),
        gen_func('TUPLE', [gen_recv(is_tuple)])
    ];

generate_code_for(atom) ->
    % -spec 'ATOM'() -> atom().
    % 'ATOM'() -> receive X when is_atom(X) -> X end.
    [
        gen_add_ann('ATOM', atom, 0),
        gen_func('ATOM', [gen_recv(is_atom)])
    ];

generate_code_for(string) ->
    % -spec 'STRING'() -> string().
    % 'STRING'() -> atom_to_list(X).
    [
        gen_add_ann('STRING', string, 0),
        gen_func('STRING', [application(abstract(atom_to_list), [abstract(a)])])
    ];

generate_code_for(any) ->
    % -spec 'ANY'() -> any().
    % 'ANY'() -> receive X -> X end.
    [
        gen_add_ann('ANY', any, 0),
        gen_func('ANY', [gen_recv()])
    ];

generate_code_for(alt) ->
    %-define(ALT(X1, X2),
    %   receive
    %     0 -> X1;
    %     1 -> X2
    %   end).
    [
        attribute(abstract(define), [
            application(variable("ALT"), [variable("X1"), variable("X2")]),
            receive_expr([
                clause([abstract(0)], none, [variable("X1")]),
                clause([abstract(1)], none, [variable("X2")])
            ])
        ])
    ];

generate_code_for(nonempty_list) ->
    % -define(NELIST(H, T), [H | T]).
    [
        attribute(abstract(define), [
            application(variable("NELIST"), [variable("H"), variable("T")]),
            cons(variable("H"), variable("T"))
        ])
    ];

generate_code_for({'fun', N}) ->
    % -define(FUN_1(X_1, Res, Y_1, Y_Res, F),
    %   begin
    %     Y_1 = X_1,
    %     Y_Res = Res,
    %     F = fun (Z_1) when Z_1 =:= Y_1 -> Res end,
    %     Y_Res = F(Y_1),
    %     F
    %   end).
    %
    % -define(FUN_2(X_1, X_2, Res, Y_1, Y_2, Y_Res, F),
    %   begin
    %     Y_1 = X_1,
    %     Y_2 = X_2,
    %     Y_Res = Res,
    %     F = fun (Z_1) when Z_1 =:= Y_1, Z_2 =:= Y_2 -> Res end,
    %     Y_Res = F(Y_1, Y_2),
    %     F
    %   end).
    %
    %   etc.
    MkVars = fun(Prefix) ->
        [variable(Prefix ++ list_utils:integer_to_string(I)) || I <- lists:seq(1, N)]
    end,
    Xs = MkVars("X_"),
    Res = variable("Res"),
    Ys = MkVars("Y_"),
    YRes = variable("Y_Res"),
    Zs = MkVars("Z_"),
    F = variable("F"),
    [
        attribute(abstract(define), [
            application(
                variable("FUN_" ++ list_utils:integer_to_string(N)),
                Xs ++ [Res]
            ),
            block_expr(
                lists:zipwith(fun erl_syntax:match_expr/2, Ys, Xs) ++
                [match_expr(YRes, Res)] ++
                [match_expr(F, fun_expr([clause(
                    Zs,
                    lists:zipwith(
                        fun(Z,Y) ->
                            infix_expr(Z, operator("=:="), Y)
                        end, Zs, Ys
                    ),
                    [Res]
                )]))] ++
                [match_expr(YRes, application(F, Ys))] ++
                [F]
            )
        ])
    ];

generate_code_for(_) ->
    [].
