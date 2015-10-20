
%%
%% @doc Functions for generating macro and definitions (resp function definitions)
%%  that are expanded (resp returned) to any element of a given type.
%% At the moment only a subset of the Erlang
%% types are supported, but more types can be added easily.
%%
%% This module is not purely functional, as each generator tracks the function
%% and macro calls being generated, so it can subsequently return the
%% corresponding definitions.
%%
%% <strong>Important:</strong> Each code generator relies on a {@link freshname_generator}
%% that must be created before and passed to the code generator via the
%% {@link set_freshgen/2} function. 
%%
%% See [http://erlang.org/doc/reference_manual/typespec.html Erlang
%%        Type and function specifications]
%%    for more details.
%%
%% @author Francisco Javier López-Fraguas <fraguas@sip.ucm.es>
%% @author Manuel Montenegro <montenegro@fdi.ucm.es>
%% @author Juan Rodríguez-Hortalá <juanrh@fdi.ucm.es>
%% @copyright 2015
%%
-module(macrocall_generator).

-import(list_utils, [integer_to_string/1]).

-import(erl_syntax, [abstract/1, application/2, macro/2, variable/1, tuple/1,
                     nil/0, integer/1, atom/1, function/2, clause/3, fun_expr/1,
                     add_ann/2, attribute/2, receive_expr/1, cons/2,
                     block_expr/1, match_expr/2, operator/1, infix_expr/3]).

-export([init/1, handle_call/3, handle_cast/2, handle_info/2, terminate/2, 
        code_change/3, new/0, stop/1, gen_code/3, get_generated_code/1,
        set_freshgen/2]).



-type code_gen() :: pid().

-type gen_specifier() :: 
    none_closure | integer | float | number | {integer, integer()} |
    {atom, atom()} | any | alt | nil | nonempty_list | {'fun', integer()} |
    pos_integer | tuple_any | non_neg_integer | atom | string.
    
    
-type ast_expr() :: term().
-type ast_form() :: term().

-behaviour(gen_server).

% The generator is implemented as a gen_server, whose state contains the
% fresh name generator and the list of gen_specifiers() generated so far.

-record(st, { fresh_gen :: freshname_generator:fn_gen(), 
              generated :: gen_specifier()}).


-spec add_to_generated(gen_specifier(), #st{}) -> #st{}.
add_to_generated(Elem, #st{generated = Gen} = St) ->
    St#st{generated = sets:add_element(Elem, Gen)}.

%% @hidden
init(FNGen) -> {ok, #st{fresh_gen = FNGen, generated = sets:new()}}.


%% @hidden
% Returns: fun() -> 'NONE'() end
handle_call({gen_call, none_closure, []}, _, St) -> 
    {reply, {'fun', 0, {'function', 'NONE', 0}}, add_to_generated(none, St)};
        
% Returns: 'INTEGER'()
handle_call({gen_call, integer, []}, _, St) -> 
    {reply, application(abstract('INTEGER'), []),
         add_to_generated(integer, St)};

% Returns: 'FLOAT'()
handle_call({gen_call, float, []}, _, St) -> 
    {reply, application(abstract('FLOAT'), []),
         add_to_generated(float, St)};

% Returns: 'NUMBER'()
handle_call({gen_call, number, []}, _, St) -> 
    {reply, application(abstract('NUMBER'), []),
         add_to_generated(number, St)};
         
% Returns: 'TUPLE'()         
handle_call({gen_call, tuple_any, []}, _, St) -> 
    {reply, application(abstract('TUPLE'), []),
         add_to_generated(tuple_any, St)};

% Returns: 'POS_INTEGER'()         
handle_call({gen_call, pos_integer, []}, _, St) -> 
    {reply, application(abstract('POS_INTEGER'), []),
         add_to_generated(pos_integer, St)};
         
% Returns: 'NON_NEG_INTEGER'()         
handle_call({gen_call, non_neg_integer, []}, _, St) -> 
    {reply, application(abstract('NON_NEG_INTEGER'), []),
         add_to_generated(non_neg_integer, St)};
         
% Returns: 'ATOM'()         
handle_call({gen_call, atom, []}, _, St) -> 
    {reply, application(abstract('ATOM'), []),
         add_to_generated(atom, St)};

% Returns: 'STRING'()         
handle_call({gen_call, string, []}, _, St) -> 
    {reply, application(abstract('STRING'), []),
         add_to_generated(string, St)};

% Returns the given integer as an AST
handle_call({gen_call, {integer, N}, []}, _, St) ->
    { reply, integer(N), St };

% Returns the given atom as an AST
handle_call({gen_call, {atom, At}, []}, _, St) ->
    { reply, atom(At), St };

% Returns 'ANY'()
handle_call({gen_call, any, []}, _, St) ->
    { reply, application(abstract('ANY'), []), add_to_generated(any, St) };
         
% Returns ?ALT(alt1, ..., altn) where Alts = [alt1,...,altn]
handle_call({gen_call, alt, Alts}, _, St) -> 
    {reply, 
         lists:foldr(fun(Alt, []) -> Alt;
                        (Alt, Xs) -> macro(variable("ALT"), [Alt, Xs])  
                     end, [], Alts),
         add_to_generated(alt, St)};

% Returns {comp1, ..., compn} where Comps = [comp1,...,compn]
handle_call({gen_call, tuple, Comps}, _, St) -> 
    {reply, tuple(Comps), St};

% Returns []
handle_call({gen_call, nil, []}, _, St) -> 
    {reply, nil(), St};

% Returns ?NELIST(Head, Tail)
handle_call({gen_call, nonempty_list, [Head, Tail]}, _, St) ->
    {reply, macro(variable("NELIST"), [Head, Tail]),
        add_to_generated(nonempty_list, St)};
        
% Returns ?FUN(comp1, ..., compn, fv1, ..., fvm) where
% fv1... fvm are fresh variables and m = n+1.
handle_call({gen_call, 'fun', Comps}, _, #st{fresh_gen = FGen} = St) ->
    FVs = [ freshname_generator:fresh_name(FGen, "F") || _ <- [0|Comps] ],
    Arity = length(Comps),
    {reply, 
        macro(
            variable("FUN_" ++ list_utils:integer_to_string(Arity - 1)),
            Comps ++ [variable(FV) || FV <- FVs]
        ),
        add_to_generated({'fun' , Arity - 1}, St)
    };

% Unknown type specifier. We return 'ANY'().
handle_call({gen_call, Type, Params}, _, St) ->
    io:format("Not recognized: ~p ~p~n", [Type, Params]),
    { reply, application(abstract('ANY'), []), add_to_generated(any, St) };
    
    
handle_call(get_generated_code, _, #st{generated = Gen} = St) ->
    ListGens = sets:to_list(Gen),
    Forms = lists:append([generate_code_for(G) || G <- ListGens]),
    {reply, Forms, St}.



% Code generated:
%
% -spec 'NONE'() -> none().
% 'NONE'() -> fun (0) -> 0 end(1).
generate_code_for(none) ->
    [
 add_ann(typespec,
    attribute(spec, [
     abstract({{'NONE',0},[{type,13,'fun',[{type,13,product,[]},{type,13,none,[]}]}]})
    ])),
    function(abstract('NONE'), [
        clause([], none, [application(
            fun_expr([clause([abstract(0)], none, [abstract(0)])]),
            [abstract(1)])])
    ])
    ];

% Code generated:
%
% -spec 'INTEGER'() -> integer().
% 'INTEGER'() -> receive X when is_integer(X) -> X end.
generate_code_for(integer) ->
    [
 add_ann(typespec,
    attribute(spec, [
     abstract({{'INTEGER',0},
      [{type,12,'fun',[{type,12,product,[]},{type,12,integer,[]}]}]})
    ])),
    function(abstract('INTEGER'), [
        clause([], none, [
            receive_expr([clause([variable("X")], 
                            [application(abstract(is_integer), [variable("X")])],
                            [variable("X")])])
        ])
    ])
    ];

% Code generated:
%
% -spec 'FLOAT'() -> float().
% 'FLOAT'() -> receive X when is_float(X) -> X end.
generate_code_for(float) ->
    [
 add_ann(typespec,
    attribute(spec, [
     abstract({{'FLOAT',0},
      [{type,12,'fun',[{type,12,product,[]},{type,12,float,[]}]}]})
    ])),
    function(abstract('FLOAT'), [
        clause([], none, [
            receive_expr([clause([variable("X")], 
                            [application(abstract(is_float), [variable("X")])],
                            [variable("X")])])
        ])
    ])
    ];


% Code generated:
%
% -spec 'NUMBER'() -> number().
% 'NUMBER'() -> receive X when is_number(X) -> X end.
generate_code_for(number) ->
    [
 add_ann(typespec,
    attribute(spec, [
     abstract({{'NUMBER',0},
      [{type,12,'fun',[{type,12,product,[]},{type,12,number,[]}]}]})
    ])),
    function(abstract('NUMBER'), [
        clause([], none, [
            receive_expr([clause([variable("X")], 
                            [application(abstract(is_number), [variable("X")])],
                            [variable("X")])])
        ])
    ])
    ];

% Code generated:
%
% -spec 'POS_INTEGER'() -> pos_integer().
% 'POS_INTEGER'() -> receive X when is_integer(X), X >= 1 -> X end.
generate_code_for(pos_integer) ->
    [
 add_ann(typespec,
    attribute(spec, [
     abstract({{'POS_INTEGER',0},
      [{type,12,'fun',[{type,12,product,[]},{type,12,pos_integer,[]}]}]})
    ])),
    function(abstract('POS_INTEGER'), [
        clause([], none, [
            receive_expr([clause([variable("X")], 
                            [application(abstract(is_number), [variable("X")]),
                             infix_expr(variable("X"), operator(">="), abstract(1))],
                            [variable("X")])])
        ])
    ])
    ];


% Code generated:
%
% -spec 'NON_NEG_INTEGER'() -> non_neg_integer().
% 'POS_INTEGER'() -> receive X when is_integer(X), X >= 0 -> X end.
generate_code_for(non_neg_integer) ->
    [
 add_ann(typespec,
    attribute(spec, [
     abstract({{'NON_NEG_INTEGER',0},
      [{type,12,'fun',[{type,12,product,[]},{type,12,non_neg_integer,[]}]}]})
    ])),
    function(abstract('NON_NEG_INTEGER'), [
        clause([], none, [
            receive_expr([clause([variable("X")], 
                            [application(abstract(is_number), [variable("X")]),
                             infix_expr(variable("X"), operator(">="), abstract(0))],
                            [variable("X")])])
        ])
    ])
    ];


% Code generated:
%
% -spec 'TUPLE'() -> tuple().
% 'TUPLE'() -> receive X when is_tuple(X) -> X end.
generate_code_for(tuple_any) ->
    [
 add_ann(typespec,
    attribute(spec, [
     abstract({{'TUPLE',0},
      [{type,12,'fun',[{type,12,product,[]},{type,12,tuple,any}]}]})
    ])),
    function(abstract('TUPLE'), [
        clause([], none, [
            receive_expr([clause([variable("X")], 
                            [application(abstract(is_tuple), [variable("X")])],
                            [variable("X")])])
        ])
    ])
    ];
    
    
% Code generated:
%
% -spec 'ATOM'() -> atom().
% 'ATOM'() -> receive X when is_atom(X) -> X end.
generate_code_for(atom) ->
    [
 add_ann(typespec,
    attribute(spec, [
     abstract({{'ATOM',0},
      [{type,12,'fun',[{type,12,product,[]},{type,12,atom,[]}]}]})
    ])),
    function(abstract('ATOM'), [
        clause([], none, [
            receive_expr([clause([variable("X")], 
                            [application(abstract(is_atom), [variable("X")])],
                            [variable("X")])])
        ])
    ])
    ];    

% Code generated:
%
% -spec 'STRING'() -> string().
% 'STRING'() -> atom_to_list(X).
generate_code_for(string) ->
    [
 add_ann(typespec,
    attribute(spec, [
     abstract({{'STRING',0},
      [{type,12,'fun',[{type,12,product,[]},{type,12,string,[]}]}]})
    ])),
    function(abstract('STRING'), [
        clause([], none, [application(abstract(atom_to_list), [abstract(a)])])
        ])
    ];


% Code generated:
%
% -spec 'ANY'() -> any().
% 'ANY'() -> receive X -> X end.
 
generate_code_for(any) ->
    [
 add_ann(typespec,
    attribute(spec, [
     abstract({{'ANY',0},
      [{type,12,'fun',[{type,12,product,[]},{type,12,any,[]}]}]})
    ])),
    function(abstract('ANY'), [
        clause([], none, [
            receive_expr([clause([variable("X")], 
                            none,
                            [variable("X")])])
        ])
    ])
    ]; 

% Code generated:
%
%-define(ALT(X1, X2),
%	receive
%	  0 -> X1;
%	  1 -> X2
%	end).
generate_code_for(alt) ->
    [
        attribute(abstract(define), [
            application(variable("ALT"), [variable("X1"), variable("X2")]),
            receive_expr([
                clause([abstract(0)], none, [variable("X1")]),
                clause([abstract(1)], none, [variable("X2")])
            ])
        ])
    ]; 
  
% Code generated:
%    
% -define(NELIST(H, T), [H | T]).    
generate_code_for(nonempty_list) ->
    [
        attribute(abstract(define), [
            application(variable("NELIST"), [variable("H"), variable("T")]),
            cons(variable("H"), variable("T"))
        ])
    ];     
    
% Code generated:
%
% -define(FUN_1(X_1, Res, Y_1, Y_Res, F),
% 	begin
% 	  Y_1 = X_1,
% 	  Y_Res = Res,
% 	  F = fun (Z_1) when Z_1 =:= Y_1 -> Res end,
% 	  Y_Res = F(Y_1),
% 	  F
% 	end).    
% 
% -define(FUN_2(X_1, X_2, Res, Y_1, Y_2, Y_Res, F),
% 	begin
% 	  Y_1 = X_1,
% 	  Y_2 = X_2,
% 	  Y_Res = Res,
% 	  F = fun (Z_1) when Z_1 =:= Y_1, Z_2 =:= Y_2 -> Res end,
% 	  Y_Res = F(Y_1, Y_2),
% 	  F
% 	end).    
%
%   etc.

generate_code_for({'fun', N}) ->
    Xs = [variable("X_" ++ integer_to_string(I)) || I <- lists:seq(1, N)],
    Res = variable("Res"),
    Ys = [variable("Y_" ++ integer_to_string(I)) || I <- lists:seq(1, N)],
    YRes = variable("Y_Res"),
    Zs = [variable("Z_" ++ integer_to_string(I)) || I <- lists:seq(1, N)],
    F = variable("F"),
    [
        attribute(abstract(define), [
            application(variable("FUN_" ++ integer_to_string(N))
                , Xs ++ [Res] ++ Ys ++ [YRes, F]),
            block_expr(
                lists:zipwith(fun erl_syntax:match_expr/2, Ys, Xs) ++
                [match_expr(YRes, Res)] ++ 
                [match_expr(F, fun_expr([clause(
                    Zs,
                    lists:zipwith(fun(Z,Y) -> 
                                    infix_expr(Z, operator("=:="), Y)
                                  end, Zs, Ys),
                    [Res]
                )]))] ++
                [match_expr(YRes, application(F, Ys))] ++
                [F]
            )
        ])
    ];     
generate_code_for(_) -> [].    



%% @hidden
handle_cast({set_freshgen, FGen}, St) ->
    {noreply, St#st{fresh_gen = FGen}};
    
handle_cast(stop, State) -> {stop, normal, State};
handle_cast(Request, State) -> 
    io:format("Freshname generator: asynchronous request ~p~n", [Request]),
    {noreply, State}.
    
%% @hidden
handle_info(Info, State) ->
    io:format("Freshname generator: unexpected message ~p~n", [Info]),
    {noreply, State}.
    
%% @hidden
terminate(_, _) -> ok.

%% @hidden
code_change(_, _, State) -> {ok, State}.

%% @doc It creates a new code generator.
%%
%% <strong>Important:</strong> Each code generator relies on a {@link freshname_generator}
%% that has to be passed to the code generator via the
%% {@link set_freshgen/2} function before generating any call.
-spec new() -> code_gen().
new() -> {ok, P} = gen_server:start(?MODULE, none, []), P.
    
%% @doc It releases a code generator. The code generator given as parameter
%% cannot be used after the call.
-spec stop(code_gen()) -> ok.
stop(Gen) -> gen_server:cast(Gen, stop).

%% @doc It generates a macro or function call corresponding to the type specifier
%% passed as parameter. Some specifiers (such as `nonempty_list' or `fun') 
%% require some extra parameters, which are assumed to have already been
%% converted into Erlang expressions. The list of these is passed as a third
%% parameter.
-spec gen_code(code_gen(), gen_specifier(), [ast_expr()]) -> ast_expr().
gen_code(Gen, Type, Components) -> 
    gen_server:call(Gen, {gen_call, Type, Components}).
    
%% @doc It returns the definitions of macros and functions whose calls have
%% been produced by this generator.
-spec get_generated_code(code_gen()) -> [ast_form()].
get_generated_code(Gen) ->
    gen_server:call(Gen, get_generated_code).    

%% @doc Sets the fresh name generator associated with this code generator.
%% The code generator may rely in the latter when generating calls (for instance,
%% when calling `?FUN').
-spec set_freshgen(code_gen(), freshname_generator:fn_gen()) -> ok.
set_freshgen(Gen, FGen) -> gen_server:cast(Gen, {set_freshgen, FGen}).
