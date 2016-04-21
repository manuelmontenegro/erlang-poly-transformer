%%===========================================================================================
%% @doc
%% Compiler transformation that transform functions calls involving polymorphic types.
%%
%% This module can be used by including
%% ```
%% -compile({parse_transform, poly_transformer}).
%% '''
%% at the beginning of a given module. If typer or dialyzer is run on a module
%% with this directive, the transformation will be applied before the analysis.
%%
%% The module being analyzed can contain the following attributes:
%%
%% ```
%% -no_polymorphic_schemes([fun1/arity1, fun2/arity2, ...]).
%% '''
%% It prevents the type specs of the given function definitions from being handled
%% polymorphically. Calls to these functions will not be translated.
%%
%% ```
%% -no_polymorphic_calls([fun1/arity1, fun2/arity2, ...]).
%% '''
%% It prevents the calls contained within these functions from being transformed.
%%
%% ```
%% -poly_transformed_output("filename").
%% '''
%% It specifies the name of the file containing the transformed program.
%% By default it adds the suffix `_trans' to the name of the file. For instance,
%% `example.erl' becomes `example_trans.erl'.
%% @end
%%
%% @author Francisco Javier López-Fraguas <fraguas@sip.ucm.es>
%% @author Manuel Montenegro <montenegro@fdi.ucm.es>
%% @author Juan Rodríguez-Hortalá <juanrh@fdi.ucm.es>
%% @author Gorka Suárez García <gorka.suarez@ucm.es>
%% @copyright 2015
%%===========================================================================================
 -module(poly_transformer).
-author("Francisco Javier López-Fraguas").
-author("Manuel Montenegro").
-author("Juan Rodríguez-Hortalá").
-author("Gorka Suárez García").
-export([parse_transform/2]).
-import(erl_syntax, [
    type/1, attribute/2, attribute_name/1, concrete/1, attribute_arguments/1,
    tuple_elements/1, abstract/1, variable/1, application/2, match_expr/2, block_expr/1,
    clause/3, receive_expr/1, tuple/1, fun_expr/1, macro/2, nil/0, integer/1, atom/1,
    add_ann/2, get_ann/1, application_operator/1, application_arguments/1, function_name/1,
    function_arity/1, variable_name/1, revert_forms/1, function_clauses/1, function/2
]).

%%===========================================================================================
%% Constants
%%===========================================================================================

-define(DOT, $.).
-define(FNAME_SUFFIX, "_transformed").

%%===========================================================================================
%% Types
%%===========================================================================================

-record(options, {output = none, no_schemes = [], no_calls = [],
                  transform_recursive_calls = true}).

%%===========================================================================================
%% Functions
%%===========================================================================================

%%-------------------------------------------------------------------------------------------
%% @doc
%% Parses and transforms a source code to be compiled from the dialyzer tool.
%% @end
%%-------------------------------------------------------------------------------------------
parse_transform(Forms, CompilerOptions) ->
    % If we are not running neither dialyzer nor typer, we do not transform the program.
    case lists:member(dialyzer, CompilerOptions) of
        true ->
            % It splits the input program into the attributes at the beginning
            % (Header) and the function definitions with their type specifications.
            {Header, FunctsDefs} = split_header(Forms),
            {ok, FileName} = get_file_name(Forms),

            % It collects the transformation options from the attributes of the
            % module.
            Options = get_options(Header),

            % It builds an environment with those functions, except those
            % discarded by the -no_polymorphic_schemes attribute. Each entry
            % in the environment is of the form:
            % {{FunName, Arity}, [Scheme_1, ..., Scheme_n]}.
            Environment = [
                {{F,A},Sch} || {{F,A}, Sch} <- build_environment(Forms),
                not lists:member({F,A}, Options#options.no_schemes)
            ],

            % We transform the environment by normalizing the type schemes.
            EnvironmentNorm = [
                {FA, normalize_overloaded_schema(Scs)}
                || {FA, Scs} <- Environment
            ],

            % It generates a macro for each entry in the environment. Each
            % entry of the MacroEnv is of the form:
            % {{FunName, Arity}, {MacroName, NumberOfExtraVars, ListOfMacros}}
            %
            % An overloaded specification is translated into a list of macros
            % (one for each scheme), and a 'main' macro. MacroName contains the
            % name of this main macro, and ListOfMacros contain the definitions
            % of each macro.
            MGen = macrocall_generator:new(),
            MacroEnv = [
                genmacro_overloaded_scheme(MGen, Binding)
                || Binding <- EnvironmentNorm
            ],

            % It collects all the macro definitions into a single list.
            MacroDefs = lists:append([ MDefs || {_, {_, _, MDefs}} <- MacroEnv ]),

            % It substitutes the type specs of the module by the normalized
            % specs.
            NormFuncDefs = [
                normalize_form(EnvironmentNorm, Form)
                || Form <- FunctsDefs
            ],

            % It replaces the calls of functions by calls to macros.
            TransformedFuncDefs = [
                replace_calls(MacroEnv, Form, Options#options.no_calls,
                    Options#options.transform_recursive_calls)
                || Form <- NormFuncDefs
            ],

            % Now we obtain the definitions of the auxiliary macros and functions
            % that have been called throughout the whole module.
            NewDefs = macrocall_generator:get_generated_code(MGen),

            % So our final module is:
            Transformed = Header ++ NewDefs ++ MacroDefs ++ TransformedFuncDefs,

            % We write the module, and obtain the name of the filename written.
            WrittenFileName = write_transformed(Options#options.output,
                Transformed, FileName),

            % Expand the macros again, so typer receives the result.
            {ok, NewForms} = epp:parse_file(WrittenFileName, []),
            NewForms;

        false ->
            Forms
    end.

%%-------------------------------------------------------------------------------------------
%% @doc
%% It splits the module into the initial attributes and the rest of the file
%% (containing function definitions and type specs).
%% @end
%%-------------------------------------------------------------------------------------------
split_header(Forms) ->
    lists:splitwith(fun(Form) -> type(Form) == attribute andalso
        concrete(attribute_name(Form)) /= spec end, Forms).

%%-------------------------------------------------------------------------------------------
%% @doc
%% Checks if the current element is an attribute directive.
%% @end
%%-------------------------------------------------------------------------------------------
is_directive(Form, Directive) ->
    type(Form) == attribute andalso concrete(attribute_name(Form)) == Directive.


%%-------------------------------------------------------------------------------------------
%% @doc
%% It generates an #options{} record from the attributes given in the header.
%% @end
%%-------------------------------------------------------------------------------------------
get_options(Header) ->
    lists:foldl(
        fun(Form, Options) ->
            case type(Form) of
                attribute ->
                    case concrete(attribute_name(Form)) of
                        poly_transformed_output ->
                            [Arg] = attribute_arguments(Form),
                            Options#options{output = concrete(Arg)};
                        no_polymorphic_calls ->
                            [Arg] = attribute_arguments(Form),
                            Options#options{no_calls = concrete(Arg)};
                        no_polymorphic_schemes ->
                            [Arg] = attribute_arguments(Form),
                            Options#options{no_schemes = concrete(Arg)};
                        no_transform_recursive_calls ->
                            Options#options{transform_recursive_calls = false};
                        _ -> Options
                    end;
                _ -> Options
            end
        end,
        #options{},
        Header
    ).

%%-------------------------------------------------------------------------------------------
%% @doc
%% Obtains the name of the input file.
%% @end
%%-------------------------------------------------------------------------------------------
get_file_name(Forms) ->
    Forms1 = lists:dropwhile(fun(Form) -> not (is_directive(Form, file)) end, Forms),
    case Forms1 of
        [] -> none;
        [X|_] -> [Name|_] = attribute_arguments(X), {ok, concrete(Name)}
    end.

%%-------------------------------------------------------------------------------------------
%% @doc
%% It builds an environment from the type specs of the program.
%% @end
%%-------------------------------------------------------------------------------------------
build_environment(Forms) ->
    [ concrete(Arg) || Form <- Forms, is_directive(Form, spec),
                       [Arg|_] <- [attribute_arguments(Form)] ].

%%===========================================================================================
%% Functions (TYPE SCHEME LINEARIZATION)
%%===========================================================================================

%%-------------------------------------------------------------------------------------------
%% @doc
%% Normalizes an overloaded schema.
%% @end
%%-------------------------------------------------------------------------------------------
normalize_overloaded_schema(Schemas) ->
    NewSchemas = [normalize_type_clause(Schema) || Schema <- Schemas],
    NewSchemas.

%%-------------------------------------------------------------------------------------------
%% @doc
%% Normalizes a type clause.
%% @end
%%-------------------------------------------------------------------------------------------
normalize_type_clause(Type) ->
     {NormType, _} = normalize_type_clause_aux(Type),
     NormType.

%%-------------------------------------------------------------------------------------------
%% @doc
%% This function returns, in addition to the normalized clause, a mapping
%% from the variables of the new linear scheme to those of the non-linear one.
%% @end
%%-------------------------------------------------------------------------------------------
normalize_type_clause_aux({type, L, bounded_fun, [Type, Constraints]}) ->
    {NewType, Mapping} = normalize_type_clause_aux(Type),
    NewConstraints = lists:append(
        [apply_mapping_to_constraint(Mapping, C) || C <- Constraints]
    ),
    {{type, L, bounded_fun, [NewType, NewConstraints]}, Mapping};

normalize_type_clause_aux({type, L, 'fun', [TParams, TRet]}) ->
    FNGen = freshname_generator:new(),
    {TParamsNew, Mapping} = refresh_names(FNGen, TParams),
    freshname_generator:stop(FNGen),
    TRetNew = join_vars(TRet, Mapping),
    {{type, L, 'fun', [TParamsNew, TRetNew]}, Mapping}.

%%-------------------------------------------------------------------------------------------
%% @doc
%% This function substitutes the type variables of a type for fresh names,
%% obtaining the corresponding map from the new variables to the old ones.
%% @end
%%-------------------------------------------------------------------------------------------
refresh_names(FNGen, Type) ->
    {_, Mapping, [NewType]} = list_utils:fold_type(fun(_, St) -> St end,
        fun refresh_names_aux/2, {FNGen, [], []}, Type),
    {NewType, Mapping}.

refresh_names_aux({var, L, Var}, {FNGen, Mapping, Stack}) ->
    FV = freshname_generator:fresh_name(FNGen, atom_to_list(Var)),
    {FNGen, [{FV, Var}|Mapping], [{var, L, FV} | Stack]};

refresh_names_aux(Type, {FNGen, Mapping, Stack}) ->
    {Type1, Stack1} = list_utils:post_compose_type(Type, Stack),
    {FNGen, Mapping, [Type1|Stack1]}.

%%-------------------------------------------------------------------------------------------
%% @doc
%% It replaces the variables of the right-hand side of a spec by using the previously
%% computed mapping.
%%
%% For instance, given the schema (A,A) -> A, if the LHS is transformed into (A_1,A_2),
%% then the RHS is transformed in to A_1 | A_2.
%% @end
%%-------------------------------------------------------------------------------------------
join_vars(Type, Mapping) ->
    {_, [TRet1]} = list_utils:fold_type(fun(_, M) -> M end,
        fun join_names_aux/2, {Mapping, []}, Type),
    TRet1.

join_names_aux({var, L, Var}, {Mapping, Stack}) ->
    FVS = [ {var, L, FV} || {FV,Var1} <- Mapping, Var1 == Var ],
    case FVS of
        [] -> {Mapping, [{var, L, Var} | Stack]};
        [FV] -> {Mapping, [FV | Stack]};
        [_|_] -> {Mapping, [{type, L, union, lists:reverse(FVS)} | Stack]}
    end;

join_names_aux(Type, {Mapping, Stack}) ->
    {Type1, Stack1} = list_utils:post_compose_type(Type, Stack),
    {Mapping, [Type1|Stack1]}.

%%-------------------------------------------------------------------------------------------
%% @doc
%% It transform the constraints of a type scheme by using the given mapping.
%% This may result in a combinatorial explosion. For instance, given the spec:
%%    -spec (A, A, B, B) -> integer() when A :: B,
%%
%% it yields:
%%    -spec(A_1, A_2, B_1, B_2) -> integer() when A_1 :: B_1, A_1 :: B_2,
%%                                                A_2 :: B_1, A_2 :: B_2.
%% @end
%%-------------------------------------------------------------------------------------------
apply_mapping_to_constraint(M, {type, L, constraint, [F, Params]}) ->
    FVs = lists:append([free_variables(Par) || Par <- Params]),
    % Computing the inverse of the mapping M.
    InvM = [{Var, lists:reverse([FV || {FV, Var1} <- M, Var1 == Var])} || Var <- FVs],
    % If a tuple {X, []} occurs in InvM, then X is a variable that only
    % occurs in the constraints, but not in the LHS of the spec. We replace
    % the binding {X, []} by {X, [X]}.
    InvMSingleton = [{Var, case Vs of [] -> [Var]; Xs -> Xs end} || {Var, Vs} <- InvM],
    Perms = permutations(InvMSingleton),
    %Perms = permutations(InvM),
    [{type, L, constraint, [F, [apply_permutation(Par, Perm) || Par <- Params]]} || Perm <- Perms].

%%-------------------------------------------------------------------------------------------
%% @doc
%% Gets the variable nodes inside a list of types.
%% @end
%%-------------------------------------------------------------------------------------------
free_variables(Type) ->
    lists:reverse(list_utils:fold_type(fun(_, St) -> St end, fun free_variables_aux/2, [], Type)).

free_variables_aux({var, _, Var}, FVs) -> [Var | FVs];
free_variables_aux(_, FVs) -> FVs.

%%-------------------------------------------------------------------------------------------
%% @doc
%% Applies a list of permutations.
%% @end
%%-------------------------------------------------------------------------------------------
apply_permutation(Type, Permut) ->
    {_, [Type1]} = list_utils:fold_type(fun(_, St) -> St end,
        fun apply_permutation_aux/2, {Permut, []}, Type),
    Type1.

apply_permutation_aux({var, L, Var}, {M, Stack}) ->
    case lists:keyfind(Var, 1, M) of
        {Var, FV} -> {M, [{var, L, FV} | Stack]};
        false -> {M, [{var, L, Var} | Stack]}
    end;

apply_permutation_aux(Type, {M, Stack}) ->
    {Type1, Stack1} = list_utils:post_compose_type(Type, Stack),
    {M, [Type1|Stack1]}.

%%-------------------------------------------------------------------------------------------
%% @doc
%% Gets a list of permutations.
%% @end
%%-------------------------------------------------------------------------------------------
permutations([]) -> [[]];
permutations([{V,FVs}|Vars]) ->
    Perms = permutations(Vars),
    lists:append([[[{V, FV}|Perm] || Perm <- Perms] || FV <- FVs]).

%%===========================================================================================
%% Functions (MACRO GENERATION)
%%===========================================================================================

%%-------------------------------------------------------------------------------------------
%% @doc
%% This generates the macro of a function with or without an overloaded scheme.
%% @end
%%-------------------------------------------------------------------------------------------
genmacro_overloaded_scheme(MGen, {{FunName, Arity}, [Scheme]}) ->
    % This generates the macro of a function with a non-overloaded scheme
    MacroName = string:to_upper(atom_to_list(FunName) ++
        "_" ++ list_utils:integer_to_string(Arity)),
    {Macro, NumVars} = genmacro(MGen, MacroName, Arity, Scheme),
    {{FunName, Arity}, {MacroName, NumVars, [Macro]}};

genmacro_overloaded_scheme(MGen, {{FunName, Arity}, OverloadedSpec}) ->
    % This generates the macro of a function with an overloaded scheme
    N = length(OverloadedSpec),
    FGen = freshname_generator:new(),
    Pars = [variable(freshname_generator:fresh_name(FGen, "PAR"))
                || _ <- lists:seq(1, Arity)],
    MacroBaseName = string:to_upper(atom_to_list(FunName) ++
        "_" ++ list_utils:integer_to_string(Arity)),
    {SubMacroEnv, Varss, MacroCalls} = lists:unzip3(lists:map(
        fun({M, Scheme}) ->
            MacroName = MacroBaseName ++ "_" ++ list_utils:integer_to_string(M),
            {Macro, NumVars} = genmacro(MGen, MacroName, Arity, Scheme),
            Vars = [
                variable(freshname_generator:fresh_name(FGen, "F"))
                || _ <- lists:seq(1, NumVars)
            ],
            {{MacroName, Macro}, Vars, macro(variable(MacroName), Pars ++ Vars)}
        end,
        lists:zip(lists:seq(1, N), OverloadedSpec)
    )),
    {_, SubMacros} = lists:unzip(SubMacroEnv),
    TotalExtraVars = lists:append(Varss),
    Macro = attribute(
        abstract(define),
        [application(variable(MacroBaseName), Pars ++ TotalExtraVars),
            macrocall_generator:gen_code(MGen, alt, MacroCalls)]
    ),
    freshname_generator:stop(FGen),
    {{FunName, Arity}, {MacroBaseName, length(TotalExtraVars), SubMacros ++ [Macro]}}.

%%-------------------------------------------------------------------------------------------
%% @doc
%% This generates the macro of each clause in a (possibly overloaded) scheme.
%% @end
%%-------------------------------------------------------------------------------------------
genmacro(MGen, MacroName, Arity, Scheme) ->
    FGen = freshname_generator:new(),
    macrocall_generator:set_freshgen(MGen, FGen),
    Params = [ freshname_generator:fresh_name(FGen, "PAR") || _ <- lists:seq(1, Arity) ],
    ParamsVar = [variable(Param) || Param <- Params],

    FVs = [ freshname_generator:fresh_name(FGen, "FRESH") || _ <- Params ],
    FVsVar = [variable(FV) || FV <- FVs],
    %FreshBindings = lists:zipwith(fun erl_syntax:match_expr/2, FVsVar, ParamsVar),
    FreshBindings = [match_expr(tuple(FVsVar), tuple(ParamsVar))],

    {TPars, TRes, Constraints} = decompose_scheme(Scheme),
    TParTypeVars = lists:append([free_variables(TPar) || TPar <- TPars]),
    TConstrTypeVars = list_utils:difference(
        list_utils:nub(lists:append([
            lists:append([free_variables(T) || T <- Ts])
            || {type, _, constraint, [_, Ts]} <- Constraints
        ])),
        TParTypeVars
    ),

    TParConstrTypeVars = TParTypeVars ++ TConstrTypeVars,
    As = [freshname_generator:fresh_name(FGen, "A") || _ <- TParConstrTypeVars],
    AVars = [ variable(A) || A <- As ],
    APs = [freshname_generator:fresh_name(FGen, "AP")  || _ <- TParConstrTypeVars],

    Eta = maps:from_list(lists:zip(TParConstrTypeVars, [variable(A) || A <- As])),
    Theta = maps:from_list(lists:zip(TParConstrTypeVars, [variable(AP) || AP <- APs])),

    ExpPars = lists:map(
        fun(TPar) ->
            VarsToSet = [maps:get(FreeVar, Theta) || FreeVar <- free_variables(TPar)],
            tr_par(TPar, MGen, FGen, Eta, Theta, VarsToSet)
        end,
        TPars
    ),
    ExpPars2 = lists:map(
        fun(TPar) ->
            VarsToSet = [maps:get(FreeVar, Theta) || FreeVar <- free_variables(TPar)],
            tr_par(TPar, MGen, FGen, Eta, Theta, VarsToSet)
        end,
        [{var, 0, Name} || Name <- TConstrTypeVars]
    ),

    ParBindings = lists:zipwith(fun erl_syntax:match_expr/2, FVsVar, ExpPars),
    CsBindings = [tr_constraint(C, MGen, FGen, Eta, Theta) || C <- Constraints],

    EtaP = maps:from_list(lists:zip(
        TParConstrTypeVars,
        [application(variable(AP), []) || AP <- APs]
    )),

    ExpRes = tr_par(TRes, MGen, FGen, EtaP, Theta, []),
    GVsVar = ParamsVar,

    Macro = attribute(abstract(define), [
        application(variable(list_to_atom(MacroName)), GVsVar),
        application(fun_expr([clause([], [],
            FreshBindings ++
            [receive_expr([clause(
                [tuple(AVars)],
                none,
                ParBindings ++ ExpPars2 ++ lists:append(CsBindings) ++ [ExpRes]
            )])]
        )]), [])
    ]),

    freshname_generator:stop(FGen),
    {Macro, Arity}.

%%-------------------------------------------------------------------------------------------
%% @doc
%% Decomposes a scheme.
%% @end
%%-------------------------------------------------------------------------------------------
decompose_scheme({type, _, 'fun', [{type, _, product, Params}, Res]}) ->
    {Params, Res, []};
decompose_scheme({type, _, bounded_fun, [T, C]}) ->
    {Params, Res, _} = decompose_scheme(T),
    {Params, Res, C}.

%%-------------------------------------------------------------------------------------------
%% @doc
%% Adds a block expression if needed.
%% @end
%%-------------------------------------------------------------------------------------------
block_expr_if_needed([Exp]) -> Exp;
block_expr_if_needed(Exps)  -> block_expr(Exps).

%%-------------------------------------------------------------------------------------------
%% @doc
%% Transforms a parameter.
%% @end
%%-------------------------------------------------------------------------------------------
tr_par({var, _, Alpha}, MGen, _, Eta, Theta, VarsToSet) ->
    AVar = maps:get(Alpha, Eta),
    APrime = maps:get(Alpha, Theta),
    Bindings = lists:map(
        fun(VarToSet) ->
            Rhs = case VarToSet == APrime of
                      true  -> fun_expr([clause([], none, [AVar])]);
                      false -> macrocall_generator:gen_code(MGen, none_closure, [])
                  end,
            match_expr(VarToSet, Rhs)
        end,
        VarsToSet
    ),
    block_expr_if_needed(Bindings ++ [AVar]);

tr_par({type, _, integer, []}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par_comps([], MGen, FGen, Eta, Theta, VarsToSet, integer);

tr_par({type, _, float, []}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par_comps([], MGen, FGen, Eta, Theta, VarsToSet, float);

tr_par({type, _, union, Alts}, MGen, FGen, Eta, Theta, VarsToSet) ->
    AltExprs = [ tr_par(Alt, MGen, FGen, Eta, Theta, VarsToSet) || Alt <- Alts ],
    macrocall_generator:gen_code(MGen, alt, AltExprs);

tr_par({type, _, tuple, any}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par_comps([], MGen, FGen, Eta, Theta, VarsToSet, tuple_any);

tr_par({type, _, tuple, Comps}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par_comps(Comps, MGen, FGen, Eta, Theta, VarsToSet, tuple);

tr_par({type, _, list, Comps}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par({type, 0, union, [{nil, 0}, {type, 0, nonempty_list, Comps}]},
        MGen, FGen, Eta, Theta, VarsToSet);

tr_par({nil, _}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par_comps([], MGen, FGen, Eta, Theta, VarsToSet, nil);

tr_par({type, _, nil, _}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par_comps([], MGen, FGen, Eta, Theta, VarsToSet, nil);

tr_par({type, _, nonempty_list, [Comp]}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par_comps([Comp, {nil,0}], MGen, FGen, Eta, Theta, VarsToSet, nonempty_list);

tr_par({type, _, nonempty_list, Comps}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par_comps(Comps, MGen, FGen, Eta, Theta, VarsToSet, nonempty_list);

tr_par({type, _, 'fun', [{type, _, product, TPars}, TRes]}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par_comps(TPars ++ [TRes], MGen, FGen, Eta, Theta, VarsToSet, 'fun');

tr_par({integer, _, N}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par_comps([], MGen, FGen, Eta, Theta, VarsToSet, {integer, N});

tr_par({atom, _, At}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par_comps([], MGen, FGen, Eta, Theta, VarsToSet, {atom, At});

tr_par({type, _, any, []}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par_comps([], MGen, FGen, Eta, Theta, VarsToSet, any);

tr_par({type, _, number, []}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par_comps([], MGen, FGen, Eta, Theta, VarsToSet, number);

tr_par({type, _, atom, []}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par_comps([], MGen, FGen, Eta, Theta, VarsToSet, atom);

tr_par({type, _, string, []}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par_comps([], MGen, FGen, Eta, Theta, VarsToSet, string);

tr_par({type, _, pos_integer, []}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par_comps([], MGen, FGen, Eta, Theta, VarsToSet, pos_integer);

tr_par({type, _, non_neg_integer, []}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par_comps([], MGen, FGen, Eta, Theta, VarsToSet, non_neg_integer);

tr_par({type, _, boolean, []}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par({type, 0, union, [{atom, 0, true}, {atom, 0, false}]},
        MGen, FGen, Eta, Theta, VarsToSet);

tr_par({type, L, term, []}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par({type, L, any, []}, MGen, FGen, Eta, Theta, VarsToSet);

tr_par({ann_type, _, [_, T]}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par(T, MGen, FGen, Eta, Theta, VarsToSet);

tr_par({paren_type, _, [T]}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par(T, MGen, FGen, Eta, Theta, VarsToSet);

tr_par(Type, MGen, _, _, _, _) ->
    io:format("Unknown type: ~p. Using any()~n", [Type]),
    %io:format("Unknown type: ~s. Using any()~n", [list_utils:type_to_string(Type)]),
    macrocall_generator:gen_code(MGen, any, []).

%%-------------------------------------------------------------------------------------------
%% @doc
%% Transforms the components of a parameter.
%% @end
%%-------------------------------------------------------------------------------------------
tr_par_comps(Comps, MGen, FGen, Eta, Theta, VarsToSet, GenCallName) ->
    FreeVarsComps = [
        [maps:get(V, Theta, variable(V)) ||  V <- free_variables(Comp)]
        || Comp <- Comps
    ],
    VarsToSetComp = [
        [ V || V <- VarsToSet, lists:member(V, FVComp)]
        || FVComp <- FreeVarsComps
    ],
    MentionedVars = lists:append(VarsToSetComp),
    NotMentionedVars = [V || V <- VarsToSet, not lists:member(V, MentionedVars)],

    CompsExprs = [
        tr_par(Comp, MGen, FGen, Eta, Theta, VarToSetComp)
        || {Comp, VarToSetComp} <- lists:zip(Comps, VarsToSetComp)
    ],
    NotMentionedAssignments = [
        match_expr(Var, macrocall_generator:gen_code(MGen, none_closure, []))
        || Var <- NotMentionedVars
    ],

    LastExpr = macrocall_generator:gen_code(MGen, GenCallName, CompsExprs),
    block_expr_if_needed(NotMentionedAssignments ++ [LastExpr]).

%%-------------------------------------------------------------------------------------------
%% @doc
%% Transforms a constraint.
%% @end
%%-------------------------------------------------------------------------------------------
tr_constraint({type, _, constraint, [{atom, _, is_subtype}, [C1, C2]]}, MGen, FGen, Eta, Theta) ->
    FV = freshname_generator:fresh_name(FGen, "C"),
    Expr1 = tr_par(C1, MGen, FGen, Eta, Theta, []),
    Expr2 = tr_par(C2, MGen, FGen, Eta, Theta, []),
    [match_expr(variable(FV), Expr1), match_expr(variable(FV), Expr2)].

%%-------------------------------------------------------------------------------------------
%% @doc
%% This replaces the specs of the program with their linearized versions.
%% @end
%%-------------------------------------------------------------------------------------------
normalize_form(NormEnv, Form) ->
    case is_directive(Form, spec) of
        true ->
            [Arg|_] = attribute_arguments(Form),
            {NameArity,_} = concrete(Arg),
            Form1 =
                case lists:keyfind(NameArity, 1, NormEnv) of
                    {NameArity, NormType} ->
                        attribute(
                            abstract(spec),
                            [tuple([
                                abstract(NameArity),
                                abstract(NormType)
                            ])]);
                    false -> Form
                end,
            add_ann(typespec, Form1);
        false -> Form
    end.

%%-------------------------------------------------------------------------------------------
%% @doc
%% It replaces the function calls in the environment with the corresponding macro calls.
%% @end
%%-------------------------------------------------------------------------------------------
replace_calls(MacroEnv, Form, NoPolyCalls, TransformRecCalls) ->
    case type(Form) of
        function ->
            Name = concrete(function_name(Form)),
            Arity = function_arity(Form),
            case lists:member({Name, Arity}, NoPolyCalls) of
                false ->
                    MacroEnv2 =
                        case TransformRecCalls of
                            true -> MacroEnv;
                            false -> lists:keydelete({Name,Arity},1,MacroEnv)
                        end,
                    erl_syntax_lib:map(
                        fun(Exp) -> replace_call(ok, MacroEnv2, Exp) end,
                        Form
                    );
                true -> Form
            end;
        _ -> Form
    end.

%%-------------------------------------------------------------------------------------------
%% @doc
%% It replaces the function calls in the environment with the corresponding macro calls.
%% @end
%%-------------------------------------------------------------------------------------------
replace_call(_, MacroEnv, Expr) ->
    case type(Expr) of
        application ->
            case application_operator(Expr) of
                {atom, _, FunName} ->
                    Args = application_arguments(Expr),
                    Arity = length(Args),
                    case lists:keyfind({FunName, Arity}, 1, MacroEnv) of
                        {_, {MacroName, _, _}} -> macro(variable(MacroName), Args);
                        false -> Expr
                    end;
                _ -> Expr
            end;
        _ -> Expr
    end.

%%-------------------------------------------------------------------------------------------
%% @doc
%% Writes a transforme source code into a new output file.
%% @end
%%-------------------------------------------------------------------------------------------
write_transformed(none, Forms, FileName) ->
    RevFileName = lists:reverse(FileName),
    Filter = fun(C) -> C /= ?DOT end,
    {RevExt, RevNameAndPoint} = lists:splitwith(Filter, RevFileName),
    NewName = case RevNameAndPoint of
        [?DOT|RevName] ->
            Name = lists:reverse(RevName),
            Ext = lists:reverse(RevExt),
            Name ++ ?FNAME_SUFFIX ++ [?DOT] ++ Ext;
        [] ->
            FileName ++ ?FNAME_SUFFIX
    end,
    write_transformed(NewName, Forms, FileName);
write_transformed(FileName, Forms, _) ->
    case file:open(FileName, [write, {encoding, utf8}]) of
        {ok, File} ->
            [io:fwrite(File, "~s~n~n", [erl_prettypr_format(Form)]) || Form <- Forms],
            io:format("Transformed program written into: ~s~n", [FileName]);
        {error, Reason} ->
            io:format("Cannot write output into: ~s [Reason: ~p]~n", [FileName, Reason])
    end,
    FileName.

%%-------------------------------------------------------------------------------------------
%% @doc
%% Gets a pretty print format to be used with a "form" element.
%% @end
%%-------------------------------------------------------------------------------------------
erl_prettypr_format(Form = {attribute,_,_,_}) ->
    erl_prettypr_format(Form, [{paper, 800}, {ribbon, 800}]);
erl_prettypr_format(Form) ->
    erl_prettypr_format(Form, [{paper, 100}, {ribbon, 100}]).

%%-------------------------------------------------------------------------------------------
%% @doc
%% Gets a pretty print format to be used with a "form" element.
%% @end
%%-------------------------------------------------------------------------------------------
erl_prettypr_format(Form, Extras) ->
    erl_prettypr:format(Form, [{hook, fun print_spec/3}, {encoding, utf8} | Extras]).

%%-------------------------------------------------------------------------------------------
%% @doc
%% Pretty prints a specification.
%% @end
%%-------------------------------------------------------------------------------------------
print_spec(Form, Ctx, Cont) ->
    Annotations = get_ann(Form),
    case lists:member(typespec, Annotations) of
        true ->
            [{NameArity, Schemes}] = [
                concrete(Arg) || Arg <- attribute_arguments(Form)
            ],
            prettypr:text(list_utils:spec_to_string(
                {attribute, 0, spec, {NameArity, Schemes}}
            ));
        false ->
            Cont(Form, Ctx)
    end.
