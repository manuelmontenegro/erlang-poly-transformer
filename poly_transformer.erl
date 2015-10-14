%%
%% @doc Compiler transformation that transform functions calls involving
%% polymorphic types.
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
%%
%% @author Francisco Javier López-Fraguas <fraguas@sip.ucm.es>
%% @author Manuel Montenegro <montenegro@fdi.ucm.es>
%% @author Juan Rodríguez-Hortalá <juanrh@fdi.ucm.es>
%% @copyright 2015
 
-module(poly_transformer).

-export([parse_transform/2]).

-compile([export_all]).

-import(erl_syntax, [type/1, attribute/2, attribute_name/1, concrete/1,
                    attribute_arguments/1, tuple_elements/1, abstract/1,
                    variable/1, application/2, match_expr/2, block_expr/1,
                    clause/3, receive_expr/1, tuple/1, fun_expr/1, macro/2,
                    nil/0, integer/1, atom/1, add_ann/2, get_ann/1,
                    application_operator/1, application_arguments/1,
                    function_name/1, function_arity/1, variable_name/1,
                    revert_forms/1, function_clauses/1, function/2]).
                    
-import(lists, [mapfoldl/3, reverse/1, member/2]).                    


-record(options, {output = none, no_schemes = [], no_calls = []}).

parse_transform(Forms, CompilerOptions) ->
    % If we are not running neither dialyzer nor typer, we do not transform
    % the program.
    case lists:member(dialyzer, CompilerOptions) of
        true -> 
            % It splits the input program into the attributes at the beginning
            % (Header) and the function definitions with their type specifications.
            {Header, FunctsDefs} = split_header(Forms),
            
            % It collects the transformation options from the attributes of the
            % module.
            Options = get_options(Header),
            
            {ok, FileName} = get_file_name(Forms),
            
            % It builds an environment with those functions, except those
            % discarded by the -no_polymorphic_schemes attribute.
            %
            % Each entry in the environment is of the form
            % {{FunName, Arity}, [Scheme_1, ..., Scheme_n]}
            Environment = [ {{F,A},Sch} 
                            || {{F,A}, Sch} <- build_environment(Forms),
                               not member({F,A}, Options#options.no_schemes) ],
            
            % We transform the environment by normalizing the type schemes
            EnvironmentNorm = 
                [ {FA, normalize_overloaded_schema(Scs)} 
                            || {FA, Scs} <- Environment ],
            
            
            % It generates a macro for each entry in the environment, 
            %
            % Each entry of the MacroEnv is of the form:
            % {{FunName, Arity}, {MacroName, NumberOfExtraVars, ListOfMacros}}
            %
            % An overloaded specification is translated into a list of macros
            % (one for each scheme), and a 'main' macro. MacroName contains the
            % name of this main macro, and ListOfMacros contain the definitions
            % of each macro.            
            % 
            MGen = macrocall_generator:new(),
            MacroEnv = [ genmacro_overloaded_scheme(MGen, Binding)
                            || Binding <- EnvironmentNorm ],
            
     
            % It collects all the macro definitions into a single list.
            MacroDefs = lists:append([ MDefs || {_, {_, _, MDefs}} <- MacroEnv ]),
            

            % It substitutes the type specs of the module by the normalized
            % specs.
            NormFuncDefs = [ normalize_form(EnvironmentNorm, Form) 
                                || Form <- FunctsDefs ],
            

            % It replaces the calls of functions by calls to macros.
            TransformedFuncDefs = 
                [ replace_calls(MacroEnv, Form, Options#options.no_calls)
                     || Form <- NormFuncDefs ],
                
            % Now we obtain the definitions of the auxiliary macros and functions
            % that have been called throughout the whole module.
            NewDefs = macrocall_generator:get_generated_code(MGen),
            
            % ..so our final module is
            Transformed = Header ++ NewDefs ++ MacroDefs ++ TransformedFuncDefs,
            
            % We write the module, and obtain the name of the filename written.
            WrittenFileName = 
                write_transformed(Options#options.output, Transformed, FileName),

            % Expand the macros again, so typer receives the result.
            {ok, NewForms} = epp:parse_file(WrittenFileName, []),
            NewForms;
        false -> Forms
    end.


% It splits the module into the initial attributes and the rest of the
% file (containing function definitions and type specs).
split_header(Forms) ->
    lists:splitwith(fun(Form) -> 
                        type(Form) == attribute andalso 
                            concrete(attribute_name(Form)) /= spec end, Forms).
    
is_directive(Form, Directive) ->
    type(Form) == attribute andalso concrete(attribute_name(Form)) == Directive.


% It generates an #options{} record from the attributes given in the
% header.
get_options(Header) ->
    lists:foldl(fun(Form, Options) ->
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
                                _ -> Options
                            end;
                        _ -> Options
                    end
                end, #options{}, Header).
    
    
% Obtains the name of the input file.
get_file_name(Forms) ->
    Forms1 = lists:dropwhile(
        fun(Form) -> not (is_directive(Form, file)) end, Forms),
    case Forms1 of
        [] -> none;
        [X|_] -> [Name|_] = attribute_arguments(X), {ok, concrete(Name)}
    end.

% It builds an environment from the type specs of the program.
build_environment(Forms) ->
    [ concrete(Arg) || Form <- Forms, is_directive(Form, spec),
                       [Arg|_] <- [attribute_arguments(Form)] ].

% TYPE SCHEME LINEARIZATION
% -------------------------
normalize_overloaded_schema(Schemas) ->
    NewSchemas = [normalize_type_clause(Schema) || Schema <- Schemas],
    NewSchemas.


normalize_type_clause(Type) -> 
     {NormType, _} = normalize_type_clause_aux(Type),
     NormType.

% This function returns, in addition to the normalized clause, a mapping
% from the variables of the new linear scheme to those of the non-linear one.
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
        

% This function substitutes the type variables of a type for fresh names,
% obtaining the corresponding map from the new variables to the old ones. 
refresh_names(FNGen, Type) ->
    {_, Mapping, [NewType]} = 
         list_utils:fold_type(fun(_, St) -> St end, 
                              fun refresh_names_aux/2,
                              {FNGen, [], []}, Type),
    {NewType, Mapping}.

refresh_names_aux({var, L, Var}, {FNGen, Mapping, Stack}) ->
    FV = freshname_generator:fresh_name(FNGen, atom_to_list(Var)),
    {FNGen, [{FV, Var}|Mapping], [{var, L, FV} | Stack]};
refresh_names_aux(Type, {FNGen, Mapping, Stack}) ->
    {Type1, Stack1} = list_utils:post_compose_type(Type, Stack),
    {FNGen, Mapping, [Type1|Stack1]}.
    

% It replaces the variables of the right-hand side of a spec by using
% the previously computed mapping.
%
% For instance, given the schema (A,A) -> A, if the LHS is transformed
% into (A_1,A_2), then the RHS is transformed in to A_1 | A_2.
join_vars(Type, Mapping) ->
    {_, [TRet1]} = 
        list_utils:fold_type(fun(_, M) -> M end,
                             fun join_names_aux/2,
                             {Mapping, []}, Type),
    TRet1.
    
join_names_aux({var, L, Var}, {Mapping, Stack}) ->
    FVS = [ {var, L, FV} || {FV,Var1} <- Mapping, Var1 == Var ],
    case FVS of
        [] -> {Mapping, [{type, L, none, []} | Stack]};
        [FV] -> {Mapping, [FV | Stack]};
        [_|_] -> {Mapping, [{type, L, union, reverse(FVS)} | Stack]}
    end;
    
join_names_aux(Type, {Mapping, Stack}) ->
    {Type1, Stack1} = list_utils:post_compose_type(Type, Stack),
    {Mapping, [Type1|Stack1]}.


% It transform the constraints of a type scheme by using the given mapping.
%
% This may result in a combinatorial explosion. For instance, given the spec:
%
% -spec (A,A,B,B) -> integer() when A :: B,
%
% it yields:
%
% -spec (A_1,A_2,B_1,B_2) -> integer() when A_1 :: B_1, A_1 :: B_2, A_2 :: B_1,
%                                           A_2 :: B_2.
% 
apply_mapping_to_constraint(M, {type, L, constraint, [F, Params]}) ->
    FVs = lists:append([free_variables(Par) || Par <- Params]),
    % Computing the inverse of the mapping M
    InvM = [ {Var, reverse([FV || {FV, Var1} <- M, Var1 == Var])} 
                                  || Var <- FVs ],
    Perms = permutations(InvM),
    [{type, L, constraint, [F, [apply_permutation(Par, Perm) || Par <- Params]]}
        || Perm <- Perms].

free_variables(Type) -> reverse(list_utils:fold_type(fun(_, St) -> St end, 
                                fun free_variables_aux/2, [], Type)).
                                
free_variables_aux({var, _, Var}, FVs) -> [Var | FVs];
free_variables_aux(_, FVs) -> FVs.


apply_permutation(Type, Permut) ->
    {_, [Type1]} = 
        list_utils:fold_type(fun(_, St) -> St end, fun apply_permutation_aux/2, 
                  {Permut, []}, Type),
    Type1.

                                
apply_permutation_aux({var, L, Var}, {M, Stack}) -> 
    case lists:keyfind(Var, 1, M) of
        {Var, FV} -> {M, [{var, L, FV} | Stack]};
        false -> {M, [{var, L, Var} | Stack]}
    end;
apply_permutation_aux(Type, {M, Stack}) ->
    {Type1, Stack1} = list_utils:post_compose_type(Type, Stack),
    {M, [Type1|Stack1]}.
    
    
permutations([]) -> [[]];
permutations([{V,FVs}|Vars]) ->
    Perms = permutations(Vars),
    lists:append([ [[{V, FV}|Perm] || Perm <- Perms] || FV <- FVs ]).


% MACRO GENERATION
% ----------------

% This generates the macro of a function with a non-overloaded scheme
genmacro_overloaded_scheme(MGen, {{FunName, Arity}, [Scheme]}) ->
    MacroName = string:to_upper(atom_to_list(FunName) ++ 
        "_" ++ list_utils:integer_to_string(Arity)),
    {Macro, NumVars} = genmacro(MGen, MacroName, Arity, Scheme),
    {{FunName, Arity}, {MacroName, NumVars, [Macro]}};
    
% This generates the macro of a function with an overloaded scheme    
genmacro_overloaded_scheme(MGen, {{FunName, Arity}, OverloadedSpec}) ->
    N = length(OverloadedSpec),
    FGen = freshname_generator:new(),
    Pars = [variable(freshname_generator:fresh_name(FGen, "PAR")) 
                || _ <- lists:seq(1, Arity)],
    MacroBaseName = string:to_upper(atom_to_list(FunName) ++ 
        "_" ++ list_utils:integer_to_string(Arity)),
    {SubMacroEnv, Varss, MacroCalls} = lists:unzip3(lists:map(
        fun({M, Scheme}) -> 
            MacroName = MacroBaseName ++ "_" ++ 
                        list_utils:integer_to_string(M),
            {Macro, NumVars} = genmacro(MGen, MacroName, Arity, Scheme),
            Vars = [variable(freshname_generator:fresh_name(FGen, "F"))
                 || _ <- lists:seq(1, NumVars)],
            {{MacroName, Macro}, Vars, 
                macro(variable(MacroName), Pars ++ Vars)}
        end, lists:zip(lists:seq(1, N), OverloadedSpec))),
    {_, SubMacros} = lists:unzip(SubMacroEnv),
    TotalExtraVars = lists:append(Varss),
    Macro = attribute(abstract(define), 
        [application(variable(MacroBaseName), Pars ++ TotalExtraVars),
            macrocall_generator:gen_code(MGen, alt, MacroCalls)]),
    {{FunName, Arity}, {MacroBaseName, length(TotalExtraVars),
                        SubMacros ++ [Macro]}}.
    
        
    
% This generates the macro of each clause in a (possibly overloaded) scheme
genmacro(MGen, MacroName, Arity, Scheme) ->
    FGen = freshname_generator:new(),
    macrocall_generator:set_freshgen(MGen, FGen),
    Params = [ freshname_generator:fresh_name(FGen, "PAR") 
                    || _ <- lists:seq(1, Arity) ],
    ParamsVar = [variable(Param) || Param <- Params],
                    
    FVs = [ freshname_generator:fresh_name(FGen, "FRESH") || _ <- Params ],
    FVsVar = [variable(FV) || FV <- FVs],
                    
    
    FreshBindings = lists:zipwith(fun erl_syntax:match_expr/2, 
                                  FVsVar, ParamsVar),
    
    {TPars, TRes, Constraints} = decompose_scheme(Scheme),
    TParTypeVars = lists:append([free_variables(TPar) || TPar <- TPars]),
    
    As = [ freshname_generator:fresh_name(FGen, "A") || _ <- TParTypeVars ],
    AVars = [ variable(A) || A <- As ],
    APs = [ freshname_generator:fresh_name(FGen, "AP")  || _ <- TParTypeVars ],
    
    Eta = maps:from_list(lists:zip(TParTypeVars, [variable(A) || A <- As])),
    Theta = maps:from_list(lists:zip(TParTypeVars, 
                           [variable(AP) || AP <- APs])),

    ExpPars =
        lists:map(fun(TPar) ->
                    VarsToSet = [ maps:get(FreeVar, Theta)
                      || FreeVar <- free_variables(TPar) ],
                    tr_par(TPar, MGen, FGen, Eta, Theta, VarsToSet)
                 end, TPars),

    ParBindings = lists:zipwith(fun erl_syntax:match_expr/2, 
                                  FVsVar, ExpPars),              
                 
    CsBindings = [tr_constraint(C, MGen, FGen, Eta, Theta) || C <- Constraints],

    EtaP = maps:from_list(lists:zip(TParTypeVars, 
            [application(variable(AP), []) || AP <- APs])),

    ExpRes = tr_par(TRes, MGen, FGen, EtaP, Theta, []),
    
    GVsVar = [variable(GV) || GV <- freshname_generator:get_names(FGen)],
    
    Macro = attribute(abstract(define), 
        [application(variable(list_to_atom(MacroName)), GVsVar),
         block_expr(FreshBindings ++
                    [receive_expr([clause([tuple(AVars)], none, 
                        ParBindings ++ lists:append(CsBindings) ++
                         [ExpRes])])]
         )]),
    
    {Macro, length(GVsVar) - Arity}.
    
decompose_scheme({type, _, 'fun', [{type, _, product, Params}, Res]}) -> 
    {Params, Res, []};    
decompose_scheme({type, _, bounded_fun, [T, C]}) -> 
    {Params, Res, _} = decompose_scheme(T),
    {Params, Res, C}.

    
block_expr_if_needed([Exp]) ->  Exp;
block_expr_if_needed(Exps) ->  block_expr(Exps).
    
tr_par({var, _, Alpha}, MGen, _, Eta, Theta, VarsToSet) ->
    AVar = maps:get(Alpha, Eta),
    APrime = maps:get(Alpha, Theta),
    Bindings = lists:map(
            fun(VarToSet) ->
                Rhs = case VarToSet == APrime of
                          true -> fun_expr([clause([], none, [AVar])]);
                          false -> macrocall_generator:gen_code(MGen, 
                                                            none_closure, [])
                      end,
                match_expr(VarToSet, Rhs)
            end, VarsToSet),
    block_expr_if_needed(Bindings ++ [AVar]);
    
tr_par({type, _, integer, []}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par_comps([], MGen, FGen, Eta, Theta, VarsToSet, integer);
    
tr_par({type, _, float, []}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par_comps([], MGen, FGen, Eta, Theta, VarsToSet, float);

    
tr_par({type, _, union, Alts}, MGen, FGen, Eta, Theta, VarsToSet) ->
    AltExprs = [ tr_par(Alt, MGen, FGen, Eta, Theta, VarsToSet)
                    || Alt <- Alts ],
    macrocall_generator:gen_code(MGen, alt, AltExprs);

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
    
tr_par({type, _, 'fun', [{type, _, product, TPars}, TRes]},
        MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par_comps(TPars ++ [TRes], MGen, FGen, Eta, Theta, VarsToSet, 'fun');

tr_par({integer, _, N}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par_comps([], MGen, FGen, Eta, Theta, VarsToSet, {integer, N});

tr_par({atom, _, At}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par_comps([], MGen, FGen, Eta, Theta, VarsToSet, {atom, At});

tr_par({type, _, any, []}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par_comps([], MGen, FGen, Eta, Theta, VarsToSet, any);

tr_par({type, _, number, []}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par_comps([], MGen, FGen, Eta, Theta, VarsToSet, number);

tr_par({type, _, boolean, []}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par({type, 0, union, [{atom, 0, true}, {atom, 0, false}]}, 
                MGen, FGen, Eta, Theta, VarsToSet);

tr_par({paren_type, _, [T]}, MGen, FGen, Eta, Theta, VarsToSet) ->
    tr_par(T, MGen, FGen, Eta, Theta, VarsToSet);


tr_par(Type, MGen, _, _, _, _) -> 
    io:format("Unknown type: ~p. Using any()~n", [Type]),
%    io:format("Unknown type: ~s. Using any()~n", [list_utils:type_to_string(Type)]),
    macrocall_generator:gen_code(MGen, any, []).
    

    
tr_par_comps(Comps, MGen, FGen, Eta, Theta, VarsToSet, GenCallName) ->

    FreeVarsComps = [
        [ maps:get(V, Theta) ||  V <- free_variables(Comp) ]
            || Comp <- Comps],
    VarsToSetComp = 
        [ [ V || V <- VarsToSet, member(V, FVComp)]
            || FVComp <- FreeVarsComps ],
    MentionedVars = lists:append(VarsToSetComp),
    NotMentionedVars = [ V || V <- VarsToSet, not member(V, MentionedVars) ],

    CompsExprs = [
       tr_par(Comp, MGen, FGen, Eta, Theta, VarToSetComp)
        || {Comp, VarToSetComp} <- lists:zip(Comps, VarsToSetComp)
    ],

    NotMentionedAssignments = [
            match_expr(Var,
                       macrocall_generator:gen_code(MGen, none_closure, []))
        || Var <- NotMentionedVars
    ],
    
    LastExpr = macrocall_generator:gen_code(MGen, GenCallName, 
                                            CompsExprs),
    block_expr_if_needed(NotMentionedAssignments ++ [LastExpr]).
    
   
tr_constraint({type, _, constraint, [{atom, _, is_subtype}, [C1, C2]]}, 
                MGen, FGen, Eta, Theta) ->
    FV = freshname_generator:fresh_name(FGen, "C"),
    Expr1 = tr_par(C1, MGen, FGen, Eta, Theta, []),
    Expr2 = tr_par(C2, MGen, FGen, Eta, Theta, []),
    [match_expr(variable(FV), Expr1), match_expr(variable(FV), Expr2)].
    

% This replaces the specs of the program with their linearized versions.
normalize_form(NormEnv, Form) ->
    case is_directive(Form, spec) of
        true ->
            [Arg|_] = attribute_arguments(Form),
            {NameArity,_} = concrete(Arg),
            Form1 = 
                case lists:keyfind(NameArity, 1, NormEnv) of
                    {NameArity, NormType} -> 
                        attribute(abstract(spec), [tuple([abstract(NameArity), 
                            abstract(NormType)])]);
                    false -> Form
                end,
            add_ann(typespec, Form1);
        false -> Form
    end.

% It replaces the function calls in the environment with the corresponding
% macro calls.    
replace_calls(MacroEnv, Form, NoPolyCalls) ->
    case type(Form) of
        function -> 
            Name = concrete(function_name(Form)),
            Arity = function_arity(Form),
            case member({Name, Arity}, NoPolyCalls) of
                false ->
                    FGen = freshname_generator:new(),
                    erl_syntax_lib:map(
                        fun(Exp) -> replace_call(FGen, MacroEnv, Exp) end,
                    Form);
                true -> Form
            end;
        _ -> Form
    end.
    
replace_call(FGen, MacroEnv, Expr) -> 
    case type(Expr) of
        application ->
            case application_operator(Expr) of 
                {atom, _, FunName} ->
                    Args = application_arguments(Expr),
                    Arity = length(Args),
                    case lists:keyfind({FunName, Arity}, 1, MacroEnv) of
                        {_, {MacroName, NumVars, _}} -> 
                            FVars = [ 
                             variable(freshname_generator:fresh_name(FGen, ""))
                             || _ <- lists:seq(1, NumVars)
                            ],
                            receive_expr([
                                clause(
                                    [tuple(FVars)],
                                    none,
                                    [macro(variable(MacroName), Args ++ FVars)]
                                )
                            ]);
                        false -> Expr
                    end;
                _ -> Expr
            end;
        _ -> Expr
    end.
        
    
    
write_transformed(none, Forms, FileName) -> 
    FileNameRev = lists:reverse(FileName),
    [Dot] = ".",
    {ExtRev, NameRev} = lists:splitwith(fun(C) -> C /= Dot end, FileNameRev),
    NewName = case NameRev of
        [Dot|Rest] -> lists:reverse(Rest) ++ "_transformed" ++ [Dot] ++ 
                        lists:reverse(ExtRev);
        [] -> FileName ++ "_transformed"
    end,
    write_transformed(NewName, Forms, FileName);
write_transformed(FileName, Forms, _) -> 
    case file:open(FileName, [write]) of
        {ok, File} ->  
            [
                io:fwrite(File, "~s~n~n", 
                    [erl_prettypr:format(Form, [{hook, fun print_spec/3}])])
                || Form <- Forms
            ],
            io:format("Transformed program written into ~s~n", [FileName]);
        {error, Reason} -> 
            io:format("Cannot write output ~s: ~p~n", [FileName, Reason])
    end,
    FileName.


    
    
print_spec(Form, Ctx, Cont) -> 
    Anns = get_ann(Form),
    case member(typespec, Anns) of
        true -> 
            [{NameArity, Schemes}] = 
                [concrete(Arg) || Arg <- attribute_arguments(Form)],
            prettypr:text(list_utils:spec_to_string(
                {attribute, 0, spec, {NameArity, Schemes}}
            ));
        false -> Cont(Form, Ctx)
    end.
    
    


    

