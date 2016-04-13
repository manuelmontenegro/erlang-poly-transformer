%%===========================================================================================
%% @doc
%% Tools for traversing Erlang terms represented by their Abstract form.
%% @end
%%
%% @reference <a href="http://www.erlang.org/doc/apps/erts/absform.html">Definition of
%%            erlang abstract format</a>
%% @author Manuel Montenegro <montenegro@fdi.ucm.es>
%%===========================================================================================
-module(parser_utils).
-author("Manuel Montenegro").
-export([
    replace_with_subexpressions/2, fold_expression/4
]).
-export_type([
    expression/0
]).

%%===========================================================================================
%% Types
%%===========================================================================================

%%-------------------------------------------------------------------------------------------
%% @doc
%% @type expression().
%% Abstract form of an Erlang expression.
%% @end
%%-------------------------------------------------------------------------------------------
-type expression() :: tuple().

%%===========================================================================================
%% Functions
%%===========================================================================================

%%-------------------------------------------------------------------------------------------
%% @private
%% @doc
%% Given an expression in the form of a tuple, it returns the positions of the tuple
%% which contain the child subexpressions.
%% @spec
%% subexpressions(expression()) -> list(integer())
%% @end
%%-------------------------------------------------------------------------------------------
-spec subexpressions(expression()) -> list(integer()).
subexpressions({match, _, _, _}) -> [3, 4];
subexpressions({tuple, _, _}) -> [3];
subexpressions({cons, _, _, _}) -> [3, 4];
subexpressions({bin,_, _}) -> [3];
subexpressions({bin_element, _, _, _, _}) -> [3];
subexpressions({op, _, _, _, _}) -> [4, 5];
subexpressions({op, _, _, _}) -> [4];
subexpressions({record, _, _, _}) -> [4];    
subexpressions({record, _, _, _, _}) -> [3, 5];
subexpressions({record_index, _, _, _}) -> [4];
subexpressions({record_field, _, _, _}) -> [3, 4];
subexpressions({record_field, _, _, _, _}) -> [3, 5];
subexpressions({map, _, _}) -> [3];
subexpressions({map_field_assoc, _, _, _}) -> [3, 4];
subexpressions({map_field_exact, _, _, _}) -> [3, 4];
subexpressions({map, _, _, _}) -> [3, 4];
subexpressions({'catch', _, _}) -> [3];
subexpressions({call, _, _, _}) -> [3, 4];
subexpressions({remote, _, _, _}) -> [3, 4];
subexpressions({lc, _, _, _}) -> [3, 4];
subexpressions({bc, _, _, _}) -> [3 ,4];
subexpressions({generate, _, _, _}) -> [3, 4];
subexpressions({b_generate, _, _, _}) -> [3, 4];
subexpressions({block, _, _}) -> [3];
subexpressions({'if', _, _}) -> [3];
subexpressions({'case', _, _, _}) -> [3, 4];
subexpressions({'try', _, _, _, _, _}) -> [3, 4, 5, 6];
subexpressions({'receive', _, _}) -> [3];
subexpressions({'receive', _, _, _, _}) -> [3, 4, 5];
subexpressions({'fun', _, {clauses, _}}) -> [3];
subexpressions({clauses, _}) -> [2];
subexpressions({'query', _, _}) -> [3];
subexpressions({clause, _, _, _, _}) -> [3, 4, 5];
subexpressions(_) -> [].

%%-------------------------------------------------------------------------------------------
%% @doc
%% It replaces the subexpressions of a given expression (or list) by the expressions
%% given as second parameter.
%% 
%% This is an utility function to be used between the transformer functions of
%% fold_expression/4.
%%
%% Note: This function has an overloaded spec. If you give an expression (resp. list
%% of expressions), you will be returned an expression (resp. list of expressions).
%%
%% @see fold_expression/4
%% @spec
%% replace_with_subexpressions(expression(), [expression()]) -> expression();
%%                            ([expression()], [expression()]) -> [expression()]
%% @end
%%-------------------------------------------------------------------------------------------
-spec replace_with_subexpressions(expression(), [expression()]) -> expression();
                                 ([expression()], [expression()]) -> [expression()].
replace_with_subexpressions([], []) -> [];
replace_with_subexpressions(Exp, NewExps) when is_list(Exp) -> NewExps;
replace_with_subexpressions(Exp, NewExps) when is_tuple(Exp) ->
       Indices = subexpressions(Exp),
       IndExps = lists:zip(Indices, NewExps),
       lists:foldl(fun({Idx, NewExp}, T) -> setelement(Idx, T, NewExp) end, Exp, IndExps).

%%-------------------------------------------------------------------------------------------
%% @doc
%% Traverses an Erlang expression (or a list of expressions) given by its abstract form.
%%
%% An accumulator is propagated and modified through the traversal.
%%
%% The first parameter is a combinator function. It combines the results of the subexpressions
%% and returns the value corresponding to the parent expression with the next state of the
%% accumulator.
%%
%% The second parameter is the accumulator transformer. It is called before traversing the first
%% child, and between the traversal of subsequent childs. It receives the parent expression, the
%% position of the last child visited, the last child visited itself, the current state of the
%% accumulator, and the partial results obtained for each child visited so far. It must return
%% the next state of the accumulator.
%%
%% Note: This function has an overloaded spec. If you give an expression (resp. list of
%%       expressions), you will be returned an expression (resp. list of expressions).
%% @spec
%% fold_expression(F::fun((expression(), A, [B]) -> {B, A}),
%%                 AccTransformer::fun((expression(), integer(), expression(), A, [B]) -> A),
%%                 InitAcc::A, Expr::expression()) -> {B, A};
%%                (F::fun(([expression()], A, [B]) -> {B, A}),
%%                 AccTransformer::fun(([expression()], integer(), expression(), A, [B]) -> A),
%%                 InitAcc::A, Expr::[expression()]) -> A.
%% @end
%%-------------------------------------------------------------------------------------------
-spec fold_expression(F::fun((expression(), A, [B]) -> {B, A}),
                      AccTransformer::fun((expression(), integer(), expression(), A, [B]) -> A),
                      InitAcc::A, Expr::expression()) -> {B, A};
                     (F::fun(([expression()], A, [B]) -> {B, A}),
                      AccTransformer::fun(([expression()], integer(), expression(), A, [B]) -> A),
                      InitAcc::A, Expr::[expression()]) -> A.
fold_expression(F, AccTransformer, InitAcc, Exprs) when is_list(Exprs) ->
    StartAcc = AccTransformer(Exprs, 0, none, InitAcc, []),
    {_, ResultsRev, LastAcc} = 
        lists:foldl(fun(Expr, {ChildNo, ResList, CurAcc}) ->
                        {Res, IntermediateAcc} = fold_expression(F, AccTransformer, CurAcc, Expr),
                        NextList = [Res | ResList],
                        NextAcc = AccTransformer(Exprs, ChildNo, Expr, IntermediateAcc, NextList),
                        {ChildNo + 1, NextList, NextAcc}
                    end, {1, [], StartAcc},  Exprs),
    F(Exprs, LastAcc, lists:reverse(ResultsRev));
fold_expression(F, AccTransformer, InitAcc, ParentExpr) when is_tuple(ParentExpr) -> 
    Indices = subexpressions(ParentExpr),
    SubExprs = lists:map(fun(Index) -> element(Index, ParentExpr) end, Indices),
    StartAcc = AccTransformer(ParentExpr, 0, none, InitAcc, []),
    {_, ResultsRev, LastAcc} = 
        lists:foldl(fun(Expr, {ChildNo, ResList, CurAcc}) ->
                        {Res, IntermediateAcc} = fold_expression(F, AccTransformer, CurAcc, Expr),
                        NextList = [Res | ResList],
                        NextAcc = AccTransformer(ParentExpr, ChildNo, Expr, IntermediateAcc, NextList),
                        {ChildNo + 1, NextList, NextAcc}
                    end, {1, [], StartAcc},  SubExprs),
    F(ParentExpr, LastAcc, lists:reverse(ResultsRev)).
