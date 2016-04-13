%%===========================================================================================
%% @doc
%% Miscellaneous utilities related to lists and ASTs representing types.
%% @end
%%
%% @author Francisco Javier López-Fraguas <fraguas@sip.ucm.es>
%% @author Manuel Montenegro <montenegro@fdi.ucm.es>
%% @author Juan Rodríguez-Hortalá <juanrh@fdi.ucm.es>
%% @copyright 2015
%%===========================================================================================
-module(list_utils).
-author("Francisco Javier López-Fraguas").
-author("Manuel Montenegro").
-author("Juan Rodríguez-Hortalá").
-export([
    unfoldr/2, unfoldl/2, integer_to_string/1, type_to_string/1,
    spec_to_string/1, fold_type/4, post_compose_type/2, nub/1, difference/2
]).

%%===========================================================================================
%% Types
%%===========================================================================================

-type ast() :: term().

%%===========================================================================================
%% Functions
%%===========================================================================================

%% @doc
%% It successively applies a function F on an initial value and collects the
%% results in a list. The value Init is the initial seed value.
%% The function F receives this seed value, and it may return:
%% <ul>
%%  <li> A value `{ok, Val, Next}'. In this case `Val' will be added to the
%%    resulting list and `Next' will be the next element to be passed to F.</li>
%%  <li>The atom `none', which means that no more elements will be generated.</li>
%% </ul>
%% @spec
%% unfoldr(fun((A) -> {ok, B, A} | none), Init :: A) -> [B]
%% @end
%%-------------------------------------------------------------------------------------------
-spec unfoldr(fun((A) -> {ok, B, A} | none), Init :: A) -> [B].
unfoldr(F, Init) -> unfold(F, Init, []).

%%-------------------------------------------------------------------------------------------
%% @doc
%% Similar to {@link unfoldr}, but the resulting list is reversed.
%% @spec
%% unfoldl(fun((A) -> {ok, B, A} | none), Init :: A) -> [B]
%% @end
%%-------------------------------------------------------------------------------------------
-spec unfoldl(fun((A) -> {ok, B, A} | none), Init :: A) -> [B].
unfoldl(F, Init) -> lists:reverse(unfold(F, Init, [])).


%%-------------------------------------------------------------------------------------------
%% @private
%% @doc
%% It successively applies a function F on an initial value and collects the
%% results in a list. The value Init is the initial seed value.
%% @spec
%% unfold(fun((A) -> {ok, B, A} | none), Init :: A, Ac :: [B]) -> [B]
%% @end
%%-------------------------------------------------------------------------------------------
-spec unfold(fun((A) -> {ok, B, A} | none), Init :: A, Ac :: [B]) -> [B].
unfold(F, Init, Ac) ->
    case F(Init) of
        {ok, Val, Next} -> unfold(F, Next, [Val|Ac]);
        none -> Ac
    end.


%%-------------------------------------------------------------------------------------------
%% @doc
%% It converts an integer into its base 10 representation as a string.
%% @spec
%% integer_to_string(integer()) -> string()
%% @end
%%-------------------------------------------------------------------------------------------
-spec integer_to_string(integer()) -> string().
integer_to_string(0) -> "0";
integer_to_string(Number) ->
    unfoldr(
        fun (0) -> none;
            (N) when N > 0 -> {ok, digit_to_string(N rem 10), N div 10}
        end,
        Number
    ).

%%-------------------------------------------------------------------------------------------
%% @private
%% @doc
%% It converts a digit into its base 10 representation as a character.
%% @spec
%% digit_to_string(integer()) -> integer()
%% @end
%%-------------------------------------------------------------------------------------------
-spec digit_to_string(integer()) -> integer().
digit_to_string(N) -> N + 48.

%%-------------------------------------------------------------------------------------------
%% @doc
%% It pretty-prints the type passed as parameter.
%% @spec
%% type_to_string (ast()) -> string()
%% @end
%%-------------------------------------------------------------------------------------------
-spec type_to_string (ast()) -> string().
type_to_string(Type) ->
    % Since the pretty printer cannot handle isolated types, but types contained
    % within specs, we embed the given type into a spec, pretty-print the whole
    % spec, and then obtain the type from the latter representation.
    SpecStr = lists:flatten(erl_pp:form({attribute, 0, spec, 
            {{f,1},[{type, 0, 'fun', [{type, 0, product, []}, Type]}]}})),
    {_, StrEnd} = lists:split(13, SpecStr),
    StrEndRev = lists:reverse(StrEnd),
    [_|TypeStrRev] = lists:takewhile(fun(C) -> C /= "." end, StrEndRev),
    lists:reverse(TypeStrRev).

%%-------------------------------------------------------------------------------------------
%% @doc
%% It pretty-prints the given type specification.
%% @spec
%% spec_to_string (ast()) -> string()
%% @end
%%-------------------------------------------------------------------------------------------
-spec spec_to_string (ast()) -> string().    
spec_to_string(Spec) -> lists:droplast(lists:flatten(erl_pp:form(Spec))).

%%-------------------------------------------------------------------------------------------
%% @doc
%% It performs a pre-post-order traversal of the AST corresponding to a type.
%%
%% This is done as the `erl_syntax_lib' module (see 
%% [http://erlang.org/doc/man/erl_syntax_lib.html])
%% cannot handle this kind of ASTs.
%%
%% The traversal carries an accumulator. The `FPre' allows one to modify
%% the accumulator when entering a node from its father, whereas `FPost' is
%% called when leaving a node after traversing its children.
%% @spec
%% fold_type(FPre :: fun((Type :: ast(), State :: term()) -> term()),
%%           FPost :: fun((Type :: ast(), State :: term()) -> term()),
%%           InitialState :: term(), Type :: ast()) -> term()
%% @end
%%-------------------------------------------------------------------------------------------
-spec fold_type(FPre :: fun((Type :: ast(), State :: term()) -> term()),
                FPost :: fun((Type :: ast(), State :: term()) -> term()),
                InitialState :: term(), Type :: ast()) -> term().
fold_type(FPre, FPost, St, {ann_type, _, [_,Type]} = T) ->
    FPost(T, fold_type(FPre, FPost, FPre(T, St), Type));
fold_type(FPre, FPost, St, {paren_type, _, Types} = T) ->
    FPost(T, fold_type_list(FPre, FPost, FPre(T, St), Types));
fold_type(FPre, FPost, St, {type, _, record, [_]} = T) ->
    FPost(T, FPre(T, St));
fold_type(FPre, FPost, St, {type, _, record, [_, Types]} = T) ->
    FPost(T, fold_type_list(FPre, FPost, FPre(T, St), Types));
fold_type(FPre, FPost, St, {type, _, field_type, [_, Type]} = T) ->
    FPost(T, fold_type(FPre, FPost, FPre(T, St), Type));
fold_type(FPre, FPost, St, {type, _, binary, [{integer,_,0}, {integer,_,0}]} = T) ->
    FPost(T, FPre(T, St));
fold_type(FPre, FPost, St, {type, _, binary, [Type, {integer,_,0}]} = T) ->
    FPost(T, fold_type(FPre, FPost, FPre(T, St), Type));
fold_type(FPre, FPost, St, {type, _, binary, [{integer,_,0}, Type]} = T) ->
    FPost(T, fold_type(FPre, FPost, FPre(T, St), Type));
fold_type(FPre, FPost, St, {type, _, binary, [Type1, Type2]} = T) ->
    FPost(T, fold_type(FPre, FPost,  fold_type(FPre, FPost, FPre(T, St), Type1), Type2));
fold_type(FPre, FPost, St, {type, _, 'fun', [{type, _, product, []}, Type]} = T) ->
    FPost(T, fold_type(FPre, FPost, FPre(T, St), Type));
fold_type(FPre, FPost, St, {type, _, _, any} = T) ->
    FPost(T, FPre(T, St));
fold_type(FPre, FPost, St, {type, _, _, Types} = T) ->
    FPost(T, fold_type_list(FPre, FPost, FPre(T, St), Types));
fold_type(FPre, FPost, St, {user_type, _, _, Types} = T) ->
    FPost(T, fold_type_list(FPre, FPost, FPre(T, St), Types));
fold_type(FPre, FPost, St, {remote_type, _, [_,_,Types]} = T) ->
    FPost(T, fold_type_list(FPre, FPost, FPre(T, St), Types));
fold_type(FPre, FPost, St, {op, _, _, Type} = T) ->
    FPost(T, fold_type(FPre, FPost, FPre(T, St), Type));
fold_type(FPre, FPost, St, {var, _, _} = T) ->
    FPost(T, FPre(T, St));
fold_type(FPre, FPost, St, T) ->
    FPost(T, FPre(T, St)).

%%-------------------------------------------------------------------------------------------
%% @private
%% @doc
%% It performs a pre-post-order traversal of the AST corresponding to a list type.
%% @end
%%-------------------------------------------------------------------------------------------
fold_type_list(FPre, FPost, St, Types) ->
    lists:foldl(fun(T, S) -> fold_type(FPre, FPost, S, T) end, St, Types).

%%-------------------------------------------------------------------------------------------
%% @doc
%% It replaces the children of the type given as first parameter with
%% the elements of the list given as second parameter.
%% @spec
%% post_compose_type(ast(), [ast()]) -> ast()
%% @end
%%-------------------------------------------------------------------------------------------
-spec post_compose_type(ast(), [ast()]) -> ast().
post_compose_type({ann_type, L, [Name, _]}, [T|St]) ->
    {{ann_type, L, [Name, T]}, St};
post_compose_type({paren_type, L, Ts}, St) ->
    {St1, St2} = reverse_split(length(Ts), St),
    {{paren_type, L, St1}, St2};
post_compose_type({type, L, record, [N, Ts]}, St) ->
    {St1, St2} = reverse_split(length(Ts), St),
    {{type, L, record, [N, St1]}, St2};
post_compose_type({type, L, field_type, [N, _]}, [T|St]) ->
    {{type, L, field_type, [N, T]}, St};
post_compose_type({type, _, binary, [{integer,_,0}, {integer,_,0}]} = T, St) ->
    {T, St};
post_compose_type({type, L, binary, [_, {integer, L1, 0}]}, [T|St]) ->
    {{type, L, binary, [T, {integer, L1, 0}]}, St};
post_compose_type({type, L, binary, [{integer,L1,0}, _]}, [T|St]) ->
    {{type, L, binary, [{integer,L1,0}, T]}, St};
post_compose_type({type, L, binary, [_, _]}, [T2,T1|St]) ->
    {{type, L, binary, [T1, T2]}, St};
post_compose_type({type, L, 'fun', [{type, L1, product, []}, _]}, [T|St]) ->
    {{type, L, 'fun', [{type, L1, product, []}, T], St}};
post_compose_type({type, _, _, any} = T, St) ->
    {T, St};
post_compose_type({type, L, F, Ts}, St) ->
    {St1, St2} = reverse_split(length(Ts), St),
    {{type, L, F, St1}, St2};
post_compose_type({user_type, L, F, Ts}, St) ->
    {St1, St2} = reverse_split(length(Ts), St),
    {{user_type, L, F, St1}, St2};
post_compose_type({remote_type, L, F, [M, F, Ts]}, St) ->
    {St1, St2} = reverse_split(length(Ts), St),
    {{remote_type, L, F, [M, F, St1]}, St2};
post_compose_type({op, L, Op, _}, [T|St]) ->
    {{op, L, Op, T}, St};
post_compose_type({var, _, _} = T, St) ->
    {T, St};
post_compose_type(T, St) ->
    {T, St}.

%%-------------------------------------------------------------------------------------------
%% @private
%% @doc
%% Splits a list in two giving the maximum number of elements of the first one.
%% @spec
%% reverse_split(number(), [T]) -> {[T], [T]} when T::any()
%% @end
%%-------------------------------------------------------------------------------------------
-spec reverse_split(number(), [T]) -> {[T], [T]} when T::any().
reverse_split(N, Xs) -> reverse_split(N, [], Xs).

%%-------------------------------------------------------------------------------------------
%% @private
%% @doc
%% Splits a list in two giving the maximum number of elements of the first one.
%% @spec
%% reverse_split(number(), [T], [T]) -> {[T], [T]} when T::any()
%% @end
%%-------------------------------------------------------------------------------------------
-spec reverse_split(number(), [T], [T]) -> {[T], [T]} when T::any().
reverse_split(0, Ac, Xs) -> {Ac, Xs};
reverse_split(N, Ac, [X|Xs]) when N > 0 -> reverse_split(N-1, [X|Ac], Xs).

%%-------------------------------------------------------------------------------------------
%% @doc
%% Gets a list with all the elements without repetitions.
%% @spec
%% nub([T]) -> [T] when T::any()
%% @end
%%-------------------------------------------------------------------------------------------
-spec nub([T]) -> [T] when T::any().
nub([]) -> [];
nub([X|Xs]) -> [X | nub([Z || Z <- Xs, Z =/= X])].

%%-------------------------------------------------------------------------------------------
%% @doc
%% Gets the elements in the first list that aren't members in the second one.
%% @spec
%% difference([T1], [T2]) -> [T1] when T1::any(), T2::any()
%% @end
%%-------------------------------------------------------------------------------------------
-spec difference([T1], [T2]) -> [T1] when T1::any(), T2::any().
difference(Xs, Ys) -> [X || X <- Xs, not lists:member(X, Ys)].
