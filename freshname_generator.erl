
%%
%% @doc Functions for creating and manipulating fresh name generators.
%%
%% Each generator is a process with an internal state that changes with
%% each name generation. This state is hidden from the programmer, so the
%% functions shown here are not purely functional.
%%
%% Each fresh name is preceded by a prefix. The generator will append the
%% string `_N' to this prefix, where `N' is an unique number. This number
%% cannot be repeated for a given prefix, but it may occur twice when applied
%% to different prefixes. For instance, when using the prefix `F', the 
%% successive calls to {@link fresh_name} will result in the names `F_1', 
%% `F_2', `F_3', etc.
%%
%% @author Francisco Javier López-Fraguas <fraguas@sip.ucm.es>
%% @author Manuel Montenegro <montenegro@fdi.ucm.es>
%% @author Juan Rodríguez-Hortalá <juanrh@fdi.ucm.es>
%% @copyright 2015

-module(freshname_generator).

-import(list_utils, [integer_to_string/1]).

-export([init/1, handle_call/3, handle_cast/2, handle_info/2, terminate/2, 
        code_change/3, new/0, stop/1, fresh_name/2, get_names/1]).

-export_type([fn_gen/0]).

-type fn_gen() :: pid().

-behaviour(gen_server).

% The fresh name generator is implemented as a gen_server, whose internal
% state is a tuple with two components:
%
% * A map associating each prefix with the suffix number to be generated for
%   the next name
% * The list of generated names.

%% @hidden
init(_) -> {ok, {maps:new(), []}}.


%% @hidden
handle_call({fresh_name, Prefix}, _, {Map, GenNames}) -> 
    Counter = maps:get(Prefix, Map, 1),
    FreshName = Prefix ++ "_" ++ integer_to_string(Counter),
    {reply, FreshName, 
        {maps:put(Prefix, Counter + 1, Map), [FreshName|GenNames]}};
        
handle_call(get_names, _, {_, GenNames} = State) ->
    {reply, lists:reverse(GenNames), State}.

%% @hidden
handle_cast(stop, State) -> {stop, normal, State}.
    
%% @hidden
handle_info(Info, State) ->
    io:format("Freshname generator: unexpected message ~p~n", [Info]),
    {noreply, State}.
    
%% @hidden
terminate(_, _) -> ok.

%% @hidden
code_change(_, _, State) -> {ok, State}.

%% @doc It generates a new fresh name generator. Each fresh name generator
%% is guaranteed not to produce the same fresh name twice.
-spec new() -> fn_gen().
new() -> {ok, P} = gen_server:start(?MODULE, none, []), P.
    
%% @doc It releases the given fresh name generator.
-spec stop(fn_gen()) -> ok.
stop(Gen) -> gen_server:cast(Gen, stop).

%% @doc It generates a fresh name with a given prefix.
%%
%% The fresh names take the form `Prefix_N' where `N' is an uniquely generated
%% number for that prefix.
-spec fresh_name(fn_gen(), Prefix :: string()) -> string().
fresh_name(Gen, Prefix) -> gen_server:call(Gen, {fresh_name, Prefix}).

%% @doc It obtains the fresh names generated so far.
%%
%% The names of the returned list respect the order in which these were generated.
-spec get_names(fn_gen()) -> [string()].
get_names(Gen) -> gen_server:call(Gen, get_names).
