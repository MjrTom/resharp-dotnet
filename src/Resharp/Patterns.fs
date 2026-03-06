// patterns, helpers
module internal rec Resharp.Patterns

open Resharp.Types
open System
open Resharp.Runtime

[<return: Struct>]
let (|PredStar|_|) (resolve: RegexNodeId -> RegexNode<_>) (nodeId: RegexNodeId) =
    match resolve nodeId with
    | Loop(node = body; field2 = 0; up = Int32.MaxValue) ->
        match resolve body with
        | Singleton pred -> ValueSome(pred)
        | _ -> ValueNone
    | _ -> ValueNone



[<return: Struct>]
let (|PredLoop|_|) (resolve: RegexNodeId -> RegexNode<_>) (nodeId: RegexNodeId) =
    match resolve nodeId with
    | Loop(node = body; field2 = low; up = up) ->
        match resolve body with
        | Singleton pred -> ValueSome(pred, low, up)
        | _ -> ValueNone
    | _ -> ValueNone

[<return: Struct>]
let (|PredStarHead|_|) (resolve: RegexNodeId -> RegexNode<_>) (nodeId: RegexNodeId) =
    match resolve nodeId with
    | Loop(node = body; field2 = 0; up = Int32.MaxValue) ->
        match resolve body with
        | Singleton pred -> ValueSome(pred)
        | _ -> ValueNone
    | Concat(node = head) ->
        match resolve head with
        | Loop(node = body; field2 = 0; up = Int32.MaxValue) ->
            match resolve body with
            | Singleton pred -> ValueSome(pred)
            | _ -> ValueNone
        | _ -> ValueNone
    | _ -> ValueNone

[<return: Struct>]
let (|LookbackPrefix|_|) (resolve: RegexNodeId -> RegexNode<_>) (nodeId: RegexNodeId) =
    match resolve nodeId with
    | LookBehind _ -> ValueSome(nodeId)
    | Concat(node = head) ->
        match resolve head with
        | LookBehind _ -> ValueSome(nodeId)
        | _ -> ValueNone
    | _ -> ValueNone

[<return: Struct>]
let (|HasPrefixLookback|_|) (getFlags: RegexNodeId -> NodeFlags) (nodeId: RegexNodeId) =
    let flags = getFlags nodeId
    if flags.HasPrefixLookbehind then
        ValueSome()
    else
        ValueNone

[<return: Struct>]
let (|HasSuffixLookahead|_|) (getFlags: RegexNodeId -> NodeFlags) (nodeId: RegexNodeId) =
    let flags = getFlags nodeId
    if flags.HasSuffixLookahead then
        ValueSome()
    else
        ValueNone



let (|ConcatSuffix|) (resolve: RegexNodeId -> RegexNode<_>) (nodeId: RegexNodeId) =
    let rec loop id =
        match resolve id with
        | Concat(node = _; field2 = tail) -> loop tail
        | _ -> id
    loop nodeId


let inline (|SplitTail|) (resolve: RegexNodeId -> RegexNode<_>) (nodeId: RegexNodeId) =
    let tmp = ResizeArray()

    let rec loop id =
        match resolve id with
        | Concat(node = h; field2 = tail) ->
            tmp.Add(h)
            loop tail
        | _ -> tmp, id

    loop nodeId


[<return: Struct>]
let (|StartsWithTrueStar|_|) (resolve: RegexNodeId -> RegexNode<_>) (solver: ISolver<_>) (nodeId: RegexNodeId) =
    let rec loop id =
        match resolve id with
        | Concat(node = head) ->
            match resolve head with
            | Loop(node = body; field2 = 0; up = Int32.MaxValue) ->
                match resolve body with
                | Singleton pred when solver.IsFull(pred) -> ValueSome()
                | _ -> ValueNone
            | _ -> ValueNone
        | Loop(node = body; field2 = 0; up = Int32.MaxValue) ->
            match resolve body with
            | Singleton pred when solver.IsFull(pred) -> ValueSome()
            | _ -> ValueNone
        | _ -> ValueNone

    loop nodeId

[<return: Struct>]
let (|EndsWithTrueStar|_|) (resolve: RegexNodeId -> RegexNode<_>) (solver: ISolver<_>) (nodeId: RegexNodeId) =
    let rec loop id =
        match resolve id with
        | Concat(node = _; field2 = tail) ->
            match resolve tail with
            | Loop(node = body; field2 = 0; up = Int32.MaxValue) ->
                match resolve body with
                | Singleton pred when solver.IsFull(pred) -> ValueSome()
                | _ -> ValueNone
            | _ -> loop tail
        | Loop(node = body; field2 = 0; up = Int32.MaxValue) ->
            match resolve body with
            | Singleton pred when solver.IsFull(pred) -> ValueSome()
            | _ -> ValueNone
        | _ -> ValueNone

    loop nodeId


