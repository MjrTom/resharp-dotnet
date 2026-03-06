// patterns, helpers
module internal rec Resharp.Patterns

open Resharp.Types
open System
open Resharp.Runtime

[<return: Struct>]
let (|PredStar|_|) (getTset: int -> 'tset) (resolve: RegexNodeId -> RegexNode<'tset>) (nodeId: RegexNodeId) =
    match resolve nodeId with
    | Loop nodes when nodes[1] = 0 && nodes[2] = Int32.MaxValue ->
        let body = nodes[0]
        match resolve body with
        | Singleton nodes -> ValueSome(getTset nodes[0])
        | _ -> ValueNone
    | _ -> ValueNone



[<return: Struct>]
let (|PredLoop|_|) (getTset: int -> 'tset) (resolve: RegexNodeId -> RegexNode<'tset>) (nodeId: RegexNodeId) =
    match resolve nodeId with
    | Loop nodes ->
        let body = nodes[0]
        let low = nodes[1]
        let up = nodes[2]
        match resolve body with
        | Singleton nodes -> ValueSome(getTset nodes[0], low, up)
        | _ -> ValueNone
    | _ -> ValueNone

[<return: Struct>]
let (|PredStarHead|_|) (getTset: int -> 'tset) (resolve: RegexNodeId -> RegexNode<'tset>) (nodeId: RegexNodeId) =
    match resolve nodeId with
    | Loop nodes when nodes[1] = 0 && nodes[2] = Int32.MaxValue ->
        let body = nodes[0]
        match resolve body with
        | Singleton nodes -> ValueSome(getTset nodes[0])
        | _ -> ValueNone
    | Concat nodes ->
        let head = nodes[0]
        match resolve head with
        | Loop nodes when nodes[1] = 0 && nodes[2] = Int32.MaxValue ->
            let body = nodes[0]
            match resolve body with
            | Singleton nodes -> ValueSome(getTset nodes[0])
            | _ -> ValueNone
        | _ -> ValueNone
    | _ -> ValueNone

[<return: Struct>]
let (|LookbackPrefix|_|) (resolve: RegexNodeId -> RegexNode<_>) (nodeId: RegexNodeId) =
    match resolve nodeId with
    | LookBehind _ -> ValueSome(nodeId)
    | Concat nodes ->
        let head = nodes[0]
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
        | Concat nodes -> loop nodes[1]
        | _ -> id
    loop nodeId


let inline (|SplitTail|) (resolve: RegexNodeId -> RegexNode<_>) (nodeId: RegexNodeId) =
    let tmp = ResizeArray()

    let rec loop id =
        match resolve id with
        | Concat nodes ->
            let h = nodes[0]
            let tail = nodes[1]
            tmp.Add(h)
            loop tail
        | _ -> tmp, id

    loop nodeId


[<return: Struct>]
let (|StartsWithTrueStar|_|) (getTset: int -> 'tset) (resolve: RegexNodeId -> RegexNode<'tset>) (solver: ISolver<'tset>) (nodeId: RegexNodeId) =
    let rec loop id =
        match resolve id with
        | Concat nodes ->
            let head = nodes[0]
            match resolve head with
            | Loop nodes when nodes[1] = 0 && nodes[2] = Int32.MaxValue ->
                let body = nodes[0]
                match resolve body with
                | Singleton nodes when solver.IsFull(getTset nodes[0]) -> ValueSome()
                | _ -> ValueNone
            | _ -> ValueNone
        | Loop nodes when nodes[1] = 0 && nodes[2] = Int32.MaxValue ->
            let body = nodes[0]
            match resolve body with
            | Singleton nodes when solver.IsFull(getTset nodes[0]) -> ValueSome()
            | _ -> ValueNone
        | _ -> ValueNone

    loop nodeId

[<return: Struct>]
let (|EndsWithTrueStar|_|) (getTset: int -> 'tset) (resolve: RegexNodeId -> RegexNode<'tset>) (solver: ISolver<'tset>) (nodeId: RegexNodeId) =
    let rec loop id =
        match resolve id with
        | Concat nodes ->
            let tail = nodes[1]
            match resolve tail with
            | Loop nodes when nodes[1] = 0 && nodes[2] = Int32.MaxValue ->
                let body = nodes[0]
                match resolve body with
                | Singleton nodes when solver.IsFull(getTset nodes[0]) -> ValueSome()
                | _ -> ValueNone
            | _ -> loop tail
        | Loop nodes when nodes[1] = 0 && nodes[2] = Int32.MaxValue ->
            let body = nodes[0]
            match resolve body with
            | Singleton nodes when solver.IsFull(getTset nodes[0]) -> ValueSome()
            | _ -> ValueNone
        | _ -> ValueNone

    loop nodeId


