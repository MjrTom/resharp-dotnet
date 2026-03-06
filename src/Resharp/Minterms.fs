module internal Resharp.Minterms

open System
open System.Collections.Generic
open Resharp.Types
open Resharp.Common
open Resharp.Runtime
open Resharp.Internal

let rec transform
    (oldBuilder: RegexBuilder<BDD>)
    (builder: RegexBuilder<'tnewset>)
    (charsetSolver: CharSetSolver)
    (newSolver: ISolver<'tnewset>)
    (nodeId: RegexNodeId)
    : RegexNodeId =

    let inline transformInner v = transform oldBuilder builder charsetSolver newSolver v
    match oldBuilder.Node(nodeId) with
    | Singleton nodes -> builder.one(newSolver.ConvertFromBDD(oldBuilder.GetTSet(nodes[0]), charsetSolver))
    | Not nodes ->
        let xs = nodes[0]
        builder.mkNot(transformInner xs)
    | And (xs) ->
        use mutable vl = new ValueList<RegexNodeId>(xs.Length)
        for x in xs do vl.Add(transformInner x)
        vl.AsSpan().Sort()
        let mem = vl.ToArray()
        builder.mkAnd(mem)
    | Or (xs) ->
        use mutable vl = new ValueList<RegexNodeId>(xs.Length)
        for x in xs do vl.Add(transformInner x)
        vl.AsSpan().Sort()
        let mem = vl.ToArray()
        builder.mkOr(mem)
    | Loop nodes ->
        let body = transformInner nodes[0]
        let lower = nodes[1]
        let upper = nodes[2]
        builder.mkLoop(body,lower,upper)
    | LookAhead nodes ->
        if nodeId = oldBuilder.anchors._nonWordRight.Value then
            builder.anchors._nonWordRight.Value
        else
            let body = nodes[0]
            let rel = nodes[1]
            let pendingNullable = nodes[2]
            builder.mkLookaround(transformInner body,false,rel,oldBuilder.ResolveRefSet(pendingNullable))
    | LookBehind nodes ->
        if nodeId = oldBuilder.anchors._nonWordLeft.Value then
            builder.anchors._nonWordLeft.Value
        else
            let body = nodes[0]
            let rel = nodes[1]
            let pendingNullable = nodes[2]
            builder.mkLookaround(transformInner body,true,rel,oldBuilder.ResolveRefSet(pendingNullable))
    | Concat nodes ->
        let head = transformInner nodes[0]
        let tail = transformInner nodes[1]
        builder.mkConcat2(head,tail)
    | Begin -> RegexNodeId.BEGIN_ANCHOR
    | End -> RegexNodeId.END_ANCHOR



let rec transformBack
    (bdds:BDD[])
    (oldBuilder: RegexBuilder<'t>)
    (builder: RegexBuilder<BDD>)
    (newSolver: ISolver<'t>)
    (charsetSolver: CharSetSolver)

    (nodeId: RegexNodeId)
    : RegexNodeId =

    let inline transformInner v = transformBack bdds oldBuilder builder newSolver charsetSolver v
    match oldBuilder.Node(nodeId) with
    | Singleton nodes ->
        let bdd : BDD = newSolver.ConvertToBDD(oldBuilder.GetTSet(nodes[0]), charsetSolver)
        builder.one(bdd)
    | Not nodes ->
        let xs = nodes[0]
        builder.mkNot(transformInner xs)
    | And (xs) ->
        use mutable vl = new ValueList<RegexNodeId>(xs.Length)
        for x in xs do vl.Add(transformInner x)
        vl.AsSpan().Sort()
        let mem = vl.ToArray()
        builder.mkAnd(mem)
    | Or (xs) ->
        use mutable vl = new ValueList<RegexNodeId>(xs.Length)
        for x in xs do vl.Add(transformInner x)
        vl.AsSpan().Sort()
        let mem = vl.ToArray()
        builder.mkOr(mem)
    | Loop nodes ->
        let body = transformInner nodes[0]
        let lower = nodes[1]
        let upper = nodes[2]
        builder.mkLoop(body,lower,upper)
    | LookAhead nodes ->
        let body = nodes[0]
        let rel = nodes[1]
        let pendingNullable = nodes[2]
        builder.mkLookaround(transformInner body,false,rel,oldBuilder.ResolveRefSet(pendingNullable))
    | LookBehind nodes ->
        let body = nodes[0]
        let rel = nodes[1]
        let pendingNullable = nodes[2]
        builder.mkLookaround(transformInner body,true,rel,oldBuilder.ResolveRefSet(pendingNullable))
    | Concat nodes ->
        let head = transformInner nodes[0]
        let tail = transformInner nodes[1]
        builder.mkConcat2(head,tail)
    | Begin -> RegexNodeId.BEGIN_ANCHOR
    | End -> RegexNodeId.END_ANCHOR

let collectSets (builder: RegexBuilder<'tset>) (nodeId: RegexNodeId) =
    let hs = HashSet()
    let rec collect (id: RegexNodeId) : unit =
        match builder.Node(id) with
        | Singleton nodes -> hs.Add (builder.GetTSet(nodes[0])) |> ignore
        | And (nodes=xs)
        | Or (nodes=xs) -> for x in xs do collect x
        | LookAhead nodes
        | LookBehind nodes
        | Not nodes
        | Loop nodes -> collect nodes[0]
        | Concat nodes ->
            collect nodes[0]
            collect nodes[1]
        | Begin | End -> ()
    collect nodeId
    hs

let compute (solver: ISolver<'tset>) (builder: RegexBuilder<'tset>) (nodeId: RegexNodeId) =
    let hs = collectSets builder nodeId
    let list = MintermGenerator<'tset>.GenerateMinterms (solver, hs)
    list.Sort()
    list.ToArray()

let createLookupUtf16 (bdds:BDD[]) =
    let arr = Array.zeroCreate<byte> (int UInt16.MaxValue + 1)
    if bdds.Length = 1 then arr else
    for mtId = 1 to bdds.Length - 1 do
        let bdd = bdds[mtId]
        let ranges = BDDRangeConverter.ToRanges(bdd)
        for rstart,rend in ranges do
            let slice = arr.AsSpan(int rstart, int (rend - rstart + 1u))
            slice.Fill(byte mtId)
    arr
