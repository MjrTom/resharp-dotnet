namespace rec Resharp.Types

open Microsoft.FSharp.Core
open Resharp
open System
open System.Buffers
open System.Collections.Generic
open System.Runtime.CompilerServices

open System.Diagnostics
open Resharp.Common
open Resharp.Runtime

type UnsupportedPatternException(msg: string) =
    inherit System.Exception(msg)

// there's 3 kinds of locations that influence
// the derivative or nullability of a regex
type internal LocationKind =
    | Begin = 0uy
    | Center = 1uy
    | End = 2uy

type internal NullKind =
    | NotNull = Byte.MaxValue
    | CurrentNull = 0uy // {0}
    // special cases for common nullability kinds like anchors
    | PrevNull = 1uy // {1}
    | Nulls01 = 2uy // {0,1}, special casing ^, $ or word boundary
    | PendingNull = 4uy // {any number of nulls}

type internal SkipKind =
    | NotSkip = Byte.MaxValue
    | SkipInitial = 0uy
    | SkipActive = 1uy

[<Flags>]
type internal NodeFlags =
    | None = 0x0uy
    | CanBeNullableFlag = 0x1uy
    | IsAlwaysNullableFlag = 0x2uy
    | ContainsLookaroundFlag = 0x4uy
    | DependsOnAnchorFlag = 0x8uy
    | HasSuffixLookaheadFlag = 0x10uy
    | HasPrefixLookbehindFlag = 0x20uy

[<AutoOpen>]
module internal RegexNodeFlagsExtensions =
    type NodeFlags with
        member inline this.Has other = this &&& other <> NodeFlags.None

        member this.IsAlwaysNullable =
            this &&& NodeFlags.IsAlwaysNullableFlag <> NodeFlags.None

        member this.CanBeNullable = this &&& NodeFlags.CanBeNullableFlag <> NodeFlags.None

        member this.ContainsLookaround =
            this &&& NodeFlags.ContainsLookaroundFlag = NodeFlags.ContainsLookaroundFlag

        member this.HasSuffixLookahead =
            this &&& NodeFlags.HasSuffixLookaheadFlag = NodeFlags.HasSuffixLookaheadFlag

        member this.HasPrefixLookbehind =
            this &&& NodeFlags.HasPrefixLookbehindFlag = NodeFlags.HasPrefixLookbehindFlag

        member this.DependsOnAnchor =
            this &&& NodeFlags.DependsOnAnchorFlag = NodeFlags.DependsOnAnchorFlag


[<Flags>]
type internal StateFlags =
    | None = 0uy
    | InitialFlag = 1uy
    | HasTagFlag = 2uy
    | IsAnchorNullableFlag = 4uy
    | CanSkipFlag = 8uy
    | IsBeginNullableFlag = 16uy
    | IsEndNullableFlag = 32uy
    | IsAlwaysNullableFlag = 64uy
    | IsPendingNullableFlag = 128uy

[<RequireQualifiedAccess>]
module internal StateFlags =

    let inline isAlwaysNullable(flags: StateFlags) =
        flags &&& StateFlags.IsAlwaysNullableFlag = StateFlags.IsAlwaysNullableFlag

    let inline isAlwaysNullableNonPending(flags: StateFlags) =
        flags &&& (StateFlags.IsAlwaysNullableFlag ||| StateFlags.IsPendingNullableFlag) = StateFlags.IsAlwaysNullableFlag


    let inline isAnchorNonPending(flags: StateFlags) =
        flags &&& (StateFlags.IsAnchorNullableFlag ||| StateFlags.IsPendingNullableFlag) = StateFlags.IsAnchorNullableFlag

    let inline canBeNullable(flags: StateFlags) =
        flags &&& (StateFlags.IsAlwaysNullableFlag ||| StateFlags.IsAnchorNullableFlag)
        <> StateFlags.None

    let inline isInitial(flags: StateFlags) =
        flags &&& StateFlags.InitialFlag = StateFlags.InitialFlag

    let inline canNotSkip(flags: StateFlags) =
        flags &&& StateFlags.CanSkipFlag = StateFlags.None

    let inline canSkipLeftToRight(flags: StateFlags) =
        flags &&& StateFlags.CanSkipFlag = StateFlags.CanSkipFlag

    let inline isPendingNullable(flags: StateFlags) =
        flags &&& StateFlags.IsPendingNullableFlag = StateFlags.IsPendingNullableFlag

[<AutoOpen>]
[<Sealed>]
module internal RegexStateFlagsExtensions =
    type StateFlags with

        [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
        member this.IsAlwaysNullable =
            this &&& StateFlags.IsAlwaysNullableFlag = StateFlags.IsAlwaysNullableFlag

        [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
        member this.CanSkip =
            this &&& (StateFlags.CanSkipFlag ||| StateFlags.InitialFlag) = StateFlags.CanSkipFlag


[<Sealed>]
type internal RegexNodeInfo<'tset when TSet<'tset>>() =

    member val NodeFlags: NodeFlags = NodeFlags.None with get, set
    member val Startset: 'tset = Unchecked.defaultof<_> with get, set
    member val PendingNullables: RefSet = RefSet([||]) with get, set

    // filled in later
    member val SubsumedByMinterm: 'tset = Unchecked.defaultof<'tset> with get, set

    member inline this.IsAlwaysNullable =
        this.NodeFlags &&& NodeFlags.IsAlwaysNullableFlag = NodeFlags.IsAlwaysNullableFlag

    member inline this.CanBeNullable =
        this.NodeFlags &&& NodeFlags.CanBeNullableFlag = NodeFlags.CanBeNullableFlag

    member inline this.ContainsLookaround =
        this.NodeFlags &&& NodeFlags.ContainsLookaroundFlag = NodeFlags.ContainsLookaroundFlag

type RegexNodeId = int

module RegexNodeId =
    [<Literal>]
    let BOT = 0

    [<Literal>]
    let EPS = 1

    [<Literal>]
    let TOP = 2

    [<Literal>]
    let TOP_STAR = 3

    [<Literal>]
    let TOP_PLUS = 4

    [<Literal>]
    let END_ANCHOR = 5

    [<Literal>]
    let BEGIN_ANCHOR = 6

type RefSetId = int

module RefSetId =
    [<Literal>]
    let Empty = 0

// this form is great because F# shares `nodes` since .NET 9 and packs this into 16B
// (https://learn.microsoft.com/en-us/dotnet/fsharp/whats-new/fsharp-9#field-sharing-for-struct-discriminated-unions)
[<NoComparison; DebuggerDisplay("{ToString()}"); Struct>]
type internal RegexNode<'tset when TSet<'tset> and 'tset: equality> =
    /// RE.RE - [0]=head, [1]=tail
    | Concat of nodes: array<RegexNodeId>
    /// 𝜓 predicate - [0]=tsetIndex
    | Singleton of nodes: array<RegexNodeId>
    /// RE{𝑚, 𝑛}, \* = {0,int32.max} - [0]=body, [1]=lower, [2]=upper
    | Loop of nodes: array<RegexNodeId>
    /// RE|RE
    | Or of nodes: array<RegexNodeId>
    /// RE&RE
    | And of nodes: array<RegexNodeId>
    /// ~RE - [0]=inner
    | Not of nodes: array<RegexNodeId>
    /// lookahead (?=...) - [0]=body, [1]=relativeTo, [2]=pendingId
    | LookAhead of nodes: array<RegexNodeId>
    /// lookbehind (?<=...) - [0]=body, [1]=relativeTo, [2]=pendingId
    | LookBehind of nodes: array<RegexNodeId>
    | Begin
    | End


[<Flags>]
type internal StartsetFlags =
    | None = 0uy
    | IsFull = 1uy
    | IsEmpty = 2uy
    | Inverted = 4uy


/// collection of concrete startset chars for vectorization purposes
type internal PredStartset = {
    Flags: StartsetFlags
    Chars: char[]
} with

    static member Of(inverted, startset: char[]) = { Flags = inverted; Chars = startset }


type internal TSet = uint64
type internal TSolver = UInt64Solver

[<Sealed>]
type internal ObjectPool<'t>(generate: unit -> 't, initialPoolCount: int) =
    let mutable pool = Queue<'t>()

    do
        for _ = 1 to initialPoolCount do
            pool.Enqueue(generate ())

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member this.Rent() =
        match pool.TryDequeue() with
        | true, v -> v
        | _ -> generate ()

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member this.Return(item: 't) = pool.Enqueue(item)


[<Sealed>]
type internal PooledArray<'t when 't: equality>(initialSize: int) =
    let mutable size = 0
    let mutable limit = initialSize

    let mutable pool: 't array = ArrayPool.Shared.Rent(initialSize)

    member this.EnsureCapacity(n) =
        if limit < n then
            let newArray = ArrayPool.Shared.Rent(n)
            ArrayPool.Shared.Return(pool)
            pool <- newArray
            limit <- newArray.Length

    member this.Add(item) =
        if size = limit then
            let newLimit = limit * 2
            let newArray = ArrayPool.Shared.Rent(newLimit)
            Array.Copy(pool, newArray, size)
            ArrayPool.Shared.Return(pool)
            pool <- newArray
            limit <- newLimit

        pool[size] <- item
        size <- size + 1

    member this.OverwriteWith(items: Span<'t>) =
        this.Clear()
        this.EnsureCapacity(items.Length)
        size <- items.Length
        items.CopyTo(pool.AsSpan())

    member this.Item
        with get (i: int) = pool[i]
        and set (i: int) v = pool[i] <- v

    member this.Clear() = size <- 0

    member this.Contains(item) =
        let mutable e = pool.AsSpan(0, size).GetEnumerator()
        let mutable found = false

        while not found && e.MoveNext() do
            found <- e.Current = item

        found

    member this.Remove(item: 't) =
        let mutable span: Span<'t> = pool.AsSpan(0, size)
        let mutable e = pool.AsSpan(0, size).GetEnumerator()
        let mutable idx = -1
        let mutable i = 0

        while idx = -1 && e.MoveNext() do
            if e.Current = item then
                idx <- i

            i <- i + 1

        if idx = size - 1 then
            size <- size - 1
        else
            span[idx] <- span[size - 1]
            size <- size - 1

    member this.GetEnumerator() =
        let mutable e = pool.AsSpan(0, size).GetEnumerator()
        e

    member this.Length = size
    member this.Count = size

    member this.Exists(lambda) =
        let mutable e = pool.AsSpan(0, size).GetEnumerator()
        let mutable found = false

        while not found && e.MoveNext() do
            found <- lambda e.Current

        found

    member this.AsSpan() = pool.AsSpan(0, size)
    member this.AsArray() = pool.AsSpan(0, size).ToArray()

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member this.Dispose() = ArrayPool.Shared.Return(pool, false)

    interface IDisposable with
        member this.Dispose() = this.Dispose()


module internal RangeSet =
    let unionMany(sets: PooledArray<struct (int * int)>) : PooledArray<struct (int * int)> =
        // ValueList.toSpan
        if sets.Length = 0 then
            sets
        else

            let setspan = sets.AsSpan().Slice(0, sets.Length)
            setspan.Sort()

            let mutable mergedInner = new PooledArray<struct (int * int)>(16)

            let mutable pendingEnd: int voption = ValueNone
            let mutable currStart = LanguagePrimitives.GenericZero

            for s, e in setspan do
                match pendingEnd with
                // extend range
                | ValueSome pend when pend >= (s - 1) -> pendingEnd <- ValueSome(max e pend)
                | ValueSome pend ->
                    // end current
                    mergedInner.Add(struct (currStart, pend))
                    // start new pending
                    currStart <- s
                    pendingEnd <- ValueSome e
                | ValueNone ->
                    currStart <- s
                    pendingEnd <- ValueSome e

            mergedInner.Add(struct (currStart, pendingEnd.Value))
            mergedInner

// uint16 will suffice, a context length of longer than 65k will exceed memory limit
type internal rsint = uint16
type internal InnerSet = (struct (rsint * rsint))[]

[<Sealed>]
type internal RefSet =
    val inner: InnerSet
    member this.IsEmpty: bool = this.inner.Length = 0
    internal new(src_set: InnerSet) = { inner = src_set }


module internal Helpers =
    let rec printNode
        (css: CharSetSolver)
        (getTset: int -> BDD)
        (resolve: RegexNodeId -> RegexNode<BDD>)
        (id: RegexNodeId)
        =

        let isFull(tset: BDD) = css.IsFull(tset)
        let isEmpty(tset: BDD) = css.IsEmpty(tset)

        let printSet(tset: BDD) =
            if isFull tset then
                "_"
            elif isEmpty tset then
                "⊥"
            else
                let bdd: BDD = box tset :?> BDD
                BDD.prettyPrintBDD css bdd

        let paren str = $"({str})"
        let print = printNode css getTset resolve

        match resolve id with
        | Singleton nodes -> printSet (getTset nodes[0])
        | Or(items) ->
            let setItems = items |> Array.map print
            setItems |> String.concat "|" |> paren
        | And(items) ->
            let setItems = items |> Array.map print
            setItems |> String.concat "&" |> paren
        | Not nodes ->
            let inner = print nodes[0]
            $"~({inner})"
        | Loop nodes ->
            let body = nodes[0]
            let lower = nodes[1]
            let upper = nodes[2]
            let inner = print body

            let inner =
                match resolve body with
                | Singleton _ -> inner
                | _ -> $"({inner})"

            let loopCount =
                if lower = 0 && upper = Int32.MaxValue then "*"
                elif lower = 1 && upper = Int32.MaxValue then "+"
                elif lower = 0 && upper = 1 then "?"
                elif lower = upper then $"{{{lower}}}"
                elif upper = Int32.MaxValue then $"{{{lower},}}"
                else $"{{{lower},{upper}}}"

            if (lower = 2) && 2 = upper && inner.Length = 1 then
                $"{inner}{inner}"
            else

                inner + loopCount

        | LookAhead nodes ->
            let body = nodes[0]
            let pending = nodes[2]
            let inner =
                match print body with
                | s when s.EndsWith "_*" -> s.Substring(0, s.Length - 2)
                | s when s.StartsWith "_*" -> s.Substring(2)
                | s -> s

            let pending = if pending = RefSetId.Empty then "" else "{...}"
            let result = $"(?={inner})" + pending

            match result with
            | @"(?=(\n|\z))"
            | @"(?=(\z|\n))" -> "$"
            | _ -> result
        | LookBehind nodes ->
            let body = nodes[0]
            let pending = nodes[2]
            let inner =
                match print body with
                | s when s.EndsWith "_*" -> s.Substring(0, s.Length - 2)
                | s when s.StartsWith "_*" -> s.Substring(2)
                | s -> s

            let pending = if pending = RefSetId.Empty then "" else "{...}"
            let result = $"(?<={inner})" + pending

            match result with
            | @"(?<=(\n|\A))"
            | @"(?<=(\A|\n))" -> "^"
            | _ -> result
        | Concat nodes -> $"{print nodes[0]}{print nodes[1]}"
        | End -> @"\z"
        | Begin -> @"\A"

module internal Solver =
    let containsSet (solver: ISolver<'d>) (larger: 'd) (smaller: 'd) : bool =
        let overlapped = solver.And(smaller, larger)
        EqualityComparer<'d>.Default.Equals(smaller, overlapped)

    let starSubsumes (solver: ISolver<'d>) (pstar: 'd) (subsumedByMinterm: 'd) : bool =
        Solver.containsSet solver pstar subsumedByMinterm

    let inline mergeSets (s: ISolver< ^t >) (coll: seq< ^t >) : ^t =
        let mutable ss = s.Empty
        use mutable coll = coll.GetEnumerator()

        while (not (s.IsFull(ss))) && coll.MoveNext() do
            ss <- s.Or(ss, coll.Current)

        ss
