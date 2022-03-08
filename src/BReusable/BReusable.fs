// from https://gist.github.com/ImaginaryDevelopment/952b3a9afc4f2fa3c4631d43f760748a
module BReusable.Reusables

open System
open System.Collections.Generic
open System.Diagnostics

let inline guardAgainstNull msg (o: obj) = if isNull o then nullArg msg

let (|GuardNull|) msg (x: 'T) =
    guardAgainstNull msg x
    x

// for expensive zips
// we don't want to count the length of each
module ZipEquality =

    type FoldEqualResult<'t> =
        | BothEmpty
        | LengthError of int * int
        | FoundError of 't
        | NullInput of string
        | Completed

    // for comparing 2 expensive sequences
    let foldEquals f (left: _ seq, right: _ seq) =
        match left, right with
        | null, null -> NullInput "Both sequences are null"
        | null, _ -> NullInput "Left is null"
        | _, null -> NullInput "Right is null"
        | _ ->
            let mutable l, r = 0, 0
            use eLeft = left.GetEnumerator()
            use eRight = right.GetEnumerator()

            let liftTrue f (x: System.Collections.IEnumerator) =
                if x.MoveNext() then
                    f ()
                    true
                else
                    false

            let lNext () = liftTrue (fun () -> l <- l + 1) eLeft
            let rNext () = liftTrue (fun () -> r <- r + 1) eRight

            let mutable status = None

            while Option.isNone status do
                match lNext (), rNext () with
                | true, false
                | false, true -> status <- Some(LengthError(l, r))
                | true, true ->
                    match f (eLeft.Current, eRight.Current) with
                    | Some err -> status <- Some(FoundError(l, err))
                    | None -> ()
                // both say no more items remain
                | false, false ->
                    if l = 0 && r = 0 then
                        status <- Some BothEmpty
                    else
                        status <- Some Completed

            match status, l, r with
            | None, 0, 0 -> BothEmpty
            | None, _, _ -> Completed
            | Some s, _, _ -> s


[<RequireQualifiedAccess>]
module Result =
    let ofOption error =
        function
        | Some s -> Ok s
        | None -> Error error
    // legacy name: bind2
    /// apply either a success function or a failure function
    let inline either happyFunc unhappyFunc twoTrackInput =
        match twoTrackInput with
        | Ok s -> happyFunc s
        | Error u -> unhappyFunc u

    /// convert a one-track function into a switch
    let inline switch f = f >> Ok

    let isHappy =
        function
        | Ok _ -> true
        | _ -> false

    /// bind a function to the failure track
    /// primary design purpose: adding data to the failure track
    let inline bind' f = either Ok f

    /// An adapter that takes a normal one-track function and turns it into a switch function, and also catches exceptions
    /// could use id instead of a full exn function for cases you just want the exception
    let inline tryCatch f fEx x =
        try
            f x |> Ok
        with
        | ex -> fEx ex |> Error

    let toOkOption =
        function
        | Ok s -> s |> Some
        | _ -> None

    let toErrorOption =
        function
        | Ok _ -> None
        | Error s -> Some s
    // two-track to two-track if fAll is true for all items
    let forAllF fAll items =
        let items = items |> List.ofSeq

        if items |> Seq.forall fAll then
            items |> Seq.choose toOkOption |> Ok
        else
            items |> Seq.choose toErrorOption |> Error


type ResultBuilder() =
    member __.Return(x) = Ok x

    member __.ReturnFrom(m: Result<_, _>) = m

    member __.Bind(m, f) = Result.bind f m

    member __.Bind((m, error): (Option<'T> * 'E), f) =
        m |> Result.ofOption error |> Result.bind f

    member __.Zero() = None

    member __.Combine(m, f) = Result.bind f m

    member __.Delay(f: unit -> _) = f

    member __.Run(f) = f ()

    member __.TryWith(m, h) =
        try
            __.ReturnFrom(m)
        with
        | e -> h e

    member __.TryFinally(m, compensation) =
        try
            __.ReturnFrom(m)
        finally
            compensation ()

    member __.Using(res: #IDisposable, body) =
        __.TryFinally(
            body res,
            fun () ->
                match res with
                | null -> ()
                | disp -> disp.Dispose()
        )

    member __.While(guard, f) =
        if not (guard ()) then
            Ok()
        else
            do f () |> ignore
            __.While(guard, f)

    member __.For(sequence: seq<_>, body) =
        __.Using(sequence.GetEnumerator(), (fun enum -> __.While(enum.MoveNext, __.Delay(fun () -> body enum.Current))))

let result = new ResultBuilder()

[<AutoOpen>]
module MatchHelpers =
    // purpose: 'when clauses' require binding variable names, and if two cases should have the same result, but one has a condition on the bound variable, it can no longer point to the same exact path
    let (|IsTrue|_|) f x = if f x then Some x else None

    let (|IsAnyOf|_|) items x =
        if items |> Seq.exists ((=) x) then
            Some x
        else
            None

    let (|GreaterThan|_|) x y =
        if LanguagePrimitives.GenericGreaterThan y x then
            Some()
        else
            None

// things that assist with point-free style
[<AutoOpen>]
module FunctionalHelpersAuto =
    let cprintf c fmt = // https://blogs.msdn.microsoft.com/chrsmith/2008/10/01/f-zen-colored-printf/
        Printf.kprintf
            (fun s ->
                let old = System.Console.ForegroundColor

                try
                    System.Console.ForegroundColor <- c
                    System.Console.Write s
                finally
                    System.Console.ForegroundColor <- old
            )
            fmt

    let cprintfn c fmt =
        Printf.kprintf
            (fun s ->
                let old = System.Console.ForegroundColor

                try
                    System.Console.ForegroundColor <- c
                    System.Console.WriteLine s
                finally
                    System.Console.ForegroundColor <- old
            )
            fmt

    let teeTuple f x = x, f x
    /// take a dead-end function and curry the input
    let tee f x =
        f x
        x
    // take a value and adjust it to fall within the range of vMin .. vMax
    let clamp vMin vMax v = max v vMin |> min vMax

    /// super handy with operators like (*) and (-)
    /// take a function that expects 2 arguments and flips them before applying to the function
    let inline flip f x y = f y x
    /// take a tuple and apply the 2 arguments one at a time (from haskell https://www.haskell.org/hoogle/?hoogle=uncurry)
    let uncurry f (x, y) = f x y
    /// does not work with null x
    let inline getType x = x.GetType()
    // purpose: eliminate having to write (fun x -> x :?> _)
    // or (fun x -> downcast x)
    let downcastX<'T> (o: obj) : 'T =
        match o with
        | :? 'T as x -> x
        | x -> failwithf "Invalid cast to %s of %A" (typeof<'T>.Name) x
    // based on http://stackoverflow.com/a/2362114/57883
    // mimic the C# as keyword
    let castAs<'t> (o: obj) : 't option =
        match o with
        | :? 't as x -> Some x
        | _ -> None

    // allows you to pattern match against non-nullables to check for null (in case c# calls)
    let (|NonNull|UnsafeNull|) x =
        match box x with
        | null -> UnsafeNull
        | _ -> NonNull

    // for statically typed parameters in an active pattern see: http://stackoverflow.com/questions/7292719/active-patterns-and-member-constraint
    //consider pulling in useful functions from https://gist.github.com/ruxo/a9244a6dfe5e73337261
    let cast<'T> (x: obj) = x :?> 'T

    let inline swallow f =
        try
            f ()
        with
        | _ -> ()

    let inline makeUnsafeDisposal f =
        { new IDisposable with
            member __.Dispose() =
                printfn "Disposing UnsafeDisposal"
                f ()
        }
    // this swallows. Disposal methods are never supposed to/allowed to throw.
    let inline disposable (f: unit -> unit) =
        let inline swallow () = swallow f
        // this is made safe by swallowing
        makeUnsafeDisposal swallow

module Tuple2 =
    let replicate x = x, x
    // useful for Seq.mapi
    let fromCurry x y = (x, y)
    let curry f x y = f (x, y)
    // calling already defined function from outer namespace, instead of duplicating the functionality for consistency with gist
    let uncurry f (x, y) = uncurry f (x, y)
    let swap (x, y) = (y, x)
    let mapFst f (x, y) = f x, y
    let mapSnd f (x, y) = x, f y
    let extendFst f (x, y) = f (x, y), y
    let extendSnd f (x, y) = x, f (x, y)

    let optionOfFst f (x, y) =
        match f x with
        | Some x -> Some(x, y)
        | None -> None

    let optionOfSnd f (x, y) =
        match f y with
        | Some y -> Some(x, y)
        | None -> None
    // start Brandon additions
    let mapBoth f (x, y) = f x, f y

()

let failNullOrEmpty paramName x =
    if String.IsNullOrEmpty x then
        raise <| ArgumentOutOfRangeException paramName
    else
        x

type System.String with






    static member indexOf delimiter (x: string) =
        failNullOrEmpty "delimiter" delimiter |> x.IndexOf

    static member indexOfC delimiter c (x: string) =
        x.IndexOf(failNullOrEmpty "delimiter" delimiter, comparisonType = c)
    // couldn't get this guy to call the other guy, so... leaving him out too
//        static member contains (delimiter, ?c:StringComparison) (x:string) =
//            match failNullOrEmpty "delimiter" delimiter, c with
//            | d, Some c -> x.IndexOf(d, comparisonType=c) |> flip (>=) 0
//            | d, None -> x.Contains d
    static member contains delimiter (x: string) =
        failNullOrEmpty "delimiter" delimiter
        |> x.Contains

    static member containsC delimiter c (x: string) =
        x
        |> String.indexOfC (failNullOrEmpty "delimiter" delimiter) c
        |> flip (>=) 0

    static member substring i (x: string) = x.Substring i
    static member substring2 i e (x: string) = x.Substring(i, e)

    // the default insensitive comparison
    static member defaultIComparison =
        StringComparison.InvariantCultureIgnoreCase

    static member containsI delimiter (x: string) =
        String.containsC delimiter String.defaultIComparison x

    static member Null: string = null

    static member trim(s: string) =
        match s with
        | null -> null
        | s -> s.Trim()

    static member trim1 (d: char) (s: string) =
        match s with
        | null -> null
        | s -> s.Trim(d)

    static member split (delims: string seq) (x: string) =
        x.Split(delims |> Array.ofSeq, StringSplitOptions.None)

    static member splitO (items: string seq) options (x: string) = x.Split(items |> Array.ofSeq, options)

    static member emptyToNull(x: string) =
        if String.IsNullOrEmpty x then
            null
        else
            x

    static member equalsI (x: string) (x2: string) =
        not <| isNull x
        && not <| isNull x2
        && x.Equals(x2, String.defaultIComparison)

    static member startsWith (toMatch: string) (x: string) =
        not <| isNull x
        && not <| isNull toMatch
        && toMatch.Length > 0
        && x.StartsWith toMatch

    static member startsWithI (toMatch: string) (x: string) =
        not <| isNull x
        && not <| isNull toMatch
        && toMatch.Length > 0
        && x.StartsWith(toMatch, String.defaultIComparison)

    static member isNumeric(x: string) =
        not <| isNull x
        && x.Length > 0
        && x |> String.forall Char.IsNumber

    static member splitLines(x: string) =
        x.Split([| "\r\n"; "\n" |], StringSplitOptions.None)

    static member before (delimiter: string) s =
        s |> String.substring2 0 (s.IndexOf delimiter)

    static member beforeOrSelf (delimiter: string) x =
        if x |> String.contains delimiter then
            x |> String.before delimiter
        else
            x

    static member beforeAnyOf (delimiters: string list) (x: string) =
        let index, _ =
            delimiters
            |> Seq.map (fun delimiter -> x.IndexOf(delimiter), delimiter)
            |> Seq.filter (fun (index, _) -> index >= 0)
            |> Seq.minBy (fun (index, _) -> index)

        x.Substring(0, index)

    static member replace (target: string) (replacement) (str: string) =
        if String.IsNullOrEmpty target then
            invalidOp "bad target"
        else
            str.Replace(target, replacement)

// comment/concern/critique auto-opening string functions may pollute (as there are so many string functions)
// not having to type `String.` on at least the used constantly is a huge reduction in typing
// also helps with point-free style
module StringHelpers =

    // I've been fighting/struggling with where to namespace/how to architect string functions, they are so commonly used, static members make it easier to find them
    // since typing `String.` with this module open makes them all easy to find
    // favor non attached methods for commonly used methods


    let contains (delimiter: string) (x: string) = String.contains delimiter x

    let containsI (delimiter: string) (x: string) =
        x
        |> String.containsC delimiter String.defaultIComparison

    let substring i x = x |> String.substring i
    let substring2 i length (x: string) = x |> String.substring2 i length //x.Substring(i, length)

    let before (delimiter: string) s =
        s |> String.substring2 0 (s.IndexOf delimiter)

    let beforeOrSelf delimiter x =
        if x |> String.contains delimiter then
            x |> before delimiter
        else
            x

    let after (delimiter: string) (x: string) =
        failNullOrEmpty "x" x
        |> tee (fun _ -> failNullOrEmpty "delimiter" delimiter |> ignore)
        |> fun x ->
            match x.IndexOf delimiter with
            | i when i < 0 -> failwithf "after called without matching substring in '%s'(%s)" x delimiter
            | i -> x |> String.substring (i + delimiter.Length)

    let afterI (delimiter: string) (x: string) =
        x
        |> String.indexOfC delimiter String.defaultIComparison
        |> (+) delimiter.Length
        |> flip String.substring x

    let afterOrSelf delimiter x =
        if x |> String.contains delimiter then
            x |> after delimiter
        else
            x

    let afterOrSelfI (delimiter: string) (x: string) =
        if x
           |> String.containsC delimiter String.defaultIComparison then
            x |> afterI delimiter
        else
            x

    let containsAnyOf (delimiters: string seq) (x: string) =
        delimiters |> Seq.exists (flip contains x)

    let containsIAnyOf (delimiters: string seq) (x: string) =
        delimiters |> Seq.exists (flip containsI x)

    let endsWith (delimiter: string) (x: string) = x.EndsWith delimiter

    let isNumeric (s: string) =
        not <| isNull s
        && s.Length > 0
        && s |> String.forall Char.IsNumber

    let replace (target: string) (replacement) (str: string) =
        if String.IsNullOrEmpty target then
            invalidOp "bad target"
        else
            str.Replace(target, replacement)

    let splitLines (x: string) =
        x.Split([| "\r\n"; "\n" |], StringSplitOptions.None)

    let startsWith (delimiter: string) (s: string) = s.StartsWith delimiter

    let startsWithI (delimiter: string) (s: string) =
        s.StartsWith(delimiter, String.defaultIComparison)

    let trim = String.trim
    let trim1 (delim: string) (x: string) = x.Trim(delim |> Array.ofSeq)

    let afterLast delimiter x =
        if x |> String.contains delimiter then
            failwithf "After last called with no match"

        x
        |> String.substring (x.LastIndexOf delimiter + delimiter.Length)

    let stringEqualsI s1 (toMatch: string) =
        not <| isNull toMatch
        && toMatch.Equals(s1, StringComparison.InvariantCultureIgnoreCase)

    let inline isNullOrEmptyToOpt s =
        if String.IsNullOrEmpty s then
            None
        else
            Some s

    // was toFormatString
    // with help from http://www.readcopyupdate.com/blog/2014/09/26/type-constraints-by-example-part1.html
    let inline toFormatString (f: string) (a: ^a) =
        (^a: (member ToString : string -> string) (a, f))

    let inline getLength s = (^a: (member Length : _) s)

    //if more is needed consider humanizer or inflector
    let toPascalCase s =
        s
        |> Seq.mapi (fun i l ->
            if i = 0 && Char.IsLower l then
                Char.ToUpper l
            else
                l
        )
        |> String.Concat

    let humanize camel : string =
        seq {
            let pascalCased = toPascalCase camel
            yield pascalCased.[0]

            for l in pascalCased |> Seq.skip 1 do
                if System.Char.IsUpper l then
                    yield ' '
                    yield l
                else
                    yield l
        }
        |> String.Concat

    /// assumes all that is needed is the first char changed, does not account for underscoring
    let toCamelCase s = // https://github.com/ayoung/Newtonsoft.Json/blob/master/Newtonsoft.Json/Utilities/StringUtils.cs
        if String.IsNullOrEmpty s then
            s
        elif not <| Char.IsUpper s.[0] then
            s
        else
            let camelCase =
                Char
                    .ToLower(s.[0], System.Globalization.CultureInfo.InvariantCulture)
                    .ToString(System.Globalization.CultureInfo.InvariantCulture)

            if (s.Length > 1) then
                camelCase + (s.Substring 1)
            else
                camelCase


open StringHelpers


// I've also been struggling with the idea that Active patterns are frequently useful as just methods, so sometimes methods are duplicated as patterns
[<AutoOpen>]
module StringPatterns =
    open StringHelpers

    let (|ToString|) (x: obj) =
        match x with
        | null -> null
        | x -> x.ToString()

    let isValueString = String.IsNullOrWhiteSpace >> not

    let (|ValueString|NonValueString|) =
        function
        | x when isValueString x -> ValueString x
        | x -> NonValueString x

    let (|MultiLine|_|) x =
        match splitLines x with
        | [||] -> None
        | lines -> Some lines

    let (|NullOrEmpty|_|) x =
        if String.IsNullOrEmpty x then
            Some()
        else
            None

    let (|WhiteSpace|_|) =
        function
        | null
        | "" -> None
        | x when String.IsNullOrWhiteSpace x -> Some x
        | _ -> None

    module Option =
        let ofValueString =
            function
            | ValueString x -> Some x
            | _ -> None

    let (|EndsWith|_|) delim x =
        // justification: fail is going to throw, and we want to name the arguments, without requiring an extra fun
        failNullOrEmpty "delim" delim |> ignore

        x
        |> Option.ofValueString
        |> Option.filter (fun x -> x.EndsWith delim)
    //let (|NullString|Empty|WhiteSpace|ValueString|) (s:string) =
    //    match s with
    //    | null -> NullString
    //    | "" -> Empty
    //    | _ when String.IsNullOrWhiteSpace s -> WhiteSpace
    //    | _ -> ValueString s

    // Optionn.OfObj because this can potentially be used with a whitespace delimiter on a whitespace-only string
    let (|StartsWith|_|) d =
        failNullOrEmpty d |> ignore

        Option.ofObj
        >> Option.filter (String.startsWith d)
        >> Option.map ignore

    let (|StartsWithI|_|) d =
        failNullOrEmpty d |> ignore

        Option.ofObj
        >> Option.filter (String.startsWithI d)
        >> Option.map ignore

    let (|After|_|) d =
        failNullOrEmpty "d" d |> ignore<string>

        Option.ofObj
        >> Option.filter (String.contains d)
        >> Option.map (StringHelpers.after d)

    let (|AfterI|_|) d =
        failNullOrEmpty "d" d |> ignore<string>

        Option.ofObj
        >> Option.filter (String.containsI d)
        >> Option.map (StringHelpers.afterI d)

    let (|Before|_|) d =
        failNullOrEmpty "d" d |> ignore<string>

        Option.ofObj
        >> Option.filter (String.contains d)
        >> Option.map (StringHelpers.before d)

    let (|BeforeI|_|) d =
        failNullOrEmpty "d" d |> ignore<string>

        Option.ofObj
        >> Option.filter (String.containsI d)
        >> Option.map (StringHelpers.before d)

    let (|StringEqualsI|_|) d =
        Option.ofObj
        >> Option.filter (String.equalsI d)
        >> Option.map ignore

    let (|InvariantEqualI|_|) d =
        Option.ofObj
        >> Option.filter (fun arg -> String.Compare(d, arg, StringComparison.InvariantCultureIgnoreCase) = 0)
        >> Option.map ignore

    let (|IsNumeric|_|) =
        Option.ofValueString
        >> Option.filter (String.forall Char.IsNumber)
        >> Option.map ignore

    let (|Contains|_|) d =
        Option.ofObj
        >> Option.filter (contains d)
        >> Option.map ignore

    let (|ContainsI|_|) d =
        Option.ofObj
        >> Option.filter (containsI d)
        >> Option.map ignore

    let (|StringContains|_|) d =
        Option.ofObj
        >> Option.filter (contains d)
        >> Option.map ignore

    let (|OrdinalEqualI|_|) (str: string) =
        Option.ofObj
        >> Option.filter (fun arg -> String.Compare(str, arg, StringComparison.OrdinalIgnoreCase) = 0)
        >> Option.map ignore

    let (|RMatch|_|) (pattern: string) (x: string) =
        let m =
            System.Text.RegularExpressions.Regex.Match(x, pattern)

        if m.Success then Some m else None

    let inline fromParser f x =
        match f x with
        | true, v -> Some v
        | _, _ -> None


    let inline tryParse parser (x: string) : 't option =
        match x with
        | null -> None
        | _ -> fromParser parser x

    let parseBool (text: string) = tryParse Boolean.TryParse text
    let parseDateTime (text: string) = tryParse DateTime.TryParse text

    let parseDecimal (text: string) =
        text
        |> tryParse Decimal.TryParse
        |> Option.map LanguagePrimitives.DecimalWithMeasure

    let parseFloat x =
        x
        |> tryParse Double.TryParse
        |> Option.map LanguagePrimitives.FloatWithMeasure

    let parseGuid = tryParse System.Guid.TryParse

    let parseInt x =
        tryParse System.Int32.TryParse x
        |> Option.map LanguagePrimitives.Int32WithMeasure

    let parseInt64 x =
        tryParse System.Int64.TryParse x
        |> Option.map LanguagePrimitives.Int64WithMeasure


    let inline isTOrTryParse (t, parser) (x: obj) : 't option =
        match x with
        | null -> None
        | :? 't as t -> Some t
        | v when v.GetType() = t -> Some(v :?> 't)
        | :? string as p -> fromParser parser p
        | _ -> None

    let inline private isTOrUseParse (t, parser) (x: obj) : 't option =
        match x with
        | null -> None
        | :? 't as t -> Some t
        | v when v.GetType() = t -> Some(v :?> 't)
        | :? string as text -> parser text
        | _ -> None

    let (|ParseBool|_|) = parseBool
    let (|ParseDateTime|_|) = parseDateTime
    let (|ParseDecimal|_|) = parseDecimal
    let (|ParseFloat|_|) = parseFloat
    let (|ParseGuid|_|) = parseGuid
    let (|ParseInt|_|) = parseInt
    let (|ParseInt64|_|) = parseInt64

    let inline (|TryParse|_|) parser (x: string) : 't option = tryParse parser x

    let (|AsBoolean|_|) x =
        isTOrUseParse (typeof<bool>, parseBool) x

    let (|AsDateTime|_|) x =
        isTOrUseParse (typeof<DateTime>, parseDateTime) x

    let (|AsDecimal|_|) x =
        isTOrUseParse (typeof<decimal>, parseDecimal) x

    let (|AsFloat|_|) x =
        isTOrUseParse (typeof<float>, parseFloat) x

    let (|AsGuid|_|) x =
        isTOrUseParse (typeof<Guid>, parseGuid) x

    let (|AsInt|_|) x =
        x |> isTOrUseParse (typeof<int>, parseInt)

    let (|AsInt64|) x =
        isTOrUseParse (typeof<int64>, parseInt64) x

    let inline (|IsTOrTryParse|_|) (t, parser) (x: obj) : 't option = isTOrTryParse (t, parser) x

    type System.String with




        static member IsValueString =
            function
            | ValueString _ -> true
            | _ -> false

#if LINQPAD
    let dumpt (title: string) x =
        x.Dump(title)
        x
#else
    let dumpt (title: string) x =
        printfn "%s:%A" title x
        x
#endif
    let indent spacing (text: string) =
        if String.IsNullOrEmpty(text) then
            String.Empty
        else if trim text |> String.contains "\r\n" then
            "\r\n" + text
            |> splitLines
            |> Seq.map (fun s -> spacing + s)
            |> String.concat "\r\n"
        else
            text

type ChangedValue<'T> = { OldValue: 'T; NewValue: 'T }

type ChangeType<'T> =
    | Unchanged of ChangedValue<'T>
    | Added of 'T
    | Removed of 'T
    | Changed of ChangedValue<'T>
    member x.GetChangeValues() =
        match x with
        | Changed y -> Some y
        | _ -> None

    member x.GetAdded() =
        match x with
        | Added y -> Some y
        | _ -> None

    member x.GetRemoved() =
        match x with
        | Removed y -> Some y
        | _ -> None

module ChangeTracking =

    let getChanges (changedItemValue: ChangedValue<'T list>) fIdentity fEqual =
        let previous, current =
            changedItemValue.OldValue, changedItemValue.NewValue

        let identities =
            let oldIdentities = previous |> Seq.map fIdentity
            let currentIdentities = current |> Seq.map fIdentity

            oldIdentities
            |> Seq.append currentIdentities
            |> Seq.distinct
            |> List.ofSeq

        identities
        |> Seq.fold
            (fun changes identity ->
                match previous
                      |> Seq.tryFind (fun x -> fIdentity x = identity),
                      current
                      |> Seq.tryFind (fun x -> fIdentity x = identity) with
                | None, None ->
                    failwithf
                        "Identity function returned an identity not present in either item, or the identity was changed"
                | Some prev, None -> Removed prev :: changes
                | None, Some curr -> Added curr :: changes
                | Some p, Some c ->
                    if fEqual p c then
                        Unchanged { OldValue = p; NewValue = c }
                        :: changes
                    else
                        Changed { OldValue = p; NewValue = c } :: changes
            )
            List.empty

    // use structural equality
    let getChangesUsingEquality changedItemValue fIdentity =
        getChanges changedItemValue fIdentity (=)

module Xml =
    open System.Xml.Linq
    let nsNone = XNamespace.None
    let toXName (ns: XNamespace) name = ns + name

    let getElement1 n (e: XElement) = e.Element n |> Option.ofObj
    // leaving out a 'getElement' as it will likely be (samples in code comments below):
    //    let getElement = toXName nsNone >> getElement1
    //    let getElement = toXName doc.Root.Name.Namespace >> getElement1
    let getElements1 n (e: XElement) = e.Elements n
    // point-free Seq.filter argument
    let isNamed n (e: XElement) = e.Name = n

    let getElementsAfter n (e: XElement) =
        e
        |> getElements1 n
        |> Seq.skipWhile (isNamed n >> not)
        |> Seq.skip 1

    let getAttributeVal name (e: XElement) =
        nsNone + name
        |> e.Attribute
        |> Option.ofObj
        |> Option.map (fun a -> a.Value)

    let setAttribVal name value (e: XElement) =
        e.SetAttributeValue(nsNone + name, value)

    let getDescendants n (e: XElement) = e.Descendants n

    let attribValueIs name value e =
        e
        |> getAttributeVal name
        |> Option.toObj
        |> (=) value

    let isElement (e: XNode) =
        match e with
        | :? XElement -> true
        | _ -> false

    // when you |> string an XElement, normally it writes appends the namespace as an attribute, but this is normally covered by the root element
    let stripNamespaces (e: XElement) : XElement =
        // if the node is not XElement, pass through
        let rec stripNamespaces (n: XNode) : XNode =
            match n with
            | :? XElement as x ->
                let contents =
                    x.Attributes()
                    // strips default namespace, but not other declared namespaces
                    |> Seq.filter (fun xa -> xa.Name.LocalName <> "xmlns")
                    |> Seq.cast<obj>
                    |> List.ofSeq
                    |> (@)
                        (
                            x.Nodes()
                            |> Seq.map stripNamespaces
                            |> Seq.cast<obj>
                            |> List.ofSeq
                        )

                XElement(nsNone + x.Name.LocalName, contents |> Array.ofList) :> XNode
            | x -> x

        stripNamespaces e :?> XElement

    type XElement with






        static member GetElement1 name (x: XElement) = x.Element(XNamespace.None + name)

        static member GetElements1 name (x: XElement) =
            x.Elements()
            |> Seq.filter (fun x -> x.Name.LocalName = name)

        static member GetElements(x: XElement) = x.Elements()

    ()


//https://blogs.msdn.microsoft.com/dsyme/2009/11/08/equality-and-comparison-constraints-in-f/
type System.Int32 with






    static member tryParse(x: string) =
        match System.Int32.TryParse x with
        | true, x -> Some x
        | _ -> None

module Choices =
    // take a list, and mapping it, the list will have items only if all of the input items met the criteria to be chosen
    let private allOrNone fChoose items =
        match items with
        | [] -> None
        | items ->
            List.foldBack
                (fun item state ->
                    match state with
                    | None -> None
                    | Some items ->
                        match fChoose item with
                        | Some item -> item :: items |> Some
                        | None -> None
                )
                items
                (Some [])

    // If all items in the list are Choice1Of2 return a list of them unwrapped
    let (|Homogenous1Of2|_|) items =
        allOrNone
            (function
            | Choice1Of2 x -> Some x
            | _ -> None)
            items

    // If all items in the list are Choice2Of2 return a list of them unwrapped
    let (|Homogenous2Of2|_|) items =
        allOrNone
            (function
            | Choice2Of2 x -> Some x
            | _ -> None)
            items

    let (|Just1sOf2|) items =
        items
        |> List.choose (
            function
            | Choice1Of2 x -> Some x
            | _ -> None
        )
        |> Some

    let (|Just2sOf2|) items =
        items
        |> List.choose (
            function
            | Choice2Of2 x -> Some x
            | _ -> None
        )


module IComparable =
    let equalsOn f x (yobj: obj) =
        match yobj with
        | :? 'T as y -> (f x = f y)
        | _ -> false

    let hashOn f x = hash (f x)

    let compareOn f x (yobj: obj) =
        match yobj with
        | :? 'T as y -> compare (f x) (f y)
        | _ -> invalidArg "yobj" "cannot compare values of different types"

module Paging =
    type Page<'T> =
        {
            Index: int
            PageSize: int
            Total: int
            PageItems: 'T list
        }
        member x.Page = x.Index + 1

        member x.Pages =
            float x.Total / float x.PageSize |> ceil |> round

// #nowarn "0042"


/// this doesn't account for cases where the identity is longer than signed int holds
type ValidIdentity<[<Measure>] 'T> private (i: int<'T>) =
    static let isValid i = i > 0<_>

    let i =
        if isValid i then
            i
        else
            failwithf "Invalid value"

    member __.Value = i
    /// valid values are 1..x
    static member TryCreateOpt i =
        if isValid i then
            ValidIdentity<'T>(i) |> Some
        else
            None

    static member get(vi: ValidIdentity<_>) : int<'T> = vi.Value
    member private __.ToDump() = i |> string // linqpad friendly
    override x.ToString() = x.ToDump()

    override x.Equals y =
        IComparable.equalsOn ValidIdentity.get x y

    override x.GetHashCode() = IComparable.hashOn ValidIdentity.get x

    interface System.IComparable with
        member x.CompareTo y =
            IComparable.compareOn ValidIdentity.get x y

[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module ValidIdentity =
    let isValid i = i > 0<_>
    let optionOfInt (x: int<_>) = if isValid x then Some x else None

    let optionOfNullable (x: int<_> Nullable) =
        x |> Option.ofNullable |> Option.bind optionOfInt

let (|IsValidIdentity|_|) x =
    ValidIdentity.TryCreateOpt(x)
    |> Option.map (fun vi -> vi.Value)


// module IntPatterns =
//     let (|PositiveInt|Zero|NegativeInt|) (x:int<_>) =
//         if x > 0<_> then PositiveInt
//         elif x = 0<_> then Zero
//         else NegativeInt

module NumPatterns =
    let inline isPositive x = x > LanguagePrimitives.GenericZero
    let inline isNegative x = x < LanguagePrimitives.GenericZero
    // let inline (|Positive|_|) x = if isPositive x then Some x else None

    let inline (|Positive|Zero|Negative|) x =
        if isPositive x then Positive x
        elif isNegative x then Negative x
        else Zero

type IDictionary<'TKey, 'TValue> with






    static member TryFind (k: 'TKey) (d: IDictionary<'TKey, 'TValue>) =
        if d.ContainsKey k then
            Some d.[k]
        else
            None

module Caching =

    let (|IsUnderXMinutes|_|) maxAgeMinutes (dt: DateTime) =
        let minutes =
            DateTime.Now - dt |> fun x -> x.TotalMinutes

        if minutes < maxAgeMinutes then
            Some()
        else
            None

    type Result =
        | Success
        | Failed

    [<NoEquality>]
    [<NoComparison>]
    type CacheAccess<'TKey, 'TValue when 'TKey: comparison> =
        {
            Getter: 'TKey -> 'TValue option
            Setter: 'TKey -> 'TValue -> unit
            GetSetter: 'TKey -> (unit -> 'TValue) -> 'TValue
        }
        // C# helper(s)
        member x.GetSetterFuncy(k, f: Func<_>) = x.GetSetter k f.Invoke


    let createTimedCache<'TKey, 'TValue when 'TKey: comparison> (fIsYoungEnough) =
        let cache =
            System.Collections.Concurrent.ConcurrentDictionary<'TKey, DateTime * 'TValue>()
        //let cache: Map<'TKey,DateTime*'TValue> = Map.empty
        let getter k =
            let result =
                cache
                |> IDictionary.TryFind k
                |> Option.filter (fst >> fIsYoungEnough)
                |> Option.map snd

            match result with
            | Some v ->
                printfn "Cache hit for %A" k
                Some v
            | None ->
                printfn "Cache miss for %A" k
                None

        let setter k v = cache.[k] <- (DateTime.Now, v)

        let getSetter k f =
            match getter k with
            | Some v -> v
            | _ ->
                let v = f ()
                setter k v
                v

        {
            Getter = getter
            Setter = setter
            GetSetter = getSetter
        }

module Debug =
    open System.Collections.ObjectModel

    type FListener(fWrite: _ -> unit, fWriteLn: _ -> unit, name) =
        inherit TraceListener(name)
        override __.Write(msg: string) = fWrite msg
        override __.WriteLine(msg: string) = fWriteLn msg
        new(fWrite, fWriteLn) = new FListener(fWrite, fWriteLn, null)

    type FLineListener(source: string ObservableCollection, fLineMap) =
        inherit TraceListener()
        let mutable lastWasWriteNotWriteLine = false
        let fLineMap = defaultArg fLineMap id

        let addText msg isLineFinished =
            if lastWasWriteNotWriteLine then
                let lastLine = source.[source.Count - 1]
                assert (source.Remove lastLine)
                lastLine + msg
            else
                msg
            |> fun x -> if isLineFinished then fLineMap x else x
            |> source.Add

        new(source, lineMap: Func<_, _>) =
            new FLineListener(
                source,
                fLineMap =
                    if isNull lineMap then
                        None
                    else
                        Some lineMap.Invoke
            )

        override __.Write(msg: string) =
            addText msg false
            lastWasWriteNotWriteLine <- true

        override __.WriteLine(msg: string) =
            addText msg true
            lastWasWriteNotWriteLine <- false


    type DebugTraceListener(?breakOnAll) =
        inherit TraceListener()
        let mutable breakOnAll: bool = defaultArg breakOnAll false
        override __.Write(_msg: string) = ()

        override __.WriteLine(msg: string) =
            let toIgnorePatterns =
                [
                    @"BindingExpression path error: 'Title' property not found on 'object' ''String' \(HashCode=-[0-9]+\)'. BindingExpression:Path=Title; DataItem='String' \(HashCode=-[0-9]+\); target element is 'ContentPresenter' \(Name='Content'\); target property is 'ResourceKey' \(type 'String'\)"
                ]

            let regMatch p =
                let m =
                    Text.RegularExpressions.Regex.Match(msg, p)

                if m.Success then Some p else None

            let matchedIgnorePattern =
                toIgnorePatterns
                |> Seq.choose regMatch
                |> Seq.tryHead

            match matchedIgnorePattern with
            | Some _ -> ()
            | None ->
                if breakOnAll && Debugger.IsAttached then
                    Debugger.Break()
                else
                    ()

    type Listener(created: DateTime, name) =
        inherit TraceListener(name)

        new(created) = new Listener(created, null)

        override __.Write(msg: string) = printf "%s" msg
        override __.WriteLine(msg: string) = printfn "%s" msg
        member __.Created = created


    let inline assertIfDebugger b =
        if not b then
            printfn "Assertion failed"

            if Diagnostics.Debugger.IsAttached then
                Debugger.Break()
// this option may be different from Debug.Assert somehow
// https://docs.microsoft.com/en-us/dotnet/articles/fsharp/language-reference/assertions
//            else
//                assert b


open System.Collections.ObjectModel

type System.Collections.ObjectModel.ReadOnlyCollection<'t> with






    static member Empty =
        System.Collections.ObjectModel.ReadOnlyCollection<'t>(ResizeArray())

    static member EmptyI =
        System.Collections.ObjectModel.ReadOnlyCollection<'t>
            .Empty
        :> IReadOnlyList<_>

    static member EmptyICollection =
        System.Collections.ObjectModel.ReadOnlyCollection<'t>
            .Empty
        :> IReadOnlyCollection<_>

module ReadOnlyCollection =
    let empty<'t> : ReadOnlyCollection<'t> = ReadOnlyCollection<'t>.Empty

    let ofSeq (x: _ seq) =
        x |> ResizeArray |> ReadOnlyCollection<_>

type IReadOnlyList<'T> with






    static member OfSeq(x: _ seq) =
        ReadOnlyCollection.ofSeq x :> IReadOnlyList<_>

type System.Action with






    static member invoke (x: System.Action) () = x.Invoke()
    static member invoke1 (x: System.Action<_>) y = x.Invoke(y)
    static member invoke2 (x: System.Action<_, _>) y z = x.Invoke(y, z)
    static member invoke3 (x: System.Action<_, _, _>) a b c = x.Invoke(a, b, c)
    static member invoke4 (x: System.Action<_, _, _, _>) a b c d = x.Invoke(a, b, c, d)
    static member invoke5 (x: System.Action<_, _, _, _, _>) a b c d e = x.Invoke(a, b, c, d, e)

module Func =
    let inline invoke (x: System.Func<_>) () = x.Invoke()
    let inline invoke1 (x: System.Func<_, _>) y = x.Invoke y
    let inline invoke2 (x: System.Func<_, _, _>) y z = x.Invoke(y, z)
    let inline invoke3 (x: System.Func<_, _, _, _>) a b c = x.Invoke(a, b, c)
    let inline invoke4 (x: System.Func<_, _, _, _, _>) a b c d = x.Invoke(a, b, c, d)
    let inline invoke5 (x: System.Func<_, _, _, _, _, _>) a b c d e = x.Invoke(a, b, c, d, e)

module Seq =

    let inline any items = items |> Seq.exists (fun _ -> true)

    let copyFrom (source: _ seq) (toPopulate: IList<_>) =
        if not <| isNull source && not <| isNull toPopulate then
            use enumerator = source.GetEnumerator()

            while enumerator.MoveNext() do
                toPopulate.Add(enumerator.Current)

    let ofType<'t> items =
        items
        |> Seq.cast<obj>
        |> Seq.choose (fun x ->
            match x with
            | :? 't as x -> Some x
            | _ -> None
        )

    let trySingle<'T> x =
        x
        |> Seq.truncate 2
        |> List.ofSeq
        |> function
            | [ (x: 'T) ] -> Ok x
            | [] -> Error "no elements"
            | _ -> Error "more than one element"

    /// Iterates over elements of the input sequence and groups adjacent elements.
    /// A new group is started when the specified predicate holds about the element
    /// of the sequence (and at the beginning of the iteration).
    ///
    /// For example:
    ///    Seq.windowedFor isOdd [3;3;2;4;1;2] = seq [[3]; [3; 2; 4]; [1; 2]]
    let windowedFor f (input: seq<_>) =
        seq {
            use en = input.GetEnumerator()
            let running = ref true
            // Generate a group starting with the current element. Stops generating
            // when it founds element such that 'f en.Current' is 'true'
            let rec group () =
                [
                    yield en.Current
                    if en.MoveNext() then
                        if not (f en.Current) then
                            yield! group ()
                    else
                        running := false
                ]

            if en.MoveNext() then
                // While there are still elements, start a new group
                while running.Value do
                    yield group () |> Seq.ofList
        }

    /// assumes you will iterate the entire sequence, otherwise not disposed
    /// probably not ok for infinite sequences
    let ofIEnumerator (en: System.Collections.IEnumerator) =
        let unfolder () =
            if en.MoveNext() then
                Some(en.Current, ())
            else
                // sequence iterated, if it is disposable dispose it
                match en with
                | :? IDisposable as d -> d.Dispose()
                | _ -> ()

                None

        Seq.unfold unfolder ()

module Map =
    let ofDictionary x =
        x :> _ seq |> Seq.map (|KeyValue|) |> Map.ofSeq

    /// in the event of a matching key, 2nd in wins
    let merge<'K, 'V when 'K: comparison> =
        Map.fold (fun acc (key: 'K) (value: 'V) -> Map.add key value acc)

    let intersect (baseDict: IDictionary<_, _>) (overrideOrAppendDict: IDictionary<_, _>) =
        baseDict
        |> Seq.append overrideOrAppendDict
        |> Seq.map (|KeyValue|)
        |> dict

module PathHelpers =
    open System.IO

    let findNewest path =
        Directory.GetFiles path
        |> Seq.map (
            Tuple2.replicate
            >> Tuple2.mapSnd File.GetLastWriteTime
        )
        |> Seq.maxBy snd


module List =
    let cartesian xs ys =
        xs
        |> List.collect (fun x -> ys |> List.map (fun y -> x, y))

    // return a Tuple where (A, B) (both present if they have a match)
    let forceJoin b a =
        let b = Set.ofList b
        let a = Set.ofList a
        let x = Set.intersect a b
        let diffa = a - b
        let diffb = b - a

        diffa - x
        |> Seq.map (fun a' -> Some a', None)
        |> Seq.append (x |> Seq.map (fun x' -> (Some x', Some x')))
        |> Seq.append (diffb - x |> Seq.map (fun b' -> None, Some b'))
        |> List.ofSeq

    // return a Tuple where (A, B) (both present if they have a match)
    let forceJoinWith (b: 'b list, f: 'b -> 'a) (a: 'a list) : ('a option * 'b option) list =
        let a = a |> Set.ofList
        let b = b |> List.map (fun b -> f b, b) |> dict

        let result =
            seq {
                yield!
                    a
                    |> Seq.map (fun x ->
                        if b.ContainsKey x then
                            (Some x, Some b.[x])
                        else
                            Some x, None
                    )

                yield!
                    b.Keys
                    |> Seq.filter (a.Contains >> not)
                    |> Seq.map (fun bKey -> None, Some b.[bKey])
            }

        result |> List.ofSeq

type System.Collections.Generic.List<'T> with






    static member tryItem i (x: List<'T>) =
        if x.Count > i then Some x.[i] else None

module Observables =
    open System.Collections.ObjectModel
    open System.Collections.Specialized
    // when loading a large number of items, wait until all are loaded to fire
    // implementation from https://peteohanlon.wordpress.com/2008/10/22/bulk-loading-in-observablecollection/
    type SuppressibleObservableCollection<'T>() =
        inherit ObservableCollection<'T>()
        let mutable suppress = false

        override __.OnCollectionChanged e =
            if not suppress then
                base.OnCollectionChanged e

        member x.AddRange items =
            if isNull items then
                raise <| ArgumentNullException "items"

            suppress <- true
            items |> Seq.iter x.Add
            suppress <- false
            x.OnCollectionChanged(NotifyCollectionChangedEventArgs(NotifyCollectionChangedAction.Reset))

    let bindObsTToObsObjDispatched (obsCollection: ObservableCollection<'t>) fDispatch =
        let obsObj = ObservableCollection<obj>()

        obsCollection.CollectionChanged.Add(fun e ->
            match e.Action with
            | NotifyCollectionChangedAction.Add ->
                fDispatch (fun () -> e.NewItems |> Seq.cast<obj> |> Seq.iter obsObj.Add)
            | NotifyCollectionChangedAction.Move ->
                fDispatch (fun () ->
                    let oldIndex = e.OldStartingIndex
                    let newIndex = e.NewStartingIndex
                    obsObj.Move(oldIndex, newIndex)
                )

            | NotifyCollectionChangedAction.Remove ->
                fDispatch (fun () ->
                    e.OldItems
                    |> Seq.cast<obj>
                    |> Seq.iter (obsObj.Remove >> ignore<bool>)
                )
            | NotifyCollectionChangedAction.Replace ->
                fDispatch (fun () ->
                    e.NewItems
                    |> Seq.cast<obj>
                    |> Seq.zip (e.OldItems |> Seq.cast<obj>)
                    |> Seq.iteri (fun i (oldItem, newItem) ->
                        assert (obsObj.[e.OldStartingIndex + i] = oldItem)
                        obsObj.[e.OldStartingIndex + i] <- newItem
                    )
                )
            | NotifyCollectionChangedAction.Reset ->
                fDispatch (fun () ->
                    obsObj.Clear()

                    if not <| isNull e.NewItems then
                        e.NewItems |> Seq.cast<obj> |> Seq.iter obsObj.Add
                )
            | x -> failwithf "Case %A is unimplemented" x

        )

        obsObj

    let bindObsTToObsObj (obsCollection: ObservableCollection<'t>) =
        bindObsTToObsObjDispatched obsCollection (fun f -> f ())

type System.Convert with






    static member ToGuid(o: obj) = o :?> Guid
    static member ToBinaryData(o: obj) = o :?> byte []


// based on http://stackoverflow.com/questions/15115050/f-type-constraints-on-enums
type System.Enum with






    [<RequiresExplicitTypeArguments>]
    static member parseT<'t when 't: enum<int>> x = Enum.Parse(typeof<'t>, x) :?> 't

    static member parseTuint<'t when 't: enum<uint>> x = Enum.Parse(typeof<'t>, x) :?> 't
    static member parse t x = Enum.Parse(t, x)
    static member getName<'t when 't: enum<int>> x = Enum.GetName(typeof<'t>, x)

    static member getAll<'t when 't: enum<int>>() =
        Enum.GetValues typeof<'t>
        |> Seq.cast<int>
        |> Seq.map (fun x -> Enum.getName<'t> x)
        |> Seq.map Enum.parseT<'t>

    // this may be a good idea here: [<RequiresExplicitTypeArguments>]
    static member fromInt<'t when 't: enum<int>>(i: int) =
        Enum.getName<'t> i |> fun x -> Enum.parseT<'t> x

type System.DateTime with






    static member addDays dy (dt: DateTime) = dt.AddDays dy
    static member addHours h (dt: DateTime) = dt.AddHours h

    static member setTime (timePart: DateTime) (datePart: DateTime) =
        if timePart.Kind = datePart.Kind then
            invalidOp "Unable to use two different date kinds to setTime"

        DateTime(
            datePart.Year,
            datePart.Month,
            datePart.Day,
            timePart.Hour,
            timePart.Minute,
            timePart.Second,
            datePart.Kind
        )

    static member addMinutes min (dt: DateTime) = dt.AddMinutes min
    static member toShortDateString(dt: DateTime) = dt.ToShortDateString()
    static member getStartOfMonth(dt: DateTime) = DateTime(dt.Year, dt.Month, 1)
    static member getYear(dt: DateTime) = dt.Year
    static member getMonth(dt: DateTime) = dt.Month
    static member getDay(dt: DateTime) = dt.Day
    static member getHour(dt: DateTime) = dt.Hour
    static member getMinute(dt: DateTime) = dt.Minute

    static member roundTo useRoundUp (ts: TimeSpan) (dt: DateTime) =
        if useRoundUp then
            ts.Ticks - 1L
        else
            ts.Ticks / 2L
        |> flip (+) dt.Ticks
        |> flip (/) ts.Ticks
        |> (*) ts.Ticks
        |> DateTime

    // taken from SO http://stackoverflow.com/a/1595311/57883
    static member getAge (now: DateTime) (dt: DateTime) =
        let age = now.Year - dt.Year

        if (now.Month < dt.Month
            || (now.Month = dt.Month && now.Day < dt.Day)) then
            age - 1
        else
            age

    static member toString (format: string) (dt: DateTime) = dt.ToString(format)

    //public static string CalculateAge(DateTime birthDate, DateTime now)
    static member getAgeDisplay (now: DateTime) (dob: DateTime) =
        let years = DateTime.getAge now dob

        let _days, now =
            let days = now.Day - dob.Day

            if days < 0 then
                let newNow = now.AddMonths(-1)
                let totalDays = now - newNow
                let totalDays = int totalDays.TotalDays
                days + totalDays, newNow
            else
                days, now

        let months =
            ((now.Year - dob.Year) * 12) + now.Month
            - dob.Month

        if (years <= 2) then
            months.ToString() + "m"
        else
            years.ToString() + "y"

    member x.GetAge(now: DateTime) = DateTime.getAge now x

    member x.GetAgeInMonths(now: DateTime) =
        ((now.Year - x.Year) * 12) + now.Month - x.Month

module Time =
    [<CustomComparison>]
    [<CustomEquality>]
    // shadowed constructor/private implementation
    type ValidatedTime =
        private
            {
                _Hour: int
                _Minute: int
            }
        static member op_LessThan(x: ValidatedTime, y: ValidatedTime) =
            x.Hour < y.Hour
            || (x.Hour = y.Hour && x.Minute < y.Minute)

        static member op_GreaterThan(x: ValidatedTime, y: ValidatedTime) =
            x.Hour > y.Hour
            || (x.Hour = y.Hour && x.Minute > y.Minute)

        static member op_GreaterThanOrEqual(x: ValidatedTime, y: ValidatedTime) =
            x.Hour > y.Hour
            || (x.Hour = y.Hour && x.Minute >= y.Minute)

        static member op_LessThanOrEqual(x: ValidatedTime, y: ValidatedTime) =
            x.Hour < y.Hour
            || (x.Hour = y.Hour && x.Minute <= y.Minute)

        static member CanCreate hour minute =
            hour < 24
            && hour >= 0
            && minute >= 0
            && minute < 60

        static member Create hour minute =
            if ValidatedTime.CanCreate hour minute then
                { _Hour = hour; _Minute = minute } |> Some
            else
                None
        // exposing any members is a questionable decision for a Pure ADT, but... maybe this is ok for the way I'm using it
        member x.Hour = x._Hour
        member x.Minute = x._Minute

        override x.ToString() =
            DateTime.Today
            |> DateTime.addHours (float x.Hour)
            |> DateTime.addMinutes (float x.Minute)
            |> DateTime.toString "hh:mmtt"

        override x.GetHashCode() = (x.Hour, x.Minute).GetHashCode()

        override x.Equals obj =
            match obj with
            | :? ValidatedTime as y -> x.Hour = y.Hour && x.Minute = y.Minute
            | _ -> false

        interface IComparable with
            member x.CompareTo(obj: obj) =
                match obj with
                | :? ValidatedTime as y ->
                    if ValidatedTime.op_LessThan (x, y) then
                        -1
                    elif ValidatedTime.op_GreaterThan (x, y) then
                        1
                    else
                        0
                | _ ->
                    raise
                    <| InvalidOperationException("Type must be ValidatedTime")

    [<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
    module ValidatedTime =
        let create hour minute =
            if ValidatedTime.CanCreate hour minute then
                { _Hour = hour; _Minute = minute } |> Some
            else
                None

        let ofDateTime (dt: DateTime) = ValidatedTime.Create dt.Hour dt.Minute

        let ofTimeSpan (ts: TimeSpan) =
            ValidatedTime.Create ts.Hours ts.Minutes

        let getHour (vt: ValidatedTime) = vt.Hour
        let getMinute (vt: ValidatedTime) = vt.Minute
    //    // shadow constructor
//    let ValidatedTime hour minute = ValidatedTime.Create hour minute

    // where only the hour component and below are relevant
    // a timespan of
    type IntraDayTimeSpan =
        | IntraDayTimeSpan of start: ValidatedTime * stop: ValidatedTime
        member x.Start =
            x
            |> function
                | IntraDayTimeSpan (start, _) -> start

        member x.Stop =
            x
            |> function
                | IntraDayTimeSpan (_, stop) -> stop

        member x.Contains(t: ValidatedTime) = x.Start < t && t < x.Stop

        member x.Overlaps(y: IntraDayTimeSpan) =
            x.Contains y.Start
            || x.Contains y.Stop
            || y.Contains x.Start
            || y.Contains x.Stop

    let IntraDayTimeSpan start stop =
        if start < stop then
            IntraDayTimeSpan(start, stop) |> Some
        else
            None

type System.TimeSpan with






    static member getTicks(x: TimeSpan) = x.Ticks
    static member toString (s: string) (x: TimeSpan) = x.ToString(s)


[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>] // for C# access
module DateTime =
    let getAgeDisplay now dob = DateTime.getAgeDisplay now dob

module Choice =
    let inline lift x = Choice1Of2 x

    let inline protect f x =
        try
            f x |> Choice1Of2
        with
        | e -> Choice2Of2 e

    let inline map f =
        function
        | Choice1Of2 x -> f x |> Choice1Of2
        | Choice2Of2 x -> Choice2Of2 x

    let inline bind f =
        function
        | Choice1Of2 x -> f x
        | Choice2Of2 x -> Choice2Of2 x

    let inline mapSnd f =
        function
        | Choice1Of2 x -> Choice1Of2 x
        | Choice2Of2 x -> f x

    let inline bindIsNullOrWhitespace msg =
        function
        | ValueString v -> Choice1Of2 v
        | _ -> Choice2Of2 msg

    let inline iter f =
        function
        | Choice1Of2 x -> f x
        | _ -> ()


//http://stackoverflow.com/a/8227943/57883
let lock (lockobj: obj) f =
    System.Threading.Monitor.Enter lockobj

    try
        f ()
    finally
        System.Threading.Monitor.Exit lockobj

let buildCmdString fs arg i : string * string * obj =
    let applied = sprintf fs arg
    let replacement = (sprintf "{%i}" i)

    let replace target =
        StringHelpers.replace target replacement

    let replaced =
        fs.Value
        |> replace "'%s'"
        |> replace "'%i'"
        |> replace "'%d'"

    applied, replaced, upcast arg


module Option =

    let getOrFailMsg argName (n: 'a option) =
        match n with
        | Some x -> x
        | None -> failwithf "Value expected for %s" argName

    let inline ofTryF f =
        try
            f ()
        with
        | _ -> None

    // for types the compiler insists aren't nullable, but maybe C# is calling
    let ofUnsafeNonNullable x =
        if Object.ReferenceEquals(null, x) then
            None
        else
            Some x

    // primarily for C# / wpf where the framework/ui are the only ones not accounting for this
    let toUnsafeObj x =
        match x with
        | Some x -> box x
        | None -> null

    // let toUnsafeT<'T> (x : 'T option) : 'T =
    //     match x with
    //     | None -> Unchecked.defaultof<_>
    //     | Some x -> x

    let ofChoice1Of2 =
        function
        | Choice1Of2 x -> Some x
        | _ -> None

    let ofChoice2Of2 =
        function
        | Choice2Of2 x -> Some x
        | _ -> None

module Diagnostics =
    type AttrDict = Map<string, string>

    let swallow f =
        try
            f () |> Some
        with
        | ex ->
            printfn "neverthrow caught %s" ex.Message
            None

    let tryAsyncCatch f =
        f |> Async.Catch |> Async.Ignore |> Async.Start

    let makeDatedFilename (dt: DateTime) =
        let dt =
            StringHelpers.toFormatString "yyyyMMdd" dt

        sprintf "DebugLog_%s.txt" dt

    let logToFile filename (dt: DateTime) topic (attrs: AttrDict) s =
        let pid, sessionId =
            try
                let proc =
                    System.Diagnostics.Process.GetCurrentProcess()

                proc.Id, proc.SessionId

            with
            | _ -> 0, 0

        let baseAttrs =
            Map [ "dt", sprintf "%A" dt
                  "pid", sprintf "%i" pid
                  "sId", sprintf "%i" sessionId ]

        let attrs =
            attrs
            |> Map.merge baseAttrs
            |> Map.toSeq
            |> Seq.map (fun (k, v) -> sprintf "%s='%s'" k (v |> replace "'" "&apos;"))
            |> String.concat " "

        let topic =
            match topic with
            | Some t -> t
            | _ -> "Message"

        let msg =
            sprintf "<%s %s>%s</%s>%s" topic attrs s topic Environment.NewLine

        printfn "logging to file: %s" msg
        System.IO.File.AppendAllText(filename, msg)

    let logToEventLog appName (s: string) : Result<unit, exn> option =
#if NETSTANDARD
        try
            use eventLog = new EventLog("Application")

            eventLog.Source <-
                appName
                |> Option.ofValueString
                |> Option.defaultValue "Application"

            eventLog.WriteEntry s
            Some(Ok())
        with
        | ex -> Some(Error ex)
#else
        None
#endif
