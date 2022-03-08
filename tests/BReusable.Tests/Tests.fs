module BReusable.ReuseablesTests

open System
open Expecto
// open ExpectoFsCheck

open BReusable
open BReusable.Reusables

[<Measure>]
type cm

let makeNoThrowTest title f =
    testCase title <| fun _ -> f (box "") |> ignore

let inline makeThrowTest title f =
    testCase title
    <| fun _ -> Expect.throws (fun () -> f (box null) |> ignore) null


[<Tests>]
let uncategorizedTests =
    testList
        "BReusable"
        [
            testList
                "guardAgainstNull"
                [
                    makeNoThrowTest "can be happy" (guardAgainstNull "fail if thrown")
                    makeThrowTest "can throw" (guardAgainstNull "test passed")
                ]
            testList
                "|GuardNull|"
                [
                    makeNoThrowTest "can be happy" ((|GuardNull|) "test failed")
                    makeThrowTest "can throw" ((|GuardNull|) "test passed")
                ]
        ]

module ZipEquality =
    open ZipEquality

    let inequalityF (l, r) =
        if l <> r then
            Some "inequality"
        else
            None

    let inline noErrors (_, _) : string option = None
    let inline allErrors (msg: string) (_, _) = Some msg

    let makeNullTest (l: _ seq, r: _ seq) =
        match l, r with
        | null, _
        | _, null ->
            fun msg ->
                testCase msg
                <| fun _ ->
                    match foldEquals inequalityF (l, r) with
                    | NullInput _ -> ()
                    | x -> invalidOp (sprintf "test failed:%A" x)
        | _ -> invalidOp "neither sequence was null"

    let runLengthTest (l: _ seq, r: _ seq) fCont =
        match foldEquals noErrors (l, r) with
        | LengthError (li, ri) -> fCont (li, ri)
        | x -> invalidOp (sprintf "test failed:%A" x)
    // expect the request to be LengthError, if not fail, if so fCont
    let makeLengthTest title (l: _ seq, r: _ seq) fCont =
        testCase title
        <| fun _ -> runLengthTest (l, r) fCont

    let makeLengthTests title data fCont =
        testList
            title
            (data
             |> List.map (fun (caseTitle, (l, r)) -> makeLengthTest caseTitle (l, r) fCont))

    [<Tests>]
    let zipEqualityTests =
        testList
            "ZipEqualityTests"
            [
                // test the test creators
                testList
                    "local helpers"
                    [
                        testCase "makeNullTest fails fast"
                        <| fun _ ->
                            null
                            |> Expect.throws (fun () -> makeNullTest (Seq.empty, Seq.empty) |> ignore)

                        // anything other than a LengthError result should throw
                        // assume other tests will cover all possibilities, but make 1 semi-duplicate test
                        testCase "runLengthTest empty"
                        <| fun _ ->
                            null
                            |> Expect.throws (fun () -> runLengthTest ([], []) ignore)
                        testCase "runLengthTest equal"
                        <| fun _ ->
                            null
                            |> Expect.throws (fun () -> runLengthTest ([ 1 ], [ 2 ]) ignore)
                    ]
                testList
                    "foldEquals"
                    [

                        // guard clause tests
                        makeNullTest (null, null) "both null"
                        makeNullTest (null, [ 1 ]) "left null"
                        makeNullTest ([ 1 ], null) "right null"

                        // result case tests
                        testCase "empties"
                        <| fun _ ->
                            match foldEquals
                                (fun _ -> invalidOp "Empty should never call this fun")
                                (Seq.empty, Seq.empty) with
                            | BothEmpty -> ()
                            | x -> invalidOp (sprintf "test failed:%A" x)

                        makeLengthTests
                            "lengths"
                            [
                                "leftLonger1", (seq [ 1 ], Seq.empty)
                                "leftLonger2", (seq [ 1; 2 ], Seq.empty)
                                "rightLonger1", (Seq.empty, seq [ 1 ])
                                "rightLonger2", (Seq.empty, seq [ 1; 2 ])
                            ]
                            ignore

                        testCase "foundError"
                        <| fun _ ->
                            let expectedMsg = "Yay found it"

                            match foldEquals (allErrors expectedMsg) ([ 1 ], [ 1 ]) with
                            | FoundError actual when (1, expectedMsg) = actual -> ()
                            | x -> invalidOp (sprintf "test failed:%A" x)

                        testCase "equal length, completed"
                        <| fun _ ->
                            match foldEquals inequalityF ([ 1; 2 ], [ 1; 2 ]) with
                            | FoldEqualResult.Completed -> ()
                            | x -> invalidOp (sprintf "test failed:%A" x)

                            ()
                    ]
            ]

module ResultTests =
    type RString = Result<string, string>

    [<Tests>]
    let resultTests =
        testList
            "Result"
            [
                testList
                    "ofOption"
                    [
                        testCase "happy"
                        <| fun _ ->
                            let msg = "hello"
                            let expected: RString = Ok msg

                            let actual: RString =
                                Some msg |> Result.ofOption "Option was none"

                            Expect.equal actual expected null
                        testCase "err"
                        <| fun _ ->
                            let msg = "world"
                            let expected: RString = Error msg
                            let actual: RString = None |> Result.ofOption msg
                            Expect.equal actual expected null
                    ]
                testList
                    "either"
                    [
                        testCase "happy"
                        <| fun _ ->
                            let msg = "hello world"
                            let expected = Ok msg

                            let actual =
                                Ok msg
                                |> Result.either Ok (TestHelper.failIfCalled "unhappy path")

                            Expect.equal actual expected null

                        testCase "unhappy"
                        <| fun _ ->
                            let msg = "hello world"
                            let expected = Error msg

                            let actual =
                                Error msg
                                |> Result.either (TestHelper.failIfCalled "happy path") Error

                            Expect.equal actual expected null
                    ]

                testCase "switch is happy"
                <| fun _ ->
                    let msg = "hello world"
                    let expected = Ok msg
                    let f = Result.switch id
                    let actual = f msg
                    Expect.equal actual expected null

                testCase "bind' is happy"
                <| fun _ ->
                    let expected = Ok 2

                    let actual =
                        Error() |> Result.bind' (fun () -> expected)

                    Expect.equal actual expected null
                testList
                    "tryCatch"
                    [

                        testCase "happy no throw"
                        <| fun _ ->
                            let expected = Ok 5
                            let actual = () |> Result.tryCatch (fun () -> 5) id
                            Expect.equal actual expected null
                            ()

                        testCase "happy ex path"
                        <| fun _ ->
                            let expected = Error 3

                            let actual =
                                ()
                                |> Result.tryCatch (fun () -> invalidOp "iop") (fun _ -> 3)

                            Expect.equal actual expected null
                            ()
                    ]

                testList
                    "toOkOption"
                    [
                        testCase "happy"
                        <| fun _ ->
                            let expected = Some 5
                            let actual = Ok 5 |> Result.toOkOption
                            Expect.equal actual expected null
                        testCase "unhappy"
                        <| fun _ ->
                            let expected = None
                            let actual = Error 5 |> Result.toOkOption
                            Expect.equal actual expected null
                    ]

                testList
                    "toErrorOption"
                    [
                        // testCase "shappy" <| Expect.simpleEqual (Some 5) Result.toErrorOption (Error 5)
                        testCase "happy errors"
                        <| fun _ ->
                            let expected = Some 5
                            let actual = Error 5 |> Result.toErrorOption
                            Expect.equal actual expected null
                        testCase "unhappy"
                        <| fun _ ->
                            let expected = None
                            let actual = Ok 5 |> Result.toErrorOption
                            Expect.equal actual expected null
                    ]

                testList
                    "forAllF"
                    [
                        testCase "happy"
                        <| fun _ ->
                            let expected = Ok [ 5; 7 ]

                            let actual =
                                [ Ok 5; Ok 7 ]
                                |> Result.forAllF (Result.isHappy)
                                |> Result.map List.ofSeq

                            Expect.equal actual expected null
                        testCase "unhappy"
                        <| fun _ ->
                            let expected = Error [ 5; 7 ]

                            let actual =
                                [ Error 5; Error 7 ]
                                |> Result.forAllF (
                                    function
                                    | Ok _ -> true
                                    | Error _ -> false
                                )
                                |> Result.mapError List.ofSeq

                            Expect.equal actual expected null
                    ]

            ]

module ResultBuilderTests =
    type RString = Result<string, string>
    type RInt = Result<int, int>

    [<AllowNullLiteral>]
    type SomeDisp<'t>(x: 't, f) =
        member _.Value = x

        interface System.IDisposable with
            member _.Dispose() = f ()

    [<Tests>]
    let rbTests =
        testList
            "ResultBuilder"
            [
                testCase "Return"
                <| fun () ->
                    let expected = Ok 5
                    let actual = result.Return 5
                    Expect.equal actual expected null
                testCase "ReturnFrom"
                <| fun () ->
                    let expected = Ok 5
                    let actual = result.ReturnFrom expected
                    Expect.equal actual expected null
                testCase "Bind"
                <| fun () ->
                    let expected = Ok 5
                    let actual = result.Bind(Ok 5, Ok)
                    Expect.equal actual expected null
                testCase "Bind2"
                <| fun () ->
                    let expected = Ok 5
                    let actual = result.Bind((Some 5, Error 3), Ok)
                    Expect.equal actual expected null
                testCase "Zero"
                <| fun () ->
                    let expected = None
                    let actual = result.Zero()
                    Expect.equal actual expected null

                testCase "Combine"
                <| fun () ->
                    let expected = Ok "5"
                    let actual: RString = result.Combine(Ok "5", Ok)
                    Expect.equal actual expected null

                testCase "Delay"
                <| fun () ->
                    let expected = 5
                    let actual = result.Delay(fun () -> 5) ()
                    Expect.equal actual expected null
                testCase "Run"
                <| fun () ->
                    let expected = 5
                    let actual = result.Run(fun () -> 5)
                    Expect.equal actual expected null

                testCase "TryWith"
                <| fun () ->
                    let expected = Ok 5
                    let actual = result.TryWith(Ok 5, Error)
                    Expect.equal actual expected null
                testCase "TryFinally"
                <| fun () ->
                    let expectedr = Ok 3
                    let expectedd = 5
                    let mutable actual = -1
                    let f () = actual <- expectedd
                    // let disp = {
                    //     new System.IDisposable with
                    //         member _.Dispose() =
                    // }
                    let actualr = result.TryFinally(expectedr, f)
                    Expect.equal actualr expectedr "result"
                    Expect.equal actual expectedd "fin"

                testCase "Using"
                <| fun () ->
                    let expected = 5
                    let mutable actual = -1

                    use disp =
                        new SomeDisp<_>(expected, (fun () -> actual <- expected))

                    let actualr: RInt =
                        result.Using(disp, Ok)
                        |> Result.map (fun x -> x.Value)

                    Expect.equal actualr (Ok expected) "result"
                testCase "While"
                <| fun () ->
                    let expected = Ok()

                    let actual =
                        result.While((fun () -> false), (fun _ -> expected))

                    Expect.equal actual expected null
                testCase "For"
                <| fun () ->
                    let expected = Ok()
                    let actual = result.For([ 1 .. 3 ], id)
                    Expect.equal actual expected null

            ]

module MatchHelperTests =
    open MatchHelpers

    [<Tests>]
    let mhTests =
        testList
            "MatchHelpers"
            [
                testList
                    "IsTrue"
                    [
                        let sut f =
                            function
                            | IsTrue f x -> Some x
                            | _ -> None

                        testCase "happy"
                        <| fun () ->
                            let v = 5
                            let expected = Some v
                            let actual = sut ((=) v) 5
                            Expect.equal actual expected null

                        testCase "unhappy"
                        <| fun () ->
                            let v = 1
                            let expected = None
                            let actual = sut ((<>) v) v
                            Expect.equal actual expected null
                    ]
                testList
                    "IsAnyOf"
                    [
                        let sut items =
                            function
                            | IsAnyOf items x -> Some x
                            | _ -> None

                        testCase "happy"
                        <| fun () ->
                            let v = 5
                            let expected = Some 5
                            let actual = 5 |> sut [ 1; 5; 6 ]
                            Expect.equal actual expected null

                        testCase "unhappy"
                        <| fun () ->
                            let v = 5
                            let expected = None
                            let actual = 5 |> sut [ 1; 2; 3 ]
                            Expect.equal actual expected null
                    ]
                testList
                    "IsGreaterThan"
                    [
                        let sut x =
                            function
                            | GreaterThan x y -> Some y
                            | _ -> None

                        testCase "happy"
                        <| fun () ->
                            let v = 5
                            let expected = Some()
                            let actual = v |> sut 4
                            Expect.equal actual expected null

                        testCase "unhappy"
                        <| fun () ->
                            let v = 5
                            let expected = None
                            let actual = v |> sut 6
                            Expect.equal actual expected null
                    ]
            ]

module FunctionalHelpersAutoTests =
    open FunctionalHelpersAuto

    [<Tests>]
    let fhTests =
        testList
            "FunctionalHelpersAuto"
            [
                testList
                    "cprintf"
                    [

                    ]
                testList
                    "cprintfn"
                    [

                    ]
                testList
                    "teeTuple"
                    [
                        testCase "happy"
                        <| fun () ->
                            let expected = 5, 25

                            let actual: int * int =
                                fst expected |> teeTuple (fun i -> i * i)

                            Expect.equal actual expected null
                            ()
                    ]
                testList
                    "tee"
                    [
                        testCase "tee"
                        <| fun () ->
                            let expected = 5
                            let actual = expected |> tee ignore
                            Expect.equal actual expected null
                    ]
                testList
                    "clamp"
                    [
                        testCase "happy"
                        <| fun () ->
                            let expected = 5
                            let actual = clamp 0 10 5
                            Expect.equal actual expected null
                        testCase "inclusiveLower"
                        <| fun () ->
                            let expected = 1
                            let actual = clamp 1 10 1
                            Expect.equal actual expected null
                        testCase "inclusiveUpper"
                        <| fun () ->
                            let expected = 10
                            let actual = clamp 1 10 10
                            Expect.equal actual expected null
                        testCase "lowerBound"
                        <| fun () ->
                            let expected = 1
                            let actual = clamp 1 10 0
                            Expect.equal actual expected null
                        testCase "upperBound"
                        <| fun () ->
                            let expected = 10
                            let actual = clamp 1 10 11
                            Expect.equal actual expected null
                        testCase "single"
                        <| fun () ->
                            let expected = 10
                            let actual = clamp 10 10 10
                            Expect.equal actual expected null
                    ]
                testProperty "flip"
                <| fun (x: int, y: int) ->
                    let expected = y, x
                    let unexpected = x, y
                    let actual = flip (fun a b -> a, b) x y

                    if x <> y then
                        Expect.notEqual actual unexpected "unex"

                    Expect.equal actual expected "exp"

                testCase "uncurry"
                <| fun () ->
                    let expected = 11
                    let actual = uncurry (+) (5, 6)
                    Expect.equal actual expected null
                testCase "getType"
                <| fun () ->
                    let expected = typeof<int>
                    let actual = 5 |> getType
                    Expect.equal actual expected null

                testCase "downcastX"
                <| fun () ->
                    let expected = 5
                    let actual = 5<cm> |> downcastX<int>
                    Expect.equal actual expected null

                testCase "castAs"
                <| fun () ->
                    let expected = 5
                    let actual = box expected |> castAs<int>
                    Expect.equal actual (Some expected) null

                testList
                    "NonNull|UnsafeNull"
                    [

                        testCase "nonnull"
                        <| fun () ->
                            let expected = 5

                            let actual =
                                (match box 5 with
                                 | NonNull as v -> Some v
                                 | _ -> None)
                                |> Option.bind castAs<int>

                            Expect.equal actual (Some expected) null

                        testCase "unsafenull"
                        <| fun () ->
                            let expected = None

                            let actual =
                                (match null with
                                 | NonNull as v -> Some v
                                 | _ -> None)

                            Expect.equal actual expected null

                    ]

                testCase "cast"
                <| fun () ->
                    let expected = 5
                    let actual = box 5 |> cast<int>
                    Expect.equal actual expected null

                testCase "swallow"
                <| fun () -> swallow (fun () -> invalidOp "bad")

                testCase "makeUnsafeDisposal"
                <| fun () ->
                    let expected = 5
                    let mutable actual = -1
                    using (makeUnsafeDisposal (fun () -> actual <- expected)) ignore
                    Expect.equal actual expected null

                testCase "disposal"
                <| fun () ->
                    let expected = 5
                    let mutable actual = -1
                    using (disposable (fun () -> actual <- expected)) ignore
                    Expect.equal actual expected null
            ]

[<Tests>]
let tuple2Tests =
    testList
        "Tuple2"
        [
            testCase "replicate"
            <| fun () ->
                let expected = 5, 5
                let actual = fst expected |> Tuple2.replicate
                Expect.equal actual expected null
            testCase "fromCurry"
            <| fun () ->
                let v = 5
                let expected = v, v
                let actual = Tuple2.fromCurry 5 5
                Expect.equal actual expected null
            testCase "curry"
            <| fun () ->
                let v = 5
                let expected = v, v
                let actual = Tuple2.curry id v v
                Expect.equal actual expected null
            testCase "swap"
            <| fun () ->
                let expected = 2, 1
                let actual = Tuple2.swap (1, 2)
                Expect.equal actual expected null
            testCase "mapFst"
            <| fun () ->
                let expected = 2, 1
                let actual = Tuple2.mapFst ((+) 1) (1, 1)
                Expect.equal actual expected null
            testCase "mapSnd"
            <| fun () ->
                let expected = 1, 2
                let actual = Tuple2.mapSnd ((+) 1) (1, 1)
                Expect.equal actual expected null

            testCase "extendFst" // f (x,y) = f (x,y), y
            <| fun () ->
                let expected = 7, 4

                let actual =
                    Tuple2.extendFst (fun (a, b) -> a + b) (3, 4)

                Expect.equal actual expected null

            testCase "extendSnd" // f (x,y) = f (x,y), y
            <| fun () ->
                let expected = 3, 7

                let actual =
                    Tuple2.extendSnd (fun (a, b) -> a + b) (3, 4)

                Expect.equal actual expected null
        // let optionOfFst f (x,y) =
        ]
