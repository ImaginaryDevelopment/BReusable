module BReusable.Reflection

open System
open System.Reflection
open System.Diagnostics
open BReusable.Reusables

open Microsoft.FSharp.Reflection

// active pattern, based on http://stackoverflow.com/a/25243799/57883
module Unboxing =
    let (|As|_|) (p: 'T) : 'U option =
        let p = p :> obj
        // if p :? 'U then Some (p :?> 'U) else None
        match p with
        | :? 'U as v -> Some v
        | _ -> None

    let getStringMaybe (o: obj) =
        match o with
        | :? string as s -> Some s
        | _ -> None

    let getIntMaybe (o: obj) =
        match o with
        | :? Nullable<int> as value -> Option.ofNullable value
        | :? Option<int> as value -> value
        | :? int as value -> Some value
        | _ -> None

    let getBoolMaybe (o: obj) =
        match o with
        | :? Nullable<bool> as value -> Option.ofNullable value
        | :? Option<bool> as value -> value
        | :? bool as value -> Some value
        | _ -> None

let rec typeMatch t (g: Type) =
    if t = typeof<obj> then
        None
    elif g.IsInterface then
        let ints =
            if t.IsInterface then
                [| t |]
            else
                t.GetInterfaces()

        ints
        |> Seq.tryPick (fun t ->
            if t.GetGenericTypeDefinition() = g then
                Some(t.GetGenericArguments())
            else
                None
        )
    elif t.IsGenericType
         && t.GetGenericTypeDefinition() = g then
        t.GetGenericArguments() |> Some
    else
        typeMatch (t.BaseType) g

/// for when you need to see if something matches and expected Generic Type Definition ( you don't know "'t" but don't care)
/// Sample (tested good) usage:
/// match list with
/// | IsTypeOf (isType:List<_>) typeArgs -> sprintf "Yay matched1 : %A" typeArgs \r\n
/// | _ -> "boo"
/// Also works for some types:
/// | IsTypeOf (null:List<_>) typeArgs -> sprintf "Yay matched: %A" typeArgs
// returns the generic arguments list of the type that matches
let (|IsTypeOf|_|) (_: 'a) (value: obj) =
    let typeDef = typedefof<'a>

    if obj.ReferenceEquals(value, null) then
        None
    else
        let typ = value.GetType()

        if typ.Name = "RuntimeType" then
            failwithf "Invalid use of |IsTypeOf|"
        //            let gtd = if typ.IsGenericType then typ.GetGenericTypeDefinition() |> Some else None
        if typ.IsGenericType
           && typ.GetGenericTypeDefinition() = typeDef then
            Some(typ.GetGenericArguments())
        else
            let typeArgs = typeMatch typ typeDef
            typeArgs

// for when you don't have a value or you want a switch on an instance of Type
// or you want to unbox as one of a number of possible types
// do not use where `| :?` is appropriate
let (|TypeOf|_|) (_: 'a) t =
    if t = typeof<'a> then
        Some()
    else
        //printfn "did not match %A to %A" typeof<'a> t
        None

// instead of null in TypeOf or TypeDef matches for types that don't allow null
let isType<'a> = Unchecked.defaultof<'a>

// if you want to know an instance of System.Type is Nullable, gives the T
let (|NullableT|_|) (t: Type) =
    if t.IsGenericType
       && t.GetGenericTypeDefinition() = typedefof<Nullable<_>> then
        Some t.GenericTypeArguments.[0]
    else
        None

let getTypeString =
    function
    | NullableT t -> sprintf "Nullable<%s>" t.Name
    | t when t.IsValueType -> t.Name
    | TypeOf (isType: Guid)
    | TypeOf (isType: String) as t -> t.Name
    | x ->
        printfn "No print type for %s" x.FullName
        x.Name

[<NoEquality; NoComparison>]
type PropWrapper<'TProp> =
    {
        PropertyInfo: PropertyInfo
        Getter: unit -> 'TProp
        Setter: 'TProp -> unit
    }

let generatePropWrapper<'T, 'TProp> (x: 'T) (prop: PropertyInfo) : PropWrapper<'TProp> option =
    if prop.CanRead && prop.CanWrite then
        {
            PropertyInfo = prop
            Getter = (fun () -> prop.GetValue x :?> 'TProp)
            Setter = fun (value: 'TProp) -> prop.SetValue(x, value)
        }
        |> Some
    else
        None

// not happy about traversal order
let getTypes<'t> : Type seq =
    let t = typeof<'t>

    let rec getTypes (t: Type) =
        seq {
            yield t

            yield!
                t.FindInterfaces(null, null)
                |> Seq.collect getTypes

            if not <| isNull t.BaseType then
                yield! getTypes t.BaseType
        }

    getTypes t
    |> Seq.map (fun x ->
        printfn "Getting type %s" x.Name
        x
    )

// worked with Task<int> and Task<obj>
let (|TypeDefOf|_|) (x: 'a) t =
    if t = typeof<'a> then
        Some()
    elif
        getTypes<'a>
        |> Seq.exists ((|TypeOf|_|) x >> Option.isSome)
    then
        Some()
    else
        None


let rec getMethod recurse name (t: Type) =
    seq {
        let m = t.GetMethod(name)
        if not <| isNull m then yield t, m

        if recurse then
            yield!
                t.GetInterfaces()
                |> Seq.collect (getMethod recurse name)
    }

let rec getMethods recurse (t: Type) =
    seq {
        yield (t, t.GetMethods())

        if recurse then
            yield!
                t.GetInterfaces()
                |> Seq.collect (getMethods recurse)
    }

// primarily for use hand-in-hand with the 'Nullish' active pattern
//unhandled: _ Nullable option
/// for boxed objects that may be 'Valueable`
let rec getReflectionValueOpt (genTypeOpt: Type option) (typeOpt: Type option) (o: obj) =
    match o, genTypeOpt, typeOpt with
    | null, _, _ -> None
    | _, Some gt, _ ->
        // based on http://stackoverflow.com/a/13367848/57883
        match gt.GetProperty "Value" with
        | null -> None
        | prop ->
            let v = prop.GetValue(o, null)
            Some v
    | _, _, Some t ->
        match t.IsGenericType with
        | true -> getReflectionValueOpt typeOpt (t.GetGenericTypeDefinition() |> Some) o
        | false -> Some o
    | _, _, None -> getReflectionValueOpt None (o.GetType() |> Some) o

//method taken from http://stackoverflow.com/q/4604139/57883
let methodSourceName (mi: MemberInfo) =
    mi.GetCustomAttributes(true)
    |> Array.tryPick (
        function
        | :? CompilationSourceNameAttribute as csna -> Some(csna)
        | _ -> None
    )
    |> function
        | Some (csna) -> csna.SourceName
        | None -> mi.Name

module Assemblies =
    open System.IO

    // http://stackoverflow.com/a/28319367/57883
    let getAssemblyFullPath (assembly: Assembly) =
        let codeBaseFailedAssert () =
            Debug.Assert(false, "CodeBase evaluation failed! - Using Location as fallback.")

        let fullPath =
            match assembly.CodeBase with
            | null ->
                codeBaseFailedAssert ()
                assembly.Location
            | codeBasePseudoUrl ->
                let filePrefix3 = @"file:///"

                if codeBasePseudoUrl.StartsWith filePrefix3 then
                    let sPath =
                        codeBasePseudoUrl.Substring filePrefix3.Length

                    let bsPath = sPath.Replace('/', '\\')
                    bsPath
                else
                    codeBaseFailedAssert ()
                    assembly.Location

        fullPath

    type ReflectionVersionInfo =
        {
            Name: string
            Path: string
            Version: string
            FileVersion: string
            ModifiedDateUtc: DateTime
            CreatedDateUtc: DateTime
        }

    let getAssemblyVersion asm =
        try
            let p = getAssemblyFullPath asm
            let n = asm.GetName()
            let fi = FileInfo(p)

            Choice1Of2
                {
                    Name = n.Name
                    Path = p
                    Version = n.Version |> string
                    FileVersion = (FileVersionInfo.GetVersionInfo p).FileVersion
                    ModifiedDateUtc = fi.LastWriteTimeUtc
                    CreatedDateUtc = fi.CreationTimeUtc
                }
        with
        | ex -> Choice2Of2 ex

module NonPublicAccess =
    // via http://www.fssnip.net/2V author: Tomas Petricek http://stackoverflow.com/users/33518/tomas-petricek
    // let us access public or private properties or methods dynamically
    // Various flags that specify what members can be called
    // NOTE: Remove 'BindingFlags.NonPublic' if you want a version
    // that can call only public methods of classes
    let staticFlags =
        BindingFlags.NonPublic
        ||| BindingFlags.Public
        ||| BindingFlags.Static

    let instanceFlags =
        BindingFlags.NonPublic
        ||| BindingFlags.Public
        ||| BindingFlags.Instance

    let private ctorFlags = instanceFlags
    let inline asMethodBase (a: #MethodBase) = a :> MethodBase

    // The operator takes just instance and a name. Depending on how it is used
    // it either calls method (when 'R is function) or accesses a property
    let (?) (o: obj) name : 'R =
        // The return type is a function, which means that we want to invoke a method
        if FSharpType.IsFunction(typeof<'R>) then
            // Get arguments (from a tuple) and their types
            let argType, _resultType =
                FSharpType.GetFunctionElements(typeof<'R>)
            // Construct an F# function as the result (and cast it to the
            // expected function type specified by 'R)
            FSharpValue.MakeFunction(
                typeof<'R>,
                fun args ->
                    // We treat elements of a tuple passed as argument as a list of arguments
                    // When the 'o' object is 'System.Type', we call static methods
                    let methods, instance, args =
                        let args =
                            // If argument is unit, we treat it as no arguments,
                            // if it is not a tuple, we create singleton array,
                            // otherwise we get all elements of the tuple
                            if argType = typeof<unit> then
                                [||]
                            elif not (FSharpType.IsTuple(argType)) then
                                [| args |]
                            else
                                FSharpValue.GetTupleFields(args)
                        // Static member call (on value of type System.Type)?
                        if (typeof<System.Type>)
                            .IsAssignableFrom(o.GetType()) then
                            let methods =
                                (unbox<Type> o).GetMethods(staticFlags)
                                |> Array.map asMethodBase

                            let ctors =
                                (unbox<Type> o).GetConstructors(ctorFlags)
                                |> Array.map asMethodBase

                            Array.concat [ methods; ctors ], null, args
                        else
                            o.GetType().GetMethods(instanceFlags)
                            |> Array.map asMethodBase,
                            o,
                            args
                    // A simple overload resolution based on the name and the number of parameters only
                    // TODO: This doesn't correctly handle multiple overloads with same parameter count
                    let methods =
                        [
                            for m in methods do
                                if m.Name = name
                                   && m.GetParameters().Length = args.Length then
                                    yield m
                        ]
                    // If we find suitable method or constructor to call, do it!
                    match methods with
                    | [] -> failwithf "No method '%s' with %d arguments found" name args.Length
                    | _ :: _ :: _ -> failwithf "Multiple methods '%s' with %d arguments found" name args.Length
                    | [ :? ConstructorInfo as c ] -> c.Invoke(args)
                    | [ m ] -> m.Invoke(instance, args)
            )
            |> unbox<'R>
        else
            // The result type is not an F# function, so we're getting a property
            // When the 'o' object is 'System.Type', we access static properties
            let typ, flags, instance =
                if (typeof<System.Type>)
                    .IsAssignableFrom(o.GetType()) then
                    unbox o, staticFlags, null
                else
                    o.GetType(), instanceFlags, o
            // Find a property that we can call and get the value
            let prop = typ.GetProperty(name, flags)

            if isNull prop && isNull instance then
                // The syntax can be also used to access nested types of a type
                let nested =
                    typ.Assembly.GetType(typ.FullName + "+" + name)
                // Return nested type if we found one
                if isNull nested then
                    failwithf "Property or nested type '%s' not found in '%s'." name typ.Name
                elif not ((typeof<'R>).IsAssignableFrom(typeof<System.Type>)) then
                    let rname = (typeof<'R>.Name)
                    failwithf "Cannot return nested type '%s' as a type '%s'." nested.Name rname
                else
                    nested |> box |> unbox<'R>
            else
                // Call property and return result if we found some
                let meth = prop.GetGetMethod(true)

                if isNull prop then
                    failwithf "Property '%s' found, but doesn't have 'get' method." name

                try
                    meth.Invoke(instance, [||]) |> unbox<'R>
                with
                | _ -> failwithf "Failed to get value of '%s' property (of type '%s')" name typ.Name


open System.Linq.Expressions
open Microsoft.FSharp.Quotations.Patterns
// until we get the `nameof()` operator
module QuotationHelpers =
    open System.Reflection

    let rec getQuoteMemberName expr =
        match expr with
        | Call (_, mi, _) -> methodSourceName mi
        | Lambda (_, expr) -> getQuoteMemberName expr
        | Coerce (expr, _) -> getQuoteMemberName expr
        | PropertyGet (_, p, _) -> p.Name
        | FieldGet (_, fi) -> fi.Name
        | ValueWithName (_, _, n) -> n
        | _ -> failwithf "Method is not a call expression"

    let getQuoteMemberNameT<'t> (expr: Quotations.Expr<'t -> _>) =
        let expr = expr :> Quotations.Expr
        getQuoteMemberName expr

    let getTypeName<'t> =
        match <@ fun (_: 't) -> () @> with
        | Lambda (x, _expr) -> x.Type.Name
        | x -> failwithf "getTypeName failed for %A" x

    // this is unused, and it's value is questionable
    type Microsoft.FSharp.Core.Option<'t> with
        static member OfT (targetOptionType: Type) value =
            let someMethod = targetOptionType.GetMethod("Some")
            let wrappedValue = someMethod.Invoke(null, [| value |])
            wrappedValue

    let (|NullableNull|NullableValue|) (x: _ Nullable) =
        if x.HasValue then
            NullableValue x.Value
        else
            NullableNull

    // Nullish covers actual null, NullableNull, and None
    let (|Nullish|NullableObj|SomeObj|GenericObj|NonNullObj|) (o: obj) =
        // consider including empty string in nullish?
        Debug.Assert(Nullable<int>() |> box |> isNull)
        Debug.Assert(None |> box |> isNull)

        match isNull o with
        | true -> Nullish
        | false ->
            let t = o |> getType
            // a more direct translation would have been t |> Nullable.GetUnderlyingType|> isNull |> not
            match t.IsGenericType with
            | false -> NonNullObj
            | true ->
                let genericType = t.GetGenericTypeDefinition()

                if genericType = typedefof<Nullable<_>> then
                    NullableObj genericType
                elif genericType = typedefof<Option<_>> then
                    SomeObj genericType
                else
                    GenericObj genericType

    // to eliminate getXXX (Nullable())
    let nullable = Nullable()

    // this may not be even remotely useful, you can just |> Option.ofNullable
    module Nullable =
        //    [<AutoOpen>]
        //    module BReusable =
        let getValueOrDefault n =
            match n with
            | NullableValue x -> x
            | NullableNull -> n.GetValueOrDefault()

        //let create x = System.Nullable x (* just use Nullable in and of itself, create is unnecessary. perhaps this is because of F# 4? *)
        let getOrDefault v n =
            match n with
            | NullableValue x -> x
            | _ -> v

        let getOrElse (v: 'a Lazy) (n: 'a Nullable) =
            match n with
            | NullableValue x -> x
            | _ ->
                match v with
                | Lazy v -> v

        let get (x: _ Nullable) = x.Value
        let fromOption = Option.toNullable
        let toOption = Option.ofNullable

        let bind f x =
            match x with
            | NullableNull -> Nullable()
            | NullableValue v -> f v

        let hasValue (x: _ Nullable) = x.HasValue
        let isNull (x: _ Nullable) = not x.HasValue
        let count (x: _ Nullable) = if x.HasValue then 1 else 0

        let fold f state x =
            match x with
            | NullableNull -> state
            | NullableValue v -> f state v

        let foldBack f x state =
            match x with
            | NullableNull -> state
            | NullableValue _ -> f x state

        let exists p x =
            match x with
            | NullableNull -> false
            | NullableValue _ -> p x

        let forall p x =
            match x with
            | NullableNull -> true
            | NullableValue _ -> p x

        let iter f x =
            match x with
            | NullableNull -> ()
            | NullableValue v -> f v

        let map f x =
            match x with
            | NullableNull -> Nullable()
            | NullableValue v -> Nullable(f v)

        let toArray x =
            match x with
            | NullableNull -> Array.empty
            | NullableValue v -> Array.singleton v

        let toList x =
            match x with
            | NullableNull -> List.empty
            | NullableValue v -> List.singleton v

        let liftNullable op (a: _ Nullable) (b: _ Nullable) =
            if a.HasValue && b.HasValue then
                Nullable(op a.Value b.Value)
            else
                Nullable()

        let mapBoolOp op a b =
            match a, b with
            | NullableValue x, NullableValue y -> op x y
            | _ -> false

        let bindf (n: _ Nullable) f ``default`` =
            if n.HasValue then
                f n.Value
            else
                ``default``

    // things I'm not sure are a good idea but enable things that otherwise might not be possible
// things that create a buttload of complexity one place, to reduce boilerplate or lessen complexity elsewhere
    module Ideas =
        let (|AsString|_|) (x: obj) =
            match x with
            | :? String as y -> Some y
            | _ -> None

    ()

    // is this even remotely useful, when you have quotation helpers above?
    module ExpressionHelpers =
        open System.Reflection

        let maybeUnary (exp: Expression<_>) =
            match exp.Body with
            | :? UnaryExpression as uExpr -> uExpr.Operand
            | x -> x

        let inline getMember (expr: Expression<_>) =
            if expr = null then
                raise <| System.ArgumentNullException("expr")
            //if expr.Body :? MemberExpression = false then raise <| System.ArgumentException("The body must be a member expression")
            let memExpr = maybeUnary expr :?> MemberExpression

            if memExpr = null then
                raise
                <| System.ArgumentException("The body must be a member expression")

            memExpr.Member

        let inline GetMemberName (expr: Expression<_>) = (getMember expr).Name

        let inline GetMemberTAct<'t> (expr: Expression<Action<'t>>) = getMember expr

        let inline GetMemberTF (expr: Expression<Func<_>>) = getMember expr

        let inline GetMemberTF2<'t> (expr: Expression<Func<'t, _>>) = getMember expr

        let getMethodOf (expr: Expression<_>) =
            let methExpr = expr.Body :?> MethodCallExpression
            methExpr.Method

        let PropertyInfoOf<'T> (expr: Expression<Func<'T, _>>) =
            let mem = getMember expr
            mem :?> PropertyInfo

        let FieldInfoOf<'T> (expr: Expression<Func<_>>) =
            let mem = getMember expr
            mem :?> FieldInfo
