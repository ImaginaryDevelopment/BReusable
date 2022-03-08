module BReusable.UoM


open System.Collections.ObjectModel

// http://fssnip.net/7SK
// allows using units of measure on other types
module IGUoM =
    open System
    type UoM = class end
        with
            static member inline Tag< ^W, ^t, ^tm when (^W or ^t) : (static member IsUoM : ^t * ^tm -> unit)> (t : ^t) = (# "" t : ^tm #)
            static member inline UnTag< ^W, ^t, ^tm when (^W or ^t) : (static member IsUoM : ^t * ^tm -> unit)> (t : ^tm) = (# "" t : ^t #)

    let inline tag (x : 't) : 'tm = UoM.Tag<UoM, 't, 'tm> x
    let inline untag (x : 'tm) : 't = UoM.UnTag<UoM, 't, 'tm> x

    [<MeasureAnnotatedAbbreviation>]
    type string<[<Measure>] 'Measure> = string

    type UoM with
        // Be *very* careful when writing this; bad args will result in invalid IL
        static member IsUoM(_ : string, _ : string<'Measure>) = ()
    [<Measure>] type FullName
    [<Measure>] type FirstName