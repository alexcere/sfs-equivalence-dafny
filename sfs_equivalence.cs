// Dafny program sfs_equivalence.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net5.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
[assembly: DafnyAssembly.DafnySourceAttribute(@"
// Dafny 3.1.0.30421
// Command Line Options: /compile:2 /spillTargetCode:1 sfs_equivalence.dfy
// sfs_equivalence.dfy

datatype BasicTerm = Value(val: int) | StackVar(id: int)

datatype StackElem = Op(input_stack: seq<BasicTerm>) | COp(elem1: BasicTerm, elem2: BasicTerm)

datatype ASFS = SFS(input: seq<BasicTerm>, dict: map<int, StackElem>, output: seq<BasicTerm>)

predicate isStackVar(el: BasicTerm)
  decreases el
{
  match el
  case Value(x) =>
    false
  case StackVar(x) =>
    true
}

function method getId(el: BasicTerm): int
  requires isStackVar(el)
  decreases el
{
  match el
  case StackVar(x) =>
    x
}

function method idsFromInput(input: seq<BasicTerm>): (sol: set<int>)
  ensures forall elem: int :: elem in sol ==> StackVar(elem) in input
  decreases input
{
  if input == [] then
    {}
  else
    match input[0] { case Value(_mcc#0) => (var val := _mcc#0; idsFromInput(input[1..])) case StackVar(_mcc#1) => var id := _mcc#1; {id} + idsFromInput(input[1..]) }
}

predicate allVarsAreStackVar(input: seq<BasicTerm>)
  decreases input
{
  if input == [] then
    true
  else
    match input[0] { case Value(_mcc#0) => (var val := _mcc#0; false) case StackVar(_mcc#1) => var id := _mcc#1; allVarsAreStackVar(input[1..]) }
}

predicate noRepeatedStackVar(input: seq<BasicTerm>, previously_ids: set<int>)
  decreases input
{
  if input == [] then
    true
  else
    match input[0] { case Value(_mcc#0) => (var val := _mcc#0; false) case StackVar(_mcc#1) => var id := _mcc#1; id !in previously_ids && noRepeatedStackVar(input[1..], previously_ids + {id}) }
}

function method atId(input: seq<BasicTerm>, pos: int): (id: int)
  requires 0 <= pos < |input|
  requires allVarsAreStackVar(input)
  ensures StackVar(id) in input
  ensures id in idsFromInput(input)
  decreases input, pos
{
  if pos == 0 then
    match input[0]
    case StackVar(x) =>
      x
  else
    atId(input, pos - 1)
}

function method getPos(input: seq<BasicTerm>, id: int): (pos: int)
  requires id in idsFromInput(input)
  requires allVarsAreStackVar(input)
  ensures 0 <= pos < |input|
  ensures match input[pos] { case Value(_mcc#0) => (var x := _mcc#0; false) case StackVar(_mcc#1) => var x := _mcc#1; x == id }
  decreases input, id
{
  match input[0]
  case StackVar(x) =>
    if x == id then
      0
    else
      1 + getPos(input[1..], id)
}

predicate initialInputIsWellDefined(input: seq<BasicTerm>)
  decreases input
{
  allVarsAreStackVar(input) &&
  noRepeatedStackVar(input, {})
}

predicate idsInDictAreWellDelimited(inputStack: seq<BasicTerm>, dict: map<int, StackElem>)
  decreases inputStack, dict
{
  forall key: int :: 
    key in dict ==>
      match dict[key] { case Op(_mcc#0) => (var l := _mcc#0; forall i :: 0 <= i < |l| ==> match l[i] { case Value(x) => true case StackVar(id2) => id2 in idsFromInput(inputStack) || id2 in dict }) case COp(_mcc#1, _mcc#2) => var x2 := _mcc#2; var x1 := _mcc#1; match x1 { case Value(x) => true case StackVar(id2) => id2 in idsFromInput(inputStack) || id2 in dict } && match x2 { case Value(x) => true case StackVar(id2) => id2 in idsFromInput(inputStack) || id2 in dict } }
}

predicate dictElementConverges(inputStack: seq<BasicTerm>, dict: map<int, StackElem>, key: int, previously_ids: set<int>)
  requires previously_ids <= dict.Keys
  requires key in dict
  requires idsInDictAreWellDelimited(inputStack, dict)
  decreases dict.Keys - previously_ids
{
  match dict[key]
  case Op(l) =>
    key !in previously_ids &&
    forall i :: 
      0 <= i < |l| ==>
        match l[i] { case Value(x) => true case StackVar(x1) => if x1 in idsFromInput(inputStack) then true else dictElementConverges(inputStack, dict, x1, previously_ids + {key}) }
  case COp(el1, el2) =>
    key !in previously_ids &&
    match el1 { case Value(x) => true case StackVar(x1) => (if x1 in idsFromInput(inputStack) then true else dictElementConverges(inputStack, dict, x1, previously_ids + {key})) } &&
    match el2 { case Value(x) => true case StackVar(x1) => if x1 in idsFromInput(inputStack) then true else dictElementConverges(inputStack, dict, x1, previously_ids + {key}) }
}

function method dependentIds(inputStack: seq<BasicTerm>, dict: map<int, StackElem>, key: int, previously_ids: set<int>): (sol: set<int>)
  requires previously_ids <= dict.Keys
  requires key in dict
  requires idsInDictAreWellDelimited(inputStack, dict)
  requires dictElementConverges(inputStack, dict, key, previously_ids)
  ensures previously_ids <= sol
  ensures sol <= dict.Keys
  decreases dict.Keys - previously_ids
{
  match dict[key]
  case Op(l) =>
    (set x, el | el in l && match el { case Value(x) => false case StackVar(x1) => (if x1 in idsFromInput(inputStack) then false else true) } && x in dependentIds(inputStack, dict, getId(el), previously_ids + {key}) :: x) + previously_ids + {key}
  case COp(el1, el2) =>
    (set x | match el1 { case Value(x) => false case StackVar(x1) => (if x1 in idsFromInput(inputStack) then false else true) } && x in dependentIds(inputStack, dict, getId(el1), previously_ids + {key}) :: x) + (set x | match el1 { case Value(x) => false case StackVar(x1) => (if x1 in idsFromInput(inputStack) then false else true) } && x in dependentIds(inputStack, dict, getId(el1), previously_ids + {key}) :: x) + previously_ids + {key}
}

predicate dictIsWellDefined(inputStack: seq<BasicTerm>, dict: map<int, StackElem>)
  decreases inputStack, dict
{
  dict.Keys * idsFromInput(inputStack) == {} &&
  idsInDictAreWellDelimited(inputStack, dict) &&
  (forall key: int :: 
    key in dict ==>
      dictElementConverges(inputStack, dict, key, {})) &&
  forall id: int :: 
    id in dict ==>
      match dict[id] { case Op(_mcc#0) => (var l := _mcc#0; Op(l) !in (dict - {id}).Values) case COp(_mcc#1, _mcc#2) => var x2 := _mcc#2; var x1 := _mcc#1; COp(x1, x2) !in (dict - {id}).Values && COp(x2, x1) !in (dict - {id}).Values }
}

predicate outputIsWellDefined(inputStack: seq<BasicTerm>, dict: map<int, StackElem>, output: seq<BasicTerm>)
  decreases inputStack, dict, output
{
  forall elem: BasicTerm :: 
    elem in output ==>
      match elem { case Value(_mcc#0) => (var x := _mcc#0; true) case StackVar(_mcc#1) => var id := _mcc#1; id in dict || id in idsFromInput(inputStack) }
}

predicate isSFS(sfs: ASFS)
  decreases sfs
{
  match sfs
  case SFS(input, dict, output) =>
    initialInputIsWellDefined(input) &&
    dictIsWellDefined(input, dict) &&
    outputIsWellDefined(input, dict, output) &&
    (set x, id | id in dict && x in dependentIds(input, dict, id, {}) :: x) == dict.Keys
}

predicate compareStackElem(input1: seq<BasicTerm>, input2: seq<BasicTerm>, dict1: map<int, StackElem>, dict2: map<int, StackElem>, key1: int, key2: int, prev_ids1: set<int>, prev_ids2: set<int>)
  requires initialInputIsWellDefined(input1)
  requires initialInputIsWellDefined(input2)
  requires idsInDictAreWellDelimited(input1, dict1)
  requires idsInDictAreWellDelimited(input2, dict2)
  requires prev_ids1 <= dict1.Keys
  requires prev_ids2 <= dict2.Keys
  requires key1 in dict1 && key2 in dict2
  requires dictElementConverges(input1, dict1, key1, prev_ids1)
  requires dictElementConverges(input2, dict2, key2, prev_ids2)
  requires dict1.Keys * idsFromInput(input1) == {}
  requires dict2.Keys * idsFromInput(input2) == {}
  decreases |dict1.Keys - prev_ids1|
{
  match (dict1[key1], dict2[key2])
  case (Op(l1), Op(l2)) =>
    |l1| == |l2| &&
    forall i :: 
      0 <= i < |l1| ==>
        match (l1[i], l2[i]) { case _#Make2(Value(x1),Value(x2)) => x1 == x2 case _#Make2(StackVar(x1),StackVar(x2)) => (if x1 in idsFromInput(input1) && x2 in idsFromInput(input2) then getPos(input1, x1) == getPos(input2, x2) else if x1 in dict1 && x2 in dict2 then compareStackElem(input1, input2, dict1, dict2, x1, x2, prev_ids1 + {key1}, prev_ids2 + {key2}) else false) case _#Make2(Value(x1),StackVar(x2)) => false case _#Make2(StackVar(x1),Value(x2)) => false }
  case (COp(el11, el12), COp(el21, el22)) =>
    (match (el11, el21) { case _#Make2(Value(x1),Value(x2)) => x1 == x2 case _#Make2(StackVar(x1),StackVar(x2)) => (if x1 in idsFromInput(input1) && x2 in idsFromInput(input2) then getPos(input1, x1) == getPos(input2, x2) else if x1 in dict1 && x2 in dict2 then compareStackElem(input1, input2, dict1, dict2, x1, x2, prev_ids1 + {key1}, prev_ids2 + {key2}) else false) case _#Make2(Value(x1),StackVar(x2)) => false case _#Make2(StackVar(x1),Value(x2)) => false } && match (el12, el22) { case _#Make2(Value(x1),Value(x2)) => x1 == x2 case _#Make2(StackVar(x1),StackVar(x2)) => (if x1 in idsFromInput(input1) && x2 in idsFromInput(input2) then getPos(input1, x1) == getPos(input2, x2) else if x1 in dict1 && x2 in dict2 then compareStackElem(input1, input2, dict1, dict2, x1, x2, prev_ids1 + {key1}, prev_ids2 + {key2}) else false) case _#Make2(Value(x1),StackVar(x2)) => false case _#Make2(StackVar(x1),Value(x2)) => false }) || (match (el11, el22) { case _#Make2(Value(x1),Value(x2)) => x1 == x2 case _#Make2(StackVar(x1),StackVar(x2)) => (if x1 in idsFromInput(input1) && x2 in idsFromInput(input2) then getPos(input1, x1) == getPos(input2, x2) else if x1 in dict1 && x2 in dict2 then compareStackElem(input1, input2, dict1, dict2, x1, x2, prev_ids1 + {key1}, prev_ids2 + {key2}) else false) case _#Make2(Value(x1),StackVar(x2)) => false case _#Make2(StackVar(x1),Value(x2)) => false } && match (el12, el21) { case _#Make2(Value(x1),Value(x2)) => x1 == x2 case _#Make2(StackVar(x1),StackVar(x2)) => (if x1 in idsFromInput(input1) && x2 in idsFromInput(input2) then getPos(input1, x1) == getPos(input2, x2) else if x1 in dict1 && x2 in dict2 then compareStackElem(input1, input2, dict1, dict2, x1, x2, prev_ids1 + {key1}, prev_ids2 + {key2}) else false) case _#Make2(Value(x1),StackVar(x2)) => false case _#Make2(StackVar(x1),Value(x2)) => false })
  case (COp(x1, y1), Op(l2)) =>
    false
  case (Op(l1), COp(x2, y2)) =>
    false
}

predicate areEquivalent(sfs1: ASFS, sfs2: ASFS)
  requires isSFS(sfs1)
  requires isSFS(sfs2)
  decreases sfs1, sfs2
{
  match (sfs1, sfs2)
  case (SFS(input1, dict1, output1), SFS(input2, dict2, output2)) =>
    |input1| == |input2| &&
    |output1| == |output2| &&
    forall i :: 
      0 <= i < |output1| ==>
        match (output1[i], output2[i]) { case _#Make2(Value(x1),Value(x2)) => x1 == x2 case _#Make2(StackVar(x1),StackVar(x2)) => (if x1 in idsFromInput(input1) && x2 in idsFromInput(input2) then getPos(input1, x1) == getPos(input2, x2) else if x1 in dict1 && x2 in dict2 then compareStackElem(input1, input2, dict1, dict2, x1, x2, {}, {}) else false) case _#Make2(StackVar(x1),Value(x2)) => false case _#Make2(Value(x1),StackVar(x2)) => false }
}

method compareDictElems(input1: seq<BasicTerm>, input2: seq<BasicTerm>, dict1: map<int, StackElem>, dict2: map<int, StackElem>, key1: int, key2: int, prev_ids1: set<int>, prev_ids2: set<int>)
    returns (b: bool)
  requires initialInputIsWellDefined(input1)
  requires initialInputIsWellDefined(input2)
  requires idsInDictAreWellDelimited(input1, dict1)
  requires idsInDictAreWellDelimited(input2, dict2)
  requires prev_ids1 <= dict1.Keys
  requires prev_ids2 <= dict2.Keys
  requires key1 in dict1 && key2 in dict2
  requires dictElementConverges(input1, dict1, key1, prev_ids1)
  requires dictElementConverges(input2, dict2, key2, prev_ids2)
  requires dict1.Keys * idsFromInput(input1) == {}
  requires dict2.Keys * idsFromInput(input2) == {}
  ensures b == compareStackElem(input1, input2, dict1, dict2, key1, key2, prev_ids1, prev_ids2)
  decreases |dict1.Keys - prev_ids1|
{
  match (dict1[key1], dict2[key2])
  case (Op(l1), Op(l2)) =>
    if |l1| != |l2| {
      return false;
    } else {
      var i := 0;
      while i < |l1|
        invariant 0 <= i <= |l1|
        invariant forall j :: 0 <= j < i ==> match (l1[j], l2[j]) { case _#Make2(Value(x1),Value(x2)) => x1 == x2 case _#Make2(StackVar(x1),StackVar(x2)) => (if x1 in idsFromInput(input1) && x2 in idsFromInput(input2) then getPos(input1, x1) == getPos(input2, x2) else if x1 in dict1 && x2 in dict2 then compareStackElem(input1, input2, dict1, dict2, x1, x2, prev_ids1 + {key1}, prev_ids2 + {key2}) else false) case _#Make2(Value(x1),StackVar(x2)) => false case _#Make2(StackVar(x1),Value(x2)) => false }
        decreases |l1| - i
      {
        match (l1[i], l2[i]) {
          case (Value(x1), Value(x2)) =>
            if x1 != x2 {
              return false;
            }
          case (StackVar(x1), StackVar(x2)) =>
            if x1 in idsFromInput(input1) && x2 in idsFromInput(input2) {
              if getPos(input1, x1) != getPos(input2, x2) {
                return false;
              }
            } else if x1 in dict1 && x2 in dict2 {
              var aux := compareDictElems(input1, input2, dict1, dict2, x1, x2, prev_ids1 + {key1}, prev_ids2 + {key2});
              if !aux {
                return false;
              }
            } else {
              return false;
            }
          case (Value(x1), StackVar(x2)) =>
            return false;
          case (StackVar(x1), Value(x2)) =>
            return false;
        }
        i := i + 1;
      }
      return true;
    }
  case (COp(el11, el12), COp(el21, el22)) =>
    var b1 := true;
    match (el11, el21) {
      case (Value(x1), Value(x2)) =>
        b1 := x1 == x2;
      case (StackVar(x1), StackVar(x2)) =>
        if x1 in idsFromInput(input1) && x2 in idsFromInput(input2) {
          b1 := getPos(input1, x1) == getPos(input2, x2);
        } else if x1 in dict1 && x2 in dict2 {
          b1 := compareDictElems(input1, input2, dict1, dict2, x1, x2, prev_ids1 + {key1}, prev_ids2 + {key2});
        } else {
          b1 := false;
        }
      case (Value(x1), StackVar(x2)) =>
        {
          b1 := false;
        }
      case (StackVar(x1), Value(x2)) =>
        {
          b1 := false;
        }
    }
    if b1 {
      match (el12, el22) {
        case (Value(x1), Value(x2)) =>
          b1 := x1 == x2;
        case (StackVar(x1), StackVar(x2)) =>
          if x1 in idsFromInput(input1) && x2 in idsFromInput(input2) {
            b1 := getPos(input1, x1) == getPos(input2, x2);
          } else if x1 in dict1 && x2 in dict2 {
            b1 := compareDictElems(input1, input2, dict1, dict2, x1, x2, prev_ids1 + {key1}, prev_ids2 + {key2});
          } else {
            b1 := false;
          }
        case (Value(x1), StackVar(x2)) =>
          {
            b1 := false;
          }
        case (StackVar(x1), Value(x2)) =>
          {
            b1 := false;
          }
      }
      if b1 {
        return true;
      }
    }
    b1 := true;
    match (el12, el21) {
      case (Value(x1), Value(x2)) =>
        b1 := x1 == x2;
      case (StackVar(x1), StackVar(x2)) =>
        if x1 in idsFromInput(input1) && x2 in idsFromInput(input2) {
          b1 := getPos(input1, x1) == getPos(input2, x2);
        } else if x1 in dict1 && x2 in dict2 {
          b1 := compareDictElems(input1, input2, dict1, dict2, x1, x2, prev_ids1 + {key1}, prev_ids2 + {key2});
        } else {
          b1 := false;
        }
      case (Value(x1), StackVar(x2)) =>
        {
          b1 := false;
        }
      case (StackVar(x1), Value(x2)) =>
        {
          b1 := false;
        }
    }
    if b1 {
      match (el11, el22) {
        case (Value(x1), Value(x2)) =>
          b1 := x1 == x2;
        case (StackVar(x1), StackVar(x2)) =>
          if x1 in idsFromInput(input1) && x2 in idsFromInput(input2) {
            b1 := getPos(input1, x1) == getPos(input2, x2);
          } else if x1 in dict1 && x2 in dict2 {
            b1 := compareDictElems(input1, input2, dict1, dict2, x1, x2, prev_ids1 + {key1}, prev_ids2 + {key2});
          } else {
            b1 := false;
          }
        case (Value(x1), StackVar(x2)) =>
          {
            b1 := false;
          }
        case (StackVar(x1), Value(x2)) =>
          {
            b1 := false;
          }
      }
      return b1;
    } else {
      return false;
    }
  case (COp(x1, y1), Op(l2)) =>
    return false;
  case (Op(l1), COp(x2, y2)) =>
    return false;
}

method areEquivalentSFS(sfs1: ASFS, sfs2: ASFS) returns (b: bool)
  requires isSFS(sfs1)
  requires isSFS(sfs2)
  ensures b == areEquivalent(sfs1, sfs2)
  decreases sfs1, sfs2
{
  match (sfs1, sfs2)
  case (SFS(input1, dict1, output1), SFS(input2, dict2, output2)) =>
    if |input1| != |input2| || |output1| != |output2| {
      return false;
    } else {
      var i := 0;
      while i < |output1|
        invariant 0 <= i <= |output1|
        invariant forall j :: 0 <= j < i ==> match (output1[j], output2[j]) { case _#Make2(Value(x1),Value(x2)) => x1 == x2 case _#Make2(StackVar(x1),StackVar(x2)) => (if x1 in idsFromInput(input1) && x2 in idsFromInput(input2) then getPos(input1, x1) == getPos(input2, x2) else if x1 in dict1 && x2 in dict2 then compareStackElem(input1, input2, dict1, dict2, x1, x2, {}, {}) else false) case _#Make2(StackVar(x1),Value(x2)) => false case _#Make2(Value(x1),StackVar(x2)) => false }
        decreases |output1| - i
      {
        match (output1[i], output2[i]) {
          case (Value(x1), Value(x2)) =>
            if x1 != x2 {
              return false;
            }
          case (StackVar(x1), StackVar(x2)) =>
            if x1 in idsFromInput(input1) && x2 in idsFromInput(input2) {
              if getPos(input1, x1) != getPos(input2, x2) {
                return false;
              }
            } else if x1 in dict1 && x2 in dict2 {
              var aux := compareDictElems(input1, input2, dict1, dict2, x1, x2, {}, {});
              if !aux {
                return false;
              }
            } else {
              return false;
            }
          case (StackVar(x1), Value(x2)) =>
            return false;
          case (Value(x1), StackVar(x2)) =>
            return false;
        }
        i := i + 1;
      }
      return true;
    }
}
")]

// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#if ISDAFNYRUNTIMELIB
using System; // for Func
using System.Numerics;
#endif

namespace DafnyAssembly {
  [AttributeUsage(AttributeTargets.Assembly)]
  public class DafnySourceAttribute : Attribute {
    public readonly string dafnySourceText;
    public DafnySourceAttribute(string txt) { dafnySourceText = txt; }
  }
}

namespace Dafny
{
  using System.Collections.Generic;
  using System.Collections.Immutable;
  using System.Linq;

  public interface ISet<out T>
  {
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<ISet<T>> AllSubsets { get; }
    bool Contains<G>(G t);
    bool EqualsAux(ISet<object> other);
    ISet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class Set<T> : ISet<T>
  {
    readonly ImmutableHashSet<T> setImpl;
    readonly bool containsNull;
    Set(ImmutableHashSet<T> d, bool containsNull) {
      this.setImpl = d;
      this.containsNull = containsNull;
    }
    public static readonly ISet<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty, false);

    private static readonly TypeDescriptor<ISet<T>> _TYPE = new Dafny.TypeDescriptor<ISet<T>>(Empty);
    public static TypeDescriptor<ISet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISet<T> FromElements(params T[] values) {
      return FromCollection(values);
    }

    public static Set<T> FromISet(ISet<T> s) {
      return s as Set<T> ?? FromCollection(s.Elements);
    }
    public static Set<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }
      return new Set<T>(d.ToImmutable(), containsNull);
    }
    public static ISet<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      if (oneMoreValue == null) {
        containsNull = true;
      } else {
        d.Add(oneMoreValue);
      }
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }
      return new Set<T>(d.ToImmutable(), containsNull);
    }
    public ISet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISet<U> th) {
        return th;
      } else {
        var d = ImmutableHashSet<U>.Empty.ToBuilder();
        foreach (var t in this.setImpl) {
          var u = converter(t);
          d.Add(u);
        }
        return new Set<U>(d.ToImmutable(), this.containsNull);
      }
    }
    public int Count {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }
    public long LongCount {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }
    public IEnumerable<T> Elements {
      get {
        if (containsNull) {
          yield return default(T);
        }
        foreach (var t in this.setImpl) {
          yield return t;
        }
      }
    }

    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".
    /// </summary>
    public IEnumerable<ISet<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list, but don't include null
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
        while (true) {
          // yield both the subset without null and, if null is in the original set, the subset with null included
          var ihs = s.ToImmutable();
          yield return new Set<T>(ihs, false);
          if (containsNull) {
            yield return new Set<T>(ihs, true);
          }
          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }
          if (i == n) {
            // we have cycled through all the subsets
            break;
          }
          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }
    public bool Equals(ISet<T> other) {
      if (other == null || Count != other.Count) {
        return false;
      } else if (this == other) {
        return true;
      }
      foreach (var elmt in Elements) {
        if (!other.Contains(elmt)) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      if (other is ISet<T>) {
        return Equals((ISet<T>)other);
      }
      var th = this as ISet<object>;
      var oth = other as ISet<object>;
      if (th != null && oth != null) {
        // We'd like to obtain the more specific type parameter U for oth's type ISet<U>.
        // We do that by making a dynamically dispatched call, like:
        //     oth.Equals(this)
        // The hope is then that its comparison "this is ISet<U>" (that is, the first "if" test
        // above, but in the call "oth.Equals(this)") will be true and the non-virtual Equals
        // can be called. However, such a recursive call to "oth.Equals(this)" could turn
        // into infinite recursion. Therefore, we instead call "oth.EqualsAux(this)", which
        // performs the desired type test, but doesn't recurse any further.
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(ISet<object> other) {
      var s = other as ISet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (containsNull) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(default(T)) + 3);
      }
      foreach (var t in this.setImpl) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(t) + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "{";
      var sep = "";
      if (containsNull) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
      foreach (var t in this.setImpl) {
        s += sep + Dafny.Helpers.ToString(t);
        sep = ", ";
      }
      return s + "}";
    }
    public static bool IsProperSubsetOf(ISet<T> th, ISet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(ISet<T> th, ISet<T> other) {
      if (other.Count < th.Count) {
        return false;
      }
      foreach (T t in th.Elements) {
        if (!other.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(ISet<T> th, ISet<T> other) {
      ISet<T> a, b;
      if (th.Count < other.Count) {
        a = th; b = other;
      } else {
        a = other; b = th;
      }
      foreach (T t in a.Elements) {
        if (b.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public bool Contains<G>(G t) {
      return t == null ? containsNull : t is T && this.setImpl.Contains((T)(object)t);
    }
    public static ISet<T> Union(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Union(b.setImpl), a.containsNull || b.containsNull);
    }
    public static ISet<T> Intersect(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Intersect(b.setImpl), a.containsNull && b.containsNull);
    }
    public static ISet<T> Difference(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Except(b.setImpl), a.containsNull && !b.containsNull);
    }
  }

  public interface IMultiSet<out T>
  {
    bool IsEmpty { get; }
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    bool Contains<G>(G t);
    BigInteger Select<G>(G t);
    IMultiSet<T> Update<G>(G t, BigInteger i);
    bool EqualsAux(IMultiSet<object> other);
    IMultiSet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class MultiSet<T> : IMultiSet<T>
  {
    readonly ImmutableDictionary<T, BigInteger> dict;
    readonly BigInteger occurrencesOfNull;  // stupidly, a Dictionary in .NET cannot use "null" as a key
    MultiSet(ImmutableDictionary<T, BigInteger>.Builder d, BigInteger occurrencesOfNull) {
      dict = d.ToImmutable();
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, BigInteger>.Empty.ToBuilder(), BigInteger.Zero);

    private static readonly TypeDescriptor<IMultiSet<T>> _TYPE = new Dafny.TypeDescriptor<IMultiSet<T>>(Empty);
    public static TypeDescriptor<IMultiSet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static MultiSet<T> FromIMultiSet(IMultiSet<T> s) {
      return s as MultiSet<T> ?? FromCollection(s.Elements);
    }
    public static MultiSet<T> FromElements(params T[] values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t, out i)) {
            i = BigInteger.Zero;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }
    public static MultiSet<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t, out i)) {
            i = BigInteger.Zero;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }
    public static MultiSet<T> FromSeq(ISequence<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values.Elements) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t, out i)) {
            i = BigInteger.Zero;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }
    public static MultiSet<T> FromSet(ISet<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values.Elements) {
        if (t == null) {
          containsNull = true;
        } else {
          d[t] = BigInteger.One;
        }
      }
      return new MultiSet<T>(d, containsNull ? BigInteger.One : BigInteger.Zero);
    }
    public IMultiSet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is IMultiSet<U> th) {
        return th;
      } else {
        var d = ImmutableDictionary<U, BigInteger>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = converter(item.Key);
          d.Add(k, item.Value);
        }
        return new MultiSet<U>(d, this.occurrencesOfNull);
      }
    }

    public bool Equals(IMultiSet<T> other) {
      return IsSubsetOf(this, other) && IsSubsetOf(other, this);
    }
    public override bool Equals(object other) {
      if (other is IMultiSet<T>) {
        return Equals((IMultiSet<T>)other);
      }
      var th = this as IMultiSet<object>;
      var oth = other as IMultiSet<object>;
      if (th != null && oth != null) {
        // See comment in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(IMultiSet<object> other) {
      var s = other as IMultiSet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (occurrencesOfNull > 0) {
        var key = Dafny.Helpers.GetHashCode(default(T));
        key = (key << 3) | (key >> 29) ^ occurrencesOfNull.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
      foreach (var kv in dict) {
        var t = Dafny.Helpers.ToString(kv.Key);
        for (var i = BigInteger.Zero; i < kv.Value; i++) {
          s += sep + t;
          sep = ", ";
        }
      }
      return s + "}";
    }
    public static bool IsProperSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      if (b.occurrencesOfNull < a.occurrencesOfNull) {
        return false;
      }
      foreach (T t in a.dict.Keys) {
        if (!b.dict.ContainsKey(t) || b.dict[t] < a.dict[t]) {
          return false;
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(IMultiSet<T> th, IMultiSet<T> other) {
      foreach (T t in th.UniqueElements) {
        if (other.Contains(t)) {
          return false;
        }
      }
      return true;
    }

    public bool Contains<G>(G t) {
      return t == null ? occurrencesOfNull > 0 : t is T && dict.ContainsKey((T)(object)t);
    }
    public BigInteger Select<G>(G t) {
      if (t == null) {
        return occurrencesOfNull;
      }
      BigInteger m;
      if (t is T && dict.TryGetValue((T)(object)t, out m)) {
        return m;
      } else {
        return BigInteger.Zero;
      }
    }
    public IMultiSet<T> Update<G>(G t, BigInteger i) {
      if (Select(t) == i) {
        return this;
      } else if (t == null) {
        var r = dict.ToBuilder();
        return new MultiSet<T>(r, i);
      } else {
        var r = dict.ToBuilder();
        r[(T)(object)t] = i;
        return new MultiSet<T>(r, occurrencesOfNull);
      }
    }
    public static IMultiSet<T> Union(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return other;
      } else if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        BigInteger i;
        if (!r.TryGetValue(t, out i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + a.dict[t];
      }
      foreach (T t in b.dict.Keys) {
        BigInteger i;
        if (!r.TryGetValue(t, out i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + b.dict[t];
      }
      return new MultiSet<T>(r, a.occurrencesOfNull + b.occurrencesOfNull);
    }
    public static IMultiSet<T> Intersect(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return th;
      } else if (other.IsEmpty) {
        return other;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t] < b.dict[t] ? a.dict[t] : b.dict[t]);
        }
      }
      return new MultiSet<T>(r, a.occurrencesOfNull < b.occurrencesOfNull ? a.occurrencesOfNull : b.occurrencesOfNull);
    }
    public static IMultiSet<T> Difference(IMultiSet<T> th, IMultiSet<T> other) { // \result == this - other
      if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t]);
        } else if (b.dict[t] < a.dict[t]) {
          r.Add(t, a.dict[t] - b.dict[t]);
        }
      }
      return new MultiSet<T>(r, b.occurrencesOfNull < a.occurrencesOfNull ? a.occurrencesOfNull - b.occurrencesOfNull : BigInteger.Zero);
    }

    public bool IsEmpty { get { return occurrencesOfNull == 0 && dict.IsEmpty; } }

    public int Count {
      get { return (int)ElementCount(); }
    }
    public long LongCount {
      get { return (long)ElementCount(); }
    }
    private BigInteger ElementCount() {
      // This is inefficient
      var c = occurrencesOfNull;
      foreach (var item in dict) {
        c += item.Value;
      }
      return c;
    }

    public IEnumerable<T> Elements {
      get {
        for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
          yield return default(T);
        }
        foreach (var item in dict) {
          for (var i = BigInteger.Zero; i < item.Value; i++) {
            yield return item.Key;
          }
        }
      }
    }

    public IEnumerable<T> UniqueElements {
      get {
        if (!occurrencesOfNull.IsZero) {
          yield return default(T);
        }
        foreach (var key in dict.Keys) {
          yield return key;
        }
      }
    }
  }

  public interface IMap<out U, out V>
  {
    int Count { get; }
    long LongCount { get; }
    ISet<U> Keys { get; }
    ISet<V> Values { get; }
    IEnumerable<IPair<U, V>> ItemEnumerable { get; }
    bool Contains<G>(G t);
    /// <summary>
    /// Returns "true" iff "this is IMap<object, object>" and "this" equals "other".
    /// </summary>
    bool EqualsObjObj(IMap<object, object> other);
    IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter);
  }

  public class Map<U, V> : IMap<U, V>
  {
    readonly ImmutableDictionary<U, V> dict;
    readonly bool hasNullKey;  // true when "null" is a key of the Map
    readonly V nullValue;  // if "hasNullKey", the value that "null" maps to

    private Map(ImmutableDictionary<U, V>.Builder d, bool hasNullKey, V nullValue) {
      dict = d.ToImmutable();
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty.ToBuilder(), false, default(V));

    private Map(ImmutableDictionary<U, V> d, bool hasNullKey, V nullValue) {
      dict = d;
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }

    private static readonly TypeDescriptor<IMap<U, V>> _TYPE = new Dafny.TypeDescriptor<IMap<U, V>>(Empty);
    public static TypeDescriptor<IMap<U, V>> _TypeDescriptor() {
      return _TYPE;
    }

    public static Map<U, V> FromElements(params IPair<U, V>[] values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromCollection(IEnumerable<IPair<U, V>> values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromIMap(IMap<U, V> m) {
      return m as Map<U, V> ?? FromCollection(m.ItemEnumerable);
    }
    public IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter) {
      if (this is IMap<UU, VV> th) {
        return th;
      } else {
        var d = ImmutableDictionary<UU, VV>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = keyConverter(item.Key);
          var v = valueConverter(item.Value);
          d.Add(k, v);
        }
        return new Map<UU, VV>(d, this.hasNullKey, (VV)(object)this.nullValue);
      }
    }
    public int Count {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }
    public long LongCount {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }

    public bool Equals(IMap<U, V> other) {
      if (other == null || LongCount != other.LongCount) {
        return false;
      } else if (this == other) {
        return true;
      }
      if (hasNullKey) {
        if (!other.Contains(default(U)) || !object.Equals(nullValue, Select(other, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Select(other, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public bool EqualsObjObj(IMap<object, object> other) {
      if (!(this is IMap<object, object>) || other == null || LongCount != other.LongCount) {
        return false;
      } else if (this == other) {
        return true;
      }
      var oth = Map<object, object>.FromIMap(other);
      if (hasNullKey) {
        if (!oth.Contains(default(U)) || !object.Equals(nullValue, Map<object, object>.Select(oth, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Map<object, object>.Select(oth, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      // See comment in Set.Equals
      var m = other as IMap<U, V>;
      if (m != null) {
        return Equals(m);
      }
      var imapoo = other as IMap<object, object>;
      if (imapoo != null) {
        return EqualsObjObj(imapoo);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (hasNullKey) {
        var key = Dafny.Helpers.GetHashCode(default(U));
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(nullValue);
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(kv.Value);
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      if (hasNullKey) {
        s += sep + Dafny.Helpers.ToString(default(U)) + " := " + Dafny.Helpers.ToString(nullValue);
        sep = ", ";
      }
      foreach (var kv in dict) {
        s += sep + Dafny.Helpers.ToString(kv.Key) + " := " + Dafny.Helpers.ToString(kv.Value);
        sep = ", ";
      }
      return s + "]";
    }
    public bool Contains<G>(G u) {
      return u == null ? hasNullKey : u is U && dict.ContainsKey((U)(object)u);
    }
    public static V Select(IMap<U, V> th, U index) {
      // the following will throw an exception if "index" in not a key of the map
      var m = FromIMap(th);
      return index == null && m.hasNullKey ? m.nullValue : m.dict[index];
    }
    public static IMap<U, V> Update(IMap<U, V> th, U index, V val) {
      var m = FromIMap(th);
      var d = m.dict.ToBuilder();
      if (index == null) {
        return new Map<U, V>(d, true, val);
      } else {
        d[index] = val;
        return new Map<U, V>(d, m.hasNullKey, m.nullValue);
      }
    }

    public static IMap<U, V> Merge(IMap<U, V> th, IMap<U, V> other) {
      var a = FromIMap(th);
      var b = FromIMap(other);
      ImmutableDictionary<U, V> d = a.dict.SetItems(b.dict);
      return new Map<U, V>(d, a.hasNullKey || b.hasNullKey, b.hasNullKey ? b.nullValue : a.nullValue);
    }

    public static IMap<U, V> Subtract(IMap<U, V> th, ISet<U> keys) {
      var a = FromIMap(th);
      ImmutableDictionary<U, V> d = a.dict.RemoveRange(keys.Elements);
      return new Map<U, V>(d, a.hasNullKey && !keys.Contains<object>(null), a.nullValue);
    }

    public ISet<U> Keys {
      get {
        if (hasNullKey) {
          return Dafny.Set<U>.FromCollectionPlusOne(dict.Keys, default(U));
        } else {
          return Dafny.Set<U>.FromCollection(dict.Keys);
        }
      }
    }
    public ISet<V> Values {
      get {
        if (hasNullKey) {
          return Dafny.Set<V>.FromCollectionPlusOne(dict.Values, nullValue);
        } else {
          return Dafny.Set<V>.FromCollection(dict.Values);
        }
      }
    }

    public IEnumerable<IPair<U, V>> ItemEnumerable {
      get {
        if (hasNullKey) {
          yield return new Pair<U, V>(default(U), nullValue);
        }
        foreach (KeyValuePair<U, V> kvp in dict) {
          yield return new Pair<U, V>(kvp.Key, kvp.Value);
        }
      }
    }

    public static ISet<_System.Tuple2<U, V>> Items(IMap<U, V> m) {
      var result = new HashSet<_System.Tuple2<U, V>>();
      foreach (var item in m.ItemEnumerable) {
        result.Add(_System.Tuple2<U, V>.create(item.Car, item.Cdr));
      }
      return Dafny.Set<_System.Tuple2<U, V>>.FromCollection(result);
    }
  }

  public interface ISequence<out T> {
    long LongCount { get; }
    int Count { get; }
    T[] Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    T Select(ulong index);
    T Select(long index);
    T Select(uint index);
    T Select(int index);
    T Select(BigInteger index);
    bool Contains<G>(G g);
    ISequence<T> Take(long m);
    ISequence<T> Take(ulong n);
    ISequence<T> Take(BigInteger n);
    ISequence<T> Drop(long m);
    ISequence<T> Drop(ulong n);
    ISequence<T> Drop(BigInteger n);
    ISequence<T> Subsequence(long lo, long hi);
    ISequence<T> Subsequence(long lo, ulong hi);
    ISequence<T> Subsequence(long lo, BigInteger hi);
    ISequence<T> Subsequence(ulong lo, long hi);
    ISequence<T> Subsequence(ulong lo, ulong hi);
    ISequence<T> Subsequence(ulong lo, BigInteger hi);
    ISequence<T> Subsequence(BigInteger lo, long hi);
    ISequence<T> Subsequence(BigInteger lo, ulong hi);
    ISequence<T> Subsequence(BigInteger lo, BigInteger hi);
    bool EqualsAux(ISequence<object> other);
    ISequence<U> DowncastClone<U>(Func<T, U> converter);
  }

  public abstract class Sequence<T> : ISequence<T>
  {
    public static readonly ISequence<T> Empty = new ArraySequence<T>(new T[0]);

    private static readonly TypeDescriptor<ISequence<T>> _TYPE = new Dafny.TypeDescriptor<ISequence<T>>(Empty);
    public static TypeDescriptor<ISequence<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISequence<T> Create(BigInteger length, System.Func<BigInteger, T> init) {
      var len = (int)length;
      var values = new T[len];
      for (int i = 0; i < len; i++) {
        values[i] = init(new BigInteger(i));
      }
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromArray(T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromElements(params T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<char> FromString(string s) {
      return new ArraySequence<char>(s.ToCharArray());
    }
    public ISequence<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISequence<U> th) {
        return th;
      } else {
        var values = new U[this.LongCount];
        for (long i = 0; i < this.LongCount; i++) {
          var val = converter(this.Select(i));
          values[i] = val;
        }
        return new ArraySequence<U>(values);
      }
    }
    public static ISequence<T> Update(ISequence<T> sequence, long index, T t) {
      T[] tmp = (T[])sequence.Elements.Clone();
      tmp[index] = t;
      return new ArraySequence<T>(tmp);
    }
    public static ISequence<T> Update(ISequence<T> sequence, ulong index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static ISequence<T> Update(ISequence<T> sequence, BigInteger index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static bool EqualUntil(ISequence<T> left, ISequence<T> right, int n) {
      T[] leftElmts = left.Elements, rightElmts = right.Elements;
      for (int i = 0; i < n; i++) {
        if (!object.Equals(leftElmts[i], rightElmts[i]))
          return false;
      }
      return true;
    }
    public static bool IsPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Elements.Length;
      return n <= right.Elements.Length && EqualUntil(left, right, n);
    }
    public static bool IsProperPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Elements.Length;
      return n < right.Elements.Length && EqualUntil(left, right, n);
    }
    public static ISequence<T> Concat(ISequence<T> left, ISequence<T> right) {
      if (left.Count == 0) {
        return right;
      }
      if (right.Count == 0) {
        return left;
      }
      return new ConcatSequence<T>(left, right);
    }
    // Make Count a public abstract instead of LongCount, since the "array size is limited to a total of 4 billion
    // elements, and to a maximum index of 0X7FEFFFFF". Therefore, as a protection, limit this to int32.
    // https://docs.microsoft.com/en-us/dotnet/api/system.array
    public abstract int Count  { get; }
    public long LongCount {
      get { return Count; }
    }
    // ImmutableElements cannot be public in the interface since ImmutableArray<T> leads to a
    // "covariant type T occurs in invariant position" error. There do not appear to be interfaces for ImmutableArray<T>
    // that resolve this.
    protected abstract ImmutableArray<T> ImmutableElements { get; }

    public T[] Elements
    {
      get { return ImmutableElements.ToArray(); }
    }
    public IEnumerable<T> UniqueElements {
      get {
        var st = Set<T>.FromCollection(ImmutableElements);
        return st.Elements;
      }
    }

    public T Select(ulong index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(long index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(uint index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(int index) {
      return ImmutableElements[index];
    }
    public T Select(BigInteger index) {
      return ImmutableElements[(int)index];
    }
    public bool Equals(ISequence<T> other) {
      int n = ImmutableElements.Length;
      return n == other.Elements.Length && EqualUntil(this, other, n);
    }
    public override bool Equals(object other) {
      if (other is ISequence<T>) {
        return Equals((ISequence<T>)other);
      }
      var th = this as ISequence<object>;
      var oth = other as ISequence<object>;
      if (th != null && oth != null) {
        // see explanation in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }
    public bool EqualsAux(ISequence<object> other) {
      var s = other as ISequence<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }
    public override int GetHashCode() {
      ImmutableArray<T> elmts = ImmutableElements;
      // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
      if (elmts.IsDefaultOrEmpty)
        return 0;
      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ Dafny.Helpers.GetHashCode(elmts[i]);
      }
      return hashCode;
    }
    public override string ToString() {
      // This is required because (ImmutableElements is ImmutableArray<char>) is not a valid type check
      var typeCheckTmp = new T[0];
      ImmutableArray<T> elmts = ImmutableElements;
      if (typeCheckTmp is char[]) {
        var s = "";
        foreach (var t in elmts) {
          s += t.ToString();
        }
        return s;
      } else {
        var s = "[";
        var sep = "";
        foreach (var t in elmts) {
          s += sep + Dafny.Helpers.ToString(t);
          sep = ", ";
        }
        return s + "]";
      }
    }
    public bool Contains<G>(G g) {
      if (g == null || g is T) {
        var t = (T)(object)g;
        return ImmutableElements.Contains(t);
      }
      return false;
    }
    public ISequence<T> Take(long m) {
      if (ImmutableElements.Length == m)
        return this;
      int length = checked((int)m);
      T[] tmp = new T[length];
      ImmutableElements.CopyTo(0, tmp, 0, length);
      return new ArraySequence<T>(tmp);
    }
    public ISequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public ISequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public ISequence<T> Drop(long m)
    {
      int startingElement = checked((int)m);
      if (startingElement == 0)
        return this;
      int length = ImmutableElements.Length - startingElement;
      T[] tmp = new T[length];
      ImmutableElements.CopyTo(startingElement, tmp, 0, length);
      return new ArraySequence<T>(tmp);
    }
    public ISequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public ISequence<T> Drop(BigInteger n) {
      if (n.IsZero)
        return this;
      return Drop((long)n);
    }
    public ISequence<T> Subsequence(long lo, long hi) {
      if (lo == 0 && hi == ImmutableElements.Length) {
        return this;
      }
      int startingIndex = checked((int) lo);
      int endingIndex = checked((int)hi);
      var length = endingIndex - startingIndex;
      T[] tmp = new T[length];
      ImmutableElements.CopyTo(startingIndex, tmp, 0, length);
      return new ArraySequence<T>(tmp);
    }
    public ISequence<T> Subsequence(long lo, ulong hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(long lo, BigInteger hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(ulong lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
  }
  internal class ArraySequence<T> : Sequence<T> {
    private readonly ImmutableArray<T> elmts;

    internal ArraySequence(ImmutableArray<T> ee) {
      elmts = ee;
    }
    internal ArraySequence(T[] ee) {
      elmts = ImmutableArray.Create<T>(ee);
    }

    protected override ImmutableArray<T> ImmutableElements {
      get
      {
        return elmts;
      }
    }
    public override int Count {
      get {
        return elmts.Length;
      }
    }
  }
  internal class ConcatSequence<T> : Sequence<T> {
    // INVARIANT: Either left != null, right != null, and elmts's underlying array == null or
    // left == null, right == null, and elmts's underlying array != null
    private ISequence<T> left, right;
    private ImmutableArray<T> elmts;
    private readonly int count;

    internal ConcatSequence(ISequence<T> left, ISequence<T> right) {
      this.left = left;
      this.right = right;
      this.count = left.Count + right.Count;
    }

    protected override ImmutableArray<T> ImmutableElements {
      get {
        // IsDefault returns true if the underlying array is a null reference
        // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
        if (elmts.IsDefault) {
          elmts = ComputeElements();
          // We don't need the original sequences anymore; let them be
          // garbage-collected
          left = null;
          right = null;
        }
        return elmts;
      }
    }

    public override int Count {
      get {
        return count;
      }
    }

    private ImmutableArray<T> ComputeElements() {
      // Traverse the tree formed by all descendants which are ConcatSequences
      var ansBuilder = ImmutableArray.CreateBuilder<T>();
      var toVisit = new Stack<ISequence<T>>();
      toVisit.Push(right);
      toVisit.Push(left);

      while (toVisit.Count != 0) {
        var seq = toVisit.Pop();
        var cs = seq as ConcatSequence<T>;
        if (cs != null && cs.elmts.IsDefault) {
          toVisit.Push(cs.right);
          toVisit.Push(cs.left);
        } else {
          var array = seq.Elements;
          ansBuilder.AddRange(array);
        }
      }
      return ansBuilder.ToImmutable();
    }
  }

  public interface IPair<out A, out B>
  {
    A Car { get; }
    B Cdr { get; }
  }
  public class Pair<A, B> : IPair<A, B>
  {
    private A car;
    private B cdr;
    public A Car { get { return car; } }
    public B Cdr { get { return cdr; } }
    public Pair(A a, B b) {
      this.car = a;
      this.cdr = b;
    }
  }

  public class TypeDescriptor<T>
  {
    private readonly T initValue;
    public TypeDescriptor(T initValue) {
      this.initValue = initValue;
    }
    public T Default() {
      return initValue;
    }
  }

  public partial class Helpers
  {
    public static int GetHashCode<G>(G g) {
      return g == null ? 1001 : g.GetHashCode();
    }

    public static int ToIntChecked(BigInteger i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) msg = "value out of range for a 32-bit int";
        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(long i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) msg = "value out of range for a 32-bit int";
        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(int i, string msg) {
      return i;
    }

    public static string ToString<G>(G g) {
      if (g == null) {
        return "null";
      } else if (g is bool) {
        return (bool)(object)g ? "true" : "false";  // capitalize boolean literals like in Dafny
      } else {
        return g.ToString();
      }
    }
    public static void Print<G>(G g) {
      System.Console.Write(ToString(g));
    }

    public static readonly TypeDescriptor<bool> BOOL = new TypeDescriptor<bool>(false);
    public static readonly TypeDescriptor<char> CHAR = new TypeDescriptor<char>('D');  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<BigInteger> INT = new TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static readonly TypeDescriptor<BigRational> REAL = new TypeDescriptor<BigRational>(BigRational.ZERO);
    public static readonly TypeDescriptor<byte> UINT8 = new TypeDescriptor<byte>(0);
    public static readonly TypeDescriptor<ushort> UINT16 = new TypeDescriptor<ushort>(0);
    public static readonly TypeDescriptor<uint> UINT32 = new TypeDescriptor<uint>(0);
    public static readonly TypeDescriptor<ulong> UINT64 = new TypeDescriptor<ulong>(0);

    public static TypeDescriptor<T> NULL<T>() where T : class {
      return new TypeDescriptor<T>(null);
    }

    public static TypeDescriptor<A[]> ARRAY<A>() {
      return new TypeDescriptor<A[]>(new A[0]);
    }

    public static bool Quantifier<T>(IEnumerable<T> vals, bool frall, System.Predicate<T> pred) {
      foreach (var u in vals) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public static IEnumerable<bool> AllBooleans() {
      yield return false;
      yield return true;
    }
    public static IEnumerable<char> AllChars() {
      for (int i = 0; i < 0x10000; i++) {
        yield return (char)i;
      }
    }
    public static IEnumerable<BigInteger> AllIntegers() {
      yield return new BigInteger(0);
      for (var j = new BigInteger(1);; j++) {
        yield return j;
        yield return -j;
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true; ) {
          j--;
          yield return j;
        }
      } else if (hi == null) {
        for (var j = (BigInteger)lo; true; j++) {
          yield return j;
        }
      } else {
        for (var j = (BigInteger)lo; j < hi; j++) {
          yield return j;
        }
      }
    }
    public static IEnumerable<T> SingleValue<T>(T e) {
      yield return e;
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }

    public static U CastConverter<T, U>(T t) {
      return (U)(object)t;
    }

    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new ArraySequence<T>((T[])array.Clone());
    }
    // In .NET version 4.5, it is possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u)
    {
      return u;
    }

    public static U Let<T, U>(T t, Func<T,U> f) {
      return f(t);
    }

    public static A Id<A>(A a) {
      return a;
    }

    public static void WithHaltHandling(Action action) {
      try {
        action();
      } catch (HaltException e) {
        Console.WriteLine("[Program halted] " + e.Message);
      }
    }
  }

  public class BigOrdinal {
    public static bool IsLimit(BigInteger ord) {
      return ord == 0;
    }
    public static bool IsSucc(BigInteger ord) {
      return 0 < ord;
    }
    public static BigInteger Offset(BigInteger ord) {
      return ord;
    }
    public static bool IsNat(BigInteger ord) {
      return true;  // at run time, every ORDINAL is a natural number
    }
  }

  public struct BigRational
  {
    public static readonly BigRational ZERO = new BigRational(0);

    // We need to deal with the special case "num == 0 && den == 0", because
    // that's what C#'s default struct constructor will produce for BigRational. :(
    // To deal with it, we ignore "den" when "num" is 0.
    BigInteger num, den;  // invariant 1 <= den || (num == 0 && den == 0)
    public override string ToString() {
      int log10;
      if (num.IsZero || den.IsOne) {
        return string.Format("{0}.0", num);
      } else if (IsPowerOf10(den, out log10)) {
        string sign;
        string digits;
        if (num.Sign < 0) {
          sign = "-"; digits = (-num).ToString();
        } else {
          sign = ""; digits = num.ToString();
        }
        if (log10 < digits.Length) {
          var n = digits.Length - log10;
          return string.Format("{0}{1}.{2}", sign, digits.Substring(0, n), digits.Substring(n));
        } else {
          return string.Format("{0}0.{1}{2}", sign, new string('0', log10 - digits.Length), digits);
        }
      } else {
        return string.Format("({0}.0 / {1}.0)", num, den);
      }
    }
    public bool IsPowerOf10(BigInteger x, out int log10) {
      log10 = 0;
      if (x.IsZero) {
        return false;
      }
      while (true) {  // invariant: x != 0 && x * 10^log10 == old(x)
        if (x.IsOne) {
          return true;
        } else if (x % 10 == 0) {
          log10++;
          x /= 10;
        } else {
          return false;
        }
      }
    }
    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    public BigInteger ToBigInteger() {
      if (num.IsZero || den.IsOne) {
        return num;
      } else if (0 < num.Sign) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }
    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      if (a.num.IsZero) {
        aa = a.num;
        bb = b.num;
        dd = b.den;
      } else if (b.num.IsZero) {
        aa = a.num;
        dd = a.den;
        bb = b.num;
      } else {
        var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
        var xx = a.den / gcd;
        var yy = b.den / gcd;
        // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
        aa = a.num * yy;
        bb = b.num * xx;
        dd = a.den * yy;
      }
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }
      BigInteger aa, bb, dd;
      Normalize(this, that, out aa, out bb, out dd);
      return aa.CompareTo(bb);
    }
    public int Sign {
      get {
        return num.Sign;
      }
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return a.CompareTo(b) > 0;
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return a.CompareTo(b) >= 0;
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num.Sign) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }

  public class HaltException : Exception {
    public HaltException(object message) : base(message.ToString())
    {
    }
  }
}

namespace @_System
{
  public class Tuple2<T0,T1> {
    public readonly T0 _0;
    public readonly T1 _1;
    public Tuple2(T0 _0, T1 _1) {
      this._0 = _0;
      this._1 = _1;
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple2<T0,T1>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ")";
      return s;
    }
    public static Tuple2<T0,T1> Default(T0 _default_T0, T1 _default_T1) {
      return create(_default_T0, _default_T1);
    }
    public static Dafny.TypeDescriptor<_System.Tuple2<T0, T1>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1) {
      return new Dafny.TypeDescriptor<_System.Tuple2<T0, T1>>(_System.Tuple2<T0, T1>.Default(_td_T0.Default(), _td_T1.Default()));
    }
    public static Tuple2<T0,T1> create(T0 _0, T1 _1) {
      return new Tuple2<T0,T1>(_0, _1);
    }
    public bool is____hMake2 { get { return true; } }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
  }

} // end of namespace _System
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
  }
} // end of namespace Dafny
namespace _System {


  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }








  public class Tuple0 {
    public Tuple0() {
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple0;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      return "()";
    }
    private static readonly Tuple0 theDefault = create();
    public static Tuple0 Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_System.Tuple0> _TYPE = new Dafny.TypeDescriptor<_System.Tuple0>(_System.Tuple0.Default());
    public static Dafny.TypeDescriptor<_System.Tuple0> _TypeDescriptor() {
      return _TYPE;
    }
    public static Tuple0 create() {
      return new Tuple0();
    }
    public static System.Collections.Generic.IEnumerable<Tuple0> AllSingletonConstructors {
      get {
        yield return Tuple0.create();
      }
    }
  }
} // end of namespace _System
namespace _module {

  public abstract class BasicTerm {
    public BasicTerm() { }
    private static readonly BasicTerm theDefault = create_Value(BigInteger.Zero);
    public static BasicTerm Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<BasicTerm> _TYPE = new Dafny.TypeDescriptor<BasicTerm>(BasicTerm.Default());
    public static Dafny.TypeDescriptor<BasicTerm> _TypeDescriptor() {
      return _TYPE;
    }
    public static BasicTerm create_Value(BigInteger val) {
      return new BasicTerm_Value(val);
    }
    public static BasicTerm create_StackVar(BigInteger id) {
      return new BasicTerm_StackVar(id);
    }
    public bool is_Value { get { return this is BasicTerm_Value; } }
    public bool is_StackVar { get { return this is BasicTerm_StackVar; } }
    public BigInteger dtor_val {
      get {
        var d = this;
        return ((BasicTerm_Value)d).val; 
      }
    }
    public BigInteger dtor_id {
      get {
        var d = this;
        return ((BasicTerm_StackVar)d).id; 
      }
    }
  }
  public class BasicTerm_Value : BasicTerm {
    public readonly BigInteger val;
    public BasicTerm_Value(BigInteger val) {
      this.val = val;
    }
    public override bool Equals(object other) {
      var oth = other as BasicTerm_Value;
      return oth != null && this.val == oth.val;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.val));
      return (int) hash;
    }
    public override string ToString() {
      string s = "BasicTerm.Value";
      s += "(";
      s += Dafny.Helpers.ToString(this.val);
      s += ")";
      return s;
    }
  }
  public class BasicTerm_StackVar : BasicTerm {
    public readonly BigInteger id;
    public BasicTerm_StackVar(BigInteger id) {
      this.id = id;
    }
    public override bool Equals(object other) {
      var oth = other as BasicTerm_StackVar;
      return oth != null && this.id == oth.id;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.id));
      return (int) hash;
    }
    public override string ToString() {
      string s = "BasicTerm.StackVar";
      s += "(";
      s += Dafny.Helpers.ToString(this.id);
      s += ")";
      return s;
    }
  }

  public abstract class StackElem {
    public StackElem() { }
    private static readonly StackElem theDefault = create_Op(Dafny.Sequence<BasicTerm>.Empty);
    public static StackElem Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<StackElem> _TYPE = new Dafny.TypeDescriptor<StackElem>(StackElem.Default());
    public static Dafny.TypeDescriptor<StackElem> _TypeDescriptor() {
      return _TYPE;
    }
    public static StackElem create_Op(Dafny.ISequence<BasicTerm> input__stack) {
      return new StackElem_Op(input__stack);
    }
    public static StackElem create_COp(BasicTerm elem1, BasicTerm elem2) {
      return new StackElem_COp(elem1, elem2);
    }
    public bool is_Op { get { return this is StackElem_Op; } }
    public bool is_COp { get { return this is StackElem_COp; } }
    public Dafny.ISequence<BasicTerm> dtor_input__stack {
      get {
        var d = this;
        return ((StackElem_Op)d).input__stack; 
      }
    }
    public BasicTerm dtor_elem1 {
      get {
        var d = this;
        return ((StackElem_COp)d).elem1; 
      }
    }
    public BasicTerm dtor_elem2 {
      get {
        var d = this;
        return ((StackElem_COp)d).elem2; 
      }
    }
  }
  public class StackElem_Op : StackElem {
    public readonly Dafny.ISequence<BasicTerm> input__stack;
    public StackElem_Op(Dafny.ISequence<BasicTerm> input__stack) {
      this.input__stack = input__stack;
    }
    public override bool Equals(object other) {
      var oth = other as StackElem_Op;
      return oth != null && object.Equals(this.input__stack, oth.input__stack);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.input__stack));
      return (int) hash;
    }
    public override string ToString() {
      string s = "StackElem.Op";
      s += "(";
      s += Dafny.Helpers.ToString(this.input__stack);
      s += ")";
      return s;
    }
  }
  public class StackElem_COp : StackElem {
    public readonly BasicTerm elem1;
    public readonly BasicTerm elem2;
    public StackElem_COp(BasicTerm elem1, BasicTerm elem2) {
      this.elem1 = elem1;
      this.elem2 = elem2;
    }
    public override bool Equals(object other) {
      var oth = other as StackElem_COp;
      return oth != null && object.Equals(this.elem1, oth.elem1) && object.Equals(this.elem2, oth.elem2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.elem1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.elem2));
      return (int) hash;
    }
    public override string ToString() {
      string s = "StackElem.COp";
      s += "(";
      s += Dafny.Helpers.ToString(this.elem1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.elem2);
      s += ")";
      return s;
    }
  }

  public class ASFS {
    public readonly Dafny.ISequence<BasicTerm> input;
    public readonly Dafny.IMap<BigInteger,StackElem> dict;
    public readonly Dafny.ISequence<BasicTerm> output;
    public ASFS(Dafny.ISequence<BasicTerm> input, Dafny.IMap<BigInteger,StackElem> dict, Dafny.ISequence<BasicTerm> output) {
      this.input = input;
      this.dict = dict;
      this.output = output;
    }
    public override bool Equals(object other) {
      var oth = other as ASFS;
      return oth != null && object.Equals(this.input, oth.input) && object.Equals(this.dict, oth.dict) && object.Equals(this.output, oth.output);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.input));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.dict));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.output));
      return (int) hash;
    }
    public override string ToString() {
      string s = "ASFS.SFS";
      s += "(";
      s += Dafny.Helpers.ToString(this.input);
      s += ", ";
      s += Dafny.Helpers.ToString(this.dict);
      s += ", ";
      s += Dafny.Helpers.ToString(this.output);
      s += ")";
      return s;
    }
    private static readonly ASFS theDefault = create(Dafny.Sequence<BasicTerm>.Empty, Dafny.Map<BigInteger, StackElem>.Empty, Dafny.Sequence<BasicTerm>.Empty);
    public static ASFS Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<ASFS> _TYPE = new Dafny.TypeDescriptor<ASFS>(ASFS.Default());
    public static Dafny.TypeDescriptor<ASFS> _TypeDescriptor() {
      return _TYPE;
    }
    public static ASFS create(Dafny.ISequence<BasicTerm> input, Dafny.IMap<BigInteger,StackElem> dict, Dafny.ISequence<BasicTerm> output) {
      return new ASFS(input, dict, output);
    }
    public bool is_SFS { get { return true; } }
    public Dafny.ISequence<BasicTerm> dtor_input {
      get {
        return this.input;
      }
    }
    public Dafny.IMap<BigInteger,StackElem> dtor_dict {
      get {
        return this.dict;
      }
    }
    public Dafny.ISequence<BasicTerm> dtor_output {
      get {
        return this.output;
      }
    }
  }

  public partial class __default {
    public static BigInteger getId(BasicTerm el) {
      BasicTerm _source0 = el;
      {
        BigInteger _3375___mcc_h1 = ((BasicTerm_StackVar)_source0).id;
        BigInteger _3376_x = _3375___mcc_h1;
        return _3376_x;
      }
    }
    public static Dafny.ISet<BigInteger> idsFromInput(Dafny.ISequence<BasicTerm> input) {
      Dafny.ISet<BigInteger> _3377___accumulator = Dafny.Set<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((input).Equals((Dafny.Sequence<BasicTerm>.FromElements()))) {
        return Dafny.Set<BigInteger>.Union(Dafny.Set<BigInteger>.FromElements(), _3377___accumulator);
      } else {
        BasicTerm _source1 = (input).Select(BigInteger.Zero);
        if (_source1.is_Value) {
          BigInteger _3378___mcc_h0 = ((BasicTerm_Value)_source1).val;
          BigInteger _3379_val = _3378___mcc_h0;
          Dafny.ISequence<BasicTerm> _in0 = (input).Drop(BigInteger.One);
          input = _in0;
          goto TAIL_CALL_START;
        } else {
          BigInteger _3380___mcc_h1 = ((BasicTerm_StackVar)_source1).id;
          BigInteger _3381_id = _3380___mcc_h1;
          _3377___accumulator = Dafny.Set<BigInteger>.Union(_3377___accumulator, Dafny.Set<BigInteger>.FromElements(_3381_id));
          Dafny.ISequence<BasicTerm> _in1 = (input).Drop(BigInteger.One);
          input = _in1;
          goto TAIL_CALL_START;
        }
      }
    }
    public static BigInteger atId(Dafny.ISequence<BasicTerm> input, BigInteger pos)
    {
    TAIL_CALL_START: ;
      if ((pos).Sign == 0) {
        BasicTerm _source2 = (input).Select(BigInteger.Zero);
        {
          BigInteger _3382___mcc_h1 = ((BasicTerm_StackVar)_source2).id;
          BigInteger _3383_x = _3382___mcc_h1;
          return _3383_x;
        }
      } else {
        Dafny.ISequence<BasicTerm> _in2 = input;
        BigInteger _in3 = (pos) - (BigInteger.One);
        input = _in2;
        pos = _in3;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger getPos(Dafny.ISequence<BasicTerm> input, BigInteger id)
    {
      BigInteger _3384___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      BasicTerm _source3 = (input).Select(BigInteger.Zero);
      {
        BigInteger _3385___mcc_h3 = ((BasicTerm_StackVar)_source3).id;
        BigInteger _3386_x = _3385___mcc_h3;
        if ((_3386_x) == (id)) {
          return (BigInteger.Zero) + (_3384___accumulator);
        } else {
          _3384___accumulator = (_3384___accumulator) + (BigInteger.One);
          Dafny.ISequence<BasicTerm> _in4 = (input).Drop(BigInteger.One);
          BigInteger _in5 = id;
          input = _in4;
          id = _in5;
          goto TAIL_CALL_START;
        }
      }
    }
    public static Dafny.ISet<BigInteger> dependentIds(Dafny.ISequence<BasicTerm> inputStack, Dafny.IMap<BigInteger,StackElem> dict, BigInteger key, Dafny.ISet<BigInteger> previously__ids)
    {
      StackElem _source4 = Dafny.Map<BigInteger, StackElem>.Select(dict,key);
      if (_source4.is_Op) {
        Dafny.ISequence<BasicTerm> _3387___mcc_h0 = ((StackElem_Op)_source4).input__stack;
        Dafny.ISequence<BasicTerm> _3388_l = _3387___mcc_h0;
        return Dafny.Set<BigInteger>.Union(Dafny.Set<BigInteger>.Union(Dafny.Helpers.Id<Func<Dafny.ISequence<BasicTerm>, Dafny.IMap<BigInteger,StackElem>, Dafny.ISet<BigInteger>, Dafny.ISequence<BasicTerm>, BigInteger, Dafny.ISet<BigInteger>>>((_3389_l, _3390_dict, _3391_previously__ids, _3392_inputStack, _3393_key) => ((System.Func<Dafny.ISet<BigInteger>>)(() => {
          var _coll0 = new System.Collections.Generic.List<BigInteger>();
          foreach (BasicTerm _compr_0 in (_3389_l).Elements) {
            BasicTerm _3394_el = (BasicTerm)_compr_0;
            foreach (BigInteger _compr_1 in (__default.dependentIds(_3392_inputStack, _3390_dict, __default.getId(_3394_el), Dafny.Set<BigInteger>.Union(_3391_previously__ids, Dafny.Set<BigInteger>.FromElements(_3393_key)))).Elements) {
              BigInteger _3395_x = (BigInteger)_compr_1;
              if ((((_3389_l).Contains((_3394_el))) && (((System.Func<BasicTerm, bool>)((_source5) => {
                if (_source5.is_Value) {
                  BigInteger _3396___mcc_h3 = ((BasicTerm_Value)_source5).val;
                  return Dafny.Helpers.Let<BigInteger, bool>(_3396___mcc_h3, _pat_let0_0 => Dafny.Helpers.Let<BigInteger, bool>(_pat_let0_0, _3397_x => false));
                } else {
                  BigInteger _3398___mcc_h4 = ((BasicTerm_StackVar)_source5).id;
                  return Dafny.Helpers.Let<BigInteger, bool>(_3398___mcc_h4, _pat_let1_0 => Dafny.Helpers.Let<BigInteger, bool>(_pat_let1_0, _3399_x1 => (((__default.idsFromInput(_3392_inputStack)).Contains((_3399_x1))) ? (false) : (true))));
                }
              }))(_3394_el))) && ((__default.dependentIds(_3392_inputStack, _3390_dict, __default.getId(_3394_el), Dafny.Set<BigInteger>.Union(_3391_previously__ids, Dafny.Set<BigInteger>.FromElements(_3393_key)))).Contains((_3395_x)))) {
                _coll0.Add(_3395_x);
              }
            }
          }
          return Dafny.Set<BigInteger>.FromCollection(_coll0);
        }))())(_3388_l, dict, previously__ids, inputStack, key), previously__ids), Dafny.Set<BigInteger>.FromElements(key));
      } else {
        BasicTerm _3400___mcc_h1 = ((StackElem_COp)_source4).elem1;
        BasicTerm _3401___mcc_h2 = ((StackElem_COp)_source4).elem2;
        BasicTerm _3402_el2 = _3401___mcc_h2;
        BasicTerm _3403_el1 = _3400___mcc_h1;
        return Dafny.Set<BigInteger>.Union(Dafny.Set<BigInteger>.Union(Dafny.Set<BigInteger>.Union(Dafny.Helpers.Id<Func<BasicTerm, Dafny.IMap<BigInteger,StackElem>, Dafny.ISet<BigInteger>, Dafny.ISequence<BasicTerm>, BigInteger, Dafny.ISet<BigInteger>>>((_3404_el1, _3405_dict, _3406_previously__ids, _3407_inputStack, _3408_key) => ((System.Func<Dafny.ISet<BigInteger>>)(() => {
          var _coll1 = new System.Collections.Generic.List<BigInteger>();
          foreach (BigInteger _compr_2 in (__default.dependentIds(_3407_inputStack, _3405_dict, __default.getId(_3404_el1), Dafny.Set<BigInteger>.Union(_3406_previously__ids, Dafny.Set<BigInteger>.FromElements(_3408_key)))).Elements) {
            BigInteger _3409_x = (BigInteger)_compr_2;
            if ((((System.Func<BasicTerm, bool>)((_source6) => {
              if (_source6.is_Value) {
                BigInteger _3410___mcc_h5 = ((BasicTerm_Value)_source6).val;
                return Dafny.Helpers.Let<BigInteger, bool>(_3410___mcc_h5, _pat_let2_0 => Dafny.Helpers.Let<BigInteger, bool>(_pat_let2_0, _3411_x => false));
              } else {
                BigInteger _3412___mcc_h6 = ((BasicTerm_StackVar)_source6).id;
                return Dafny.Helpers.Let<BigInteger, bool>(_3412___mcc_h6, _pat_let3_0 => Dafny.Helpers.Let<BigInteger, bool>(_pat_let3_0, _3413_x1 => (((__default.idsFromInput(_3407_inputStack)).Contains((_3413_x1))) ? (false) : (true))));
              }
            }))(_3404_el1)) && ((__default.dependentIds(_3407_inputStack, _3405_dict, __default.getId(_3404_el1), Dafny.Set<BigInteger>.Union(_3406_previously__ids, Dafny.Set<BigInteger>.FromElements(_3408_key)))).Contains((_3409_x)))) {
              _coll1.Add(_3409_x);
            }
          }
          return Dafny.Set<BigInteger>.FromCollection(_coll1);
        }))())(_3403_el1, dict, previously__ids, inputStack, key), Dafny.Helpers.Id<Func<BasicTerm, Dafny.IMap<BigInteger,StackElem>, Dafny.ISet<BigInteger>, Dafny.ISequence<BasicTerm>, BigInteger, Dafny.ISet<BigInteger>>>((_3414_el1, _3415_dict, _3416_previously__ids, _3417_inputStack, _3418_key) => ((System.Func<Dafny.ISet<BigInteger>>)(() => {
          var _coll2 = new System.Collections.Generic.List<BigInteger>();
          foreach (BigInteger _compr_3 in (__default.dependentIds(_3417_inputStack, _3415_dict, __default.getId(_3414_el1), Dafny.Set<BigInteger>.Union(_3416_previously__ids, Dafny.Set<BigInteger>.FromElements(_3418_key)))).Elements) {
            BigInteger _3419_x = (BigInteger)_compr_3;
            if ((((System.Func<BasicTerm, bool>)((_source7) => {
              if (_source7.is_Value) {
                BigInteger _3420___mcc_h7 = ((BasicTerm_Value)_source7).val;
                return Dafny.Helpers.Let<BigInteger, bool>(_3420___mcc_h7, _pat_let4_0 => Dafny.Helpers.Let<BigInteger, bool>(_pat_let4_0, _3421_x => false));
              } else {
                BigInteger _3422___mcc_h8 = ((BasicTerm_StackVar)_source7).id;
                return Dafny.Helpers.Let<BigInteger, bool>(_3422___mcc_h8, _pat_let5_0 => Dafny.Helpers.Let<BigInteger, bool>(_pat_let5_0, _3423_x1 => (((__default.idsFromInput(_3417_inputStack)).Contains((_3423_x1))) ? (false) : (true))));
              }
            }))(_3414_el1)) && ((__default.dependentIds(_3417_inputStack, _3415_dict, __default.getId(_3414_el1), Dafny.Set<BigInteger>.Union(_3416_previously__ids, Dafny.Set<BigInteger>.FromElements(_3418_key)))).Contains((_3419_x)))) {
              _coll2.Add(_3419_x);
            }
          }
          return Dafny.Set<BigInteger>.FromCollection(_coll2);
        }))())(_3403_el1, dict, previously__ids, inputStack, key)), previously__ids), Dafny.Set<BigInteger>.FromElements(key));
      }
    }
    public static bool compareDictElems(Dafny.ISequence<BasicTerm> input1, Dafny.ISequence<BasicTerm> input2, Dafny.IMap<BigInteger,StackElem> dict1, Dafny.IMap<BigInteger,StackElem> dict2, BigInteger key1, BigInteger key2, Dafny.ISet<BigInteger> prev__ids1, Dafny.ISet<BigInteger> prev__ids2)
    {
      bool b = false;
      _System.Tuple2<StackElem, StackElem> _source8 = @_System.Tuple2<StackElem, StackElem>.create(Dafny.Map<BigInteger, StackElem>.Select(dict1,key1), Dafny.Map<BigInteger, StackElem>.Select(dict2,key2));
      {
        StackElem _3424___mcc_h0 = ((_System.Tuple2<StackElem, StackElem>)_source8)._0;
        StackElem _3425___mcc_h1 = ((_System.Tuple2<StackElem, StackElem>)_source8)._1;
        StackElem _source9 = _3424___mcc_h0;
        if (_source9.is_Op) {
          Dafny.ISequence<BasicTerm> _3426___mcc_h2 = ((StackElem_Op)_source9).input__stack;
          StackElem _source10 = _3425___mcc_h1;
          if (_source10.is_Op) {
            Dafny.ISequence<BasicTerm> _3427___mcc_h3 = ((StackElem_Op)_source10).input__stack;
            {
              Dafny.ISequence<BasicTerm> _3428_l2 = _3427___mcc_h3;
              Dafny.ISequence<BasicTerm> _3429_l1 = _3426___mcc_h2;
              if ((new BigInteger((_3429_l1).Count)) != (new BigInteger((_3428_l2).Count))) {
                b = false;
                return b;
              } else {
                BigInteger _3430_i;
                _3430_i = BigInteger.Zero;
                while ((_3430_i) < (new BigInteger((_3429_l1).Count))) {
                  _System.Tuple2<BasicTerm, BasicTerm> _source11 = @_System.Tuple2<BasicTerm, BasicTerm>.create((_3429_l1).Select(_3430_i), (_3428_l2).Select(_3430_i));
                  {
                    BasicTerm _3431___mcc_h19 = ((_System.Tuple2<BasicTerm, BasicTerm>)_source11)._0;
                    BasicTerm _3432___mcc_h20 = ((_System.Tuple2<BasicTerm, BasicTerm>)_source11)._1;
                    BasicTerm _source12 = _3431___mcc_h19;
                    if (_source12.is_Value) {
                      BigInteger _3433___mcc_h21 = ((BasicTerm_Value)_source12).val;
                      BasicTerm _source13 = _3432___mcc_h20;
                      if (_source13.is_Value) {
                        BigInteger _3434___mcc_h22 = ((BasicTerm_Value)_source13).val;
                        {
                          BigInteger _3435_x2 = _3434___mcc_h22;
                          BigInteger _3436_x1 = _3433___mcc_h21;
                          if ((_3436_x1) != (_3435_x2)) {
                            b = false;
                            return b;
                          }
                        }
                      } else {
                        BigInteger _3437___mcc_h23 = ((BasicTerm_StackVar)_source13).id;
                        {
                          BigInteger _3438_x2 = _3437___mcc_h23;
                          BigInteger _3439_x1 = _3433___mcc_h21;
                          b = false;
                          return b;
                        }
                      }
                    } else {
                      BigInteger _3440___mcc_h24 = ((BasicTerm_StackVar)_source12).id;
                      BasicTerm _source14 = _3432___mcc_h20;
                      if (_source14.is_Value) {
                        BigInteger _3441___mcc_h25 = ((BasicTerm_Value)_source14).val;
                        {
                          BigInteger _3442_x2 = _3441___mcc_h25;
                          BigInteger _3443_x1 = _3440___mcc_h24;
                          b = false;
                          return b;
                        }
                      } else {
                        BigInteger _3444___mcc_h26 = ((BasicTerm_StackVar)_source14).id;
                        {
                          BigInteger _3445_x2 = _3444___mcc_h26;
                          BigInteger _3446_x1 = _3440___mcc_h24;
                          if (((__default.idsFromInput(input1)).Contains((_3446_x1))) && ((__default.idsFromInput(input2)).Contains((_3445_x2)))) {
                            if ((__default.getPos(input1, _3446_x1)) != (__default.getPos(input2, _3445_x2))) {
                              b = false;
                              return b;
                            }
                          } else if (((dict1).Contains((_3446_x1))) && ((dict2).Contains((_3445_x2)))) {
                            bool _3447_aux;
                            bool _out0;
                            _out0 = __default.compareDictElems(input1, input2, dict1, dict2, _3446_x1, _3445_x2, Dafny.Set<BigInteger>.Union(prev__ids1, Dafny.Set<BigInteger>.FromElements(key1)), Dafny.Set<BigInteger>.Union(prev__ids2, Dafny.Set<BigInteger>.FromElements(key2)));
                            _3447_aux = _out0;
                            if (!(_3447_aux)) {
                              b = false;
                              return b;
                            }
                          } else {
                            b = false;
                            return b;
                          }
                        }
                      }
                    }
                  }
                  _3430_i = (_3430_i) + (BigInteger.One);
                }
                b = true;
                return b;
              }
            }
          } else {
            BasicTerm _3448___mcc_h4 = ((StackElem_COp)_source10).elem1;
            BasicTerm _3449___mcc_h5 = ((StackElem_COp)_source10).elem2;
            {
              BasicTerm _3450_y2 = _3449___mcc_h5;
              BasicTerm _3451_x2 = _3448___mcc_h4;
              Dafny.ISequence<BasicTerm> _3452_l1 = _3426___mcc_h2;
              b = false;
              return b;
            }
          }
        } else {
          BasicTerm _3453___mcc_h6 = ((StackElem_COp)_source9).elem1;
          BasicTerm _3454___mcc_h7 = ((StackElem_COp)_source9).elem2;
          StackElem _source15 = _3425___mcc_h1;
          if (_source15.is_Op) {
            Dafny.ISequence<BasicTerm> _3455___mcc_h8 = ((StackElem_Op)_source15).input__stack;
            {
              Dafny.ISequence<BasicTerm> _3456_l2 = _3455___mcc_h8;
              BasicTerm _3457_y1 = _3454___mcc_h7;
              BasicTerm _3458_x1 = _3453___mcc_h6;
              b = false;
              return b;
            }
          } else {
            BasicTerm _3459___mcc_h9 = ((StackElem_COp)_source15).elem1;
            BasicTerm _3460___mcc_h10 = ((StackElem_COp)_source15).elem2;
            {
              BasicTerm _3461_el22 = _3460___mcc_h10;
              BasicTerm _3462_el21 = _3459___mcc_h9;
              BasicTerm _3463_el12 = _3454___mcc_h7;
              BasicTerm _3464_el11 = _3453___mcc_h6;
              bool _3465_b1;
              _3465_b1 = true;
              _System.Tuple2<BasicTerm, BasicTerm> _source16 = @_System.Tuple2<BasicTerm, BasicTerm>.create(_3464_el11, _3462_el21);
              {
                BasicTerm _3466___mcc_h27 = ((_System.Tuple2<BasicTerm, BasicTerm>)_source16)._0;
                BasicTerm _3467___mcc_h28 = ((_System.Tuple2<BasicTerm, BasicTerm>)_source16)._1;
                BasicTerm _source17 = _3466___mcc_h27;
                if (_source17.is_Value) {
                  BigInteger _3468___mcc_h29 = ((BasicTerm_Value)_source17).val;
                  BasicTerm _source18 = _3467___mcc_h28;
                  if (_source18.is_Value) {
                    BigInteger _3469___mcc_h30 = ((BasicTerm_Value)_source18).val;
                    {
                      BigInteger _3470_x2 = _3469___mcc_h30;
                      BigInteger _3471_x1 = _3468___mcc_h29;
                      _3465_b1 = (_3471_x1) == (_3470_x2);
                    }
                  } else {
                    BigInteger _3472___mcc_h31 = ((BasicTerm_StackVar)_source18).id;
                    {
                      BigInteger _3473_x2 = _3472___mcc_h31;
                      BigInteger _3474_x1 = _3468___mcc_h29;
                      {
                        _3465_b1 = false;
                      }
                    }
                  }
                } else {
                  BigInteger _3475___mcc_h32 = ((BasicTerm_StackVar)_source17).id;
                  BasicTerm _source19 = _3467___mcc_h28;
                  if (_source19.is_Value) {
                    BigInteger _3476___mcc_h33 = ((BasicTerm_Value)_source19).val;
                    {
                      BigInteger _3477_x2 = _3476___mcc_h33;
                      BigInteger _3478_x1 = _3475___mcc_h32;
                      {
                        _3465_b1 = false;
                      }
                    }
                  } else {
                    BigInteger _3479___mcc_h34 = ((BasicTerm_StackVar)_source19).id;
                    {
                      BigInteger _3480_x2 = _3479___mcc_h34;
                      BigInteger _3481_x1 = _3475___mcc_h32;
                      if (((__default.idsFromInput(input1)).Contains((_3481_x1))) && ((__default.idsFromInput(input2)).Contains((_3480_x2)))) {
                        _3465_b1 = (__default.getPos(input1, _3481_x1)) == (__default.getPos(input2, _3480_x2));
                      } else if (((dict1).Contains((_3481_x1))) && ((dict2).Contains((_3480_x2)))) {
                        bool _out1;
                        _out1 = __default.compareDictElems(input1, input2, dict1, dict2, _3481_x1, _3480_x2, Dafny.Set<BigInteger>.Union(prev__ids1, Dafny.Set<BigInteger>.FromElements(key1)), Dafny.Set<BigInteger>.Union(prev__ids2, Dafny.Set<BigInteger>.FromElements(key2)));
                        _3465_b1 = _out1;
                      } else {
                        _3465_b1 = false;
                      }
                    }
                  }
                }
              }
              if (_3465_b1) {
                _System.Tuple2<BasicTerm, BasicTerm> _source20 = @_System.Tuple2<BasicTerm, BasicTerm>.create(_3463_el12, _3461_el22);
                {
                  BasicTerm _3482___mcc_h35 = ((_System.Tuple2<BasicTerm, BasicTerm>)_source20)._0;
                  BasicTerm _3483___mcc_h36 = ((_System.Tuple2<BasicTerm, BasicTerm>)_source20)._1;
                  BasicTerm _source21 = _3482___mcc_h35;
                  if (_source21.is_Value) {
                    BigInteger _3484___mcc_h37 = ((BasicTerm_Value)_source21).val;
                    BasicTerm _source22 = _3483___mcc_h36;
                    if (_source22.is_Value) {
                      BigInteger _3485___mcc_h38 = ((BasicTerm_Value)_source22).val;
                      {
                        BigInteger _3486_x2 = _3485___mcc_h38;
                        BigInteger _3487_x1 = _3484___mcc_h37;
                        _3465_b1 = (_3487_x1) == (_3486_x2);
                      }
                    } else {
                      BigInteger _3488___mcc_h39 = ((BasicTerm_StackVar)_source22).id;
                      {
                        BigInteger _3489_x2 = _3488___mcc_h39;
                        BigInteger _3490_x1 = _3484___mcc_h37;
                        {
                          _3465_b1 = false;
                        }
                      }
                    }
                  } else {
                    BigInteger _3491___mcc_h40 = ((BasicTerm_StackVar)_source21).id;
                    BasicTerm _source23 = _3483___mcc_h36;
                    if (_source23.is_Value) {
                      BigInteger _3492___mcc_h41 = ((BasicTerm_Value)_source23).val;
                      {
                        BigInteger _3493_x2 = _3492___mcc_h41;
                        BigInteger _3494_x1 = _3491___mcc_h40;
                        {
                          _3465_b1 = false;
                        }
                      }
                    } else {
                      BigInteger _3495___mcc_h42 = ((BasicTerm_StackVar)_source23).id;
                      {
                        BigInteger _3496_x2 = _3495___mcc_h42;
                        BigInteger _3497_x1 = _3491___mcc_h40;
                        if (((__default.idsFromInput(input1)).Contains((_3497_x1))) && ((__default.idsFromInput(input2)).Contains((_3496_x2)))) {
                          _3465_b1 = (__default.getPos(input1, _3497_x1)) == (__default.getPos(input2, _3496_x2));
                        } else if (((dict1).Contains((_3497_x1))) && ((dict2).Contains((_3496_x2)))) {
                          bool _out2;
                          _out2 = __default.compareDictElems(input1, input2, dict1, dict2, _3497_x1, _3496_x2, Dafny.Set<BigInteger>.Union(prev__ids1, Dafny.Set<BigInteger>.FromElements(key1)), Dafny.Set<BigInteger>.Union(prev__ids2, Dafny.Set<BigInteger>.FromElements(key2)));
                          _3465_b1 = _out2;
                        } else {
                          _3465_b1 = false;
                        }
                      }
                    }
                  }
                }
                if (_3465_b1) {
                  b = true;
                  return b;
                }
              }
              _3465_b1 = true;
              _System.Tuple2<BasicTerm, BasicTerm> _source24 = @_System.Tuple2<BasicTerm, BasicTerm>.create(_3463_el12, _3462_el21);
              {
                BasicTerm _3498___mcc_h43 = ((_System.Tuple2<BasicTerm, BasicTerm>)_source24)._0;
                BasicTerm _3499___mcc_h44 = ((_System.Tuple2<BasicTerm, BasicTerm>)_source24)._1;
                BasicTerm _source25 = _3498___mcc_h43;
                if (_source25.is_Value) {
                  BigInteger _3500___mcc_h45 = ((BasicTerm_Value)_source25).val;
                  BasicTerm _source26 = _3499___mcc_h44;
                  if (_source26.is_Value) {
                    BigInteger _3501___mcc_h46 = ((BasicTerm_Value)_source26).val;
                    {
                      BigInteger _3502_x2 = _3501___mcc_h46;
                      BigInteger _3503_x1 = _3500___mcc_h45;
                      _3465_b1 = (_3503_x1) == (_3502_x2);
                    }
                  } else {
                    BigInteger _3504___mcc_h47 = ((BasicTerm_StackVar)_source26).id;
                    {
                      BigInteger _3505_x2 = _3504___mcc_h47;
                      BigInteger _3506_x1 = _3500___mcc_h45;
                      {
                        _3465_b1 = false;
                      }
                    }
                  }
                } else {
                  BigInteger _3507___mcc_h48 = ((BasicTerm_StackVar)_source25).id;
                  BasicTerm _source27 = _3499___mcc_h44;
                  if (_source27.is_Value) {
                    BigInteger _3508___mcc_h49 = ((BasicTerm_Value)_source27).val;
                    {
                      BigInteger _3509_x2 = _3508___mcc_h49;
                      BigInteger _3510_x1 = _3507___mcc_h48;
                      {
                        _3465_b1 = false;
                      }
                    }
                  } else {
                    BigInteger _3511___mcc_h50 = ((BasicTerm_StackVar)_source27).id;
                    {
                      BigInteger _3512_x2 = _3511___mcc_h50;
                      BigInteger _3513_x1 = _3507___mcc_h48;
                      if (((__default.idsFromInput(input1)).Contains((_3513_x1))) && ((__default.idsFromInput(input2)).Contains((_3512_x2)))) {
                        _3465_b1 = (__default.getPos(input1, _3513_x1)) == (__default.getPos(input2, _3512_x2));
                      } else if (((dict1).Contains((_3513_x1))) && ((dict2).Contains((_3512_x2)))) {
                        bool _out3;
                        _out3 = __default.compareDictElems(input1, input2, dict1, dict2, _3513_x1, _3512_x2, Dafny.Set<BigInteger>.Union(prev__ids1, Dafny.Set<BigInteger>.FromElements(key1)), Dafny.Set<BigInteger>.Union(prev__ids2, Dafny.Set<BigInteger>.FromElements(key2)));
                        _3465_b1 = _out3;
                      } else {
                        _3465_b1 = false;
                      }
                    }
                  }
                }
              }
              if (_3465_b1) {
                _System.Tuple2<BasicTerm, BasicTerm> _source28 = @_System.Tuple2<BasicTerm, BasicTerm>.create(_3464_el11, _3461_el22);
                {
                  BasicTerm _3514___mcc_h51 = ((_System.Tuple2<BasicTerm, BasicTerm>)_source28)._0;
                  BasicTerm _3515___mcc_h52 = ((_System.Tuple2<BasicTerm, BasicTerm>)_source28)._1;
                  BasicTerm _source29 = _3514___mcc_h51;
                  if (_source29.is_Value) {
                    BigInteger _3516___mcc_h53 = ((BasicTerm_Value)_source29).val;
                    BasicTerm _source30 = _3515___mcc_h52;
                    if (_source30.is_Value) {
                      BigInteger _3517___mcc_h54 = ((BasicTerm_Value)_source30).val;
                      {
                        BigInteger _3518_x2 = _3517___mcc_h54;
                        BigInteger _3519_x1 = _3516___mcc_h53;
                        _3465_b1 = (_3519_x1) == (_3518_x2);
                      }
                    } else {
                      BigInteger _3520___mcc_h55 = ((BasicTerm_StackVar)_source30).id;
                      {
                        BigInteger _3521_x2 = _3520___mcc_h55;
                        BigInteger _3522_x1 = _3516___mcc_h53;
                        {
                          _3465_b1 = false;
                        }
                      }
                    }
                  } else {
                    BigInteger _3523___mcc_h56 = ((BasicTerm_StackVar)_source29).id;
                    BasicTerm _source31 = _3515___mcc_h52;
                    if (_source31.is_Value) {
                      BigInteger _3524___mcc_h57 = ((BasicTerm_Value)_source31).val;
                      {
                        BigInteger _3525_x2 = _3524___mcc_h57;
                        BigInteger _3526_x1 = _3523___mcc_h56;
                        {
                          _3465_b1 = false;
                        }
                      }
                    } else {
                      BigInteger _3527___mcc_h58 = ((BasicTerm_StackVar)_source31).id;
                      {
                        BigInteger _3528_x2 = _3527___mcc_h58;
                        BigInteger _3529_x1 = _3523___mcc_h56;
                        if (((__default.idsFromInput(input1)).Contains((_3529_x1))) && ((__default.idsFromInput(input2)).Contains((_3528_x2)))) {
                          _3465_b1 = (__default.getPos(input1, _3529_x1)) == (__default.getPos(input2, _3528_x2));
                        } else if (((dict1).Contains((_3529_x1))) && ((dict2).Contains((_3528_x2)))) {
                          bool _out4;
                          _out4 = __default.compareDictElems(input1, input2, dict1, dict2, _3529_x1, _3528_x2, Dafny.Set<BigInteger>.Union(prev__ids1, Dafny.Set<BigInteger>.FromElements(key1)), Dafny.Set<BigInteger>.Union(prev__ids2, Dafny.Set<BigInteger>.FromElements(key2)));
                          _3465_b1 = _out4;
                        } else {
                          _3465_b1 = false;
                        }
                      }
                    }
                  }
                }
                b = _3465_b1;
                return b;
              } else {
                b = false;
                return b;
              }
            }
          }
        }
      }
      return b;
    }
    public static bool areEquivalentSFS(ASFS sfs1, ASFS sfs2)
    {
      bool b = false;
      _System.Tuple2<ASFS, ASFS> _source32 = @_System.Tuple2<ASFS, ASFS>.create(sfs1, sfs2);
      {
        ASFS _3530___mcc_h0 = ((_System.Tuple2<ASFS, ASFS>)_source32)._0;
        ASFS _3531___mcc_h1 = ((_System.Tuple2<ASFS, ASFS>)_source32)._1;
        ASFS _source33 = _3530___mcc_h0;
        {
          Dafny.ISequence<BasicTerm> _3532___mcc_h2 = ((ASFS)_source33).input;
          Dafny.IMap<BigInteger,StackElem> _3533___mcc_h3 = ((ASFS)_source33).dict;
          Dafny.ISequence<BasicTerm> _3534___mcc_h4 = ((ASFS)_source33).output;
          ASFS _source34 = _3531___mcc_h1;
          {
            Dafny.ISequence<BasicTerm> _3535___mcc_h5 = ((ASFS)_source34).input;
            Dafny.IMap<BigInteger,StackElem> _3536___mcc_h6 = ((ASFS)_source34).dict;
            Dafny.ISequence<BasicTerm> _3537___mcc_h7 = ((ASFS)_source34).output;
            {
              Dafny.ISequence<BasicTerm> _3538_output2 = _3537___mcc_h7;
              Dafny.IMap<BigInteger,StackElem> _3539_dict2 = _3536___mcc_h6;
              Dafny.ISequence<BasicTerm> _3540_input2 = _3535___mcc_h5;
              Dafny.ISequence<BasicTerm> _3541_output1 = _3534___mcc_h4;
              Dafny.IMap<BigInteger,StackElem> _3542_dict1 = _3533___mcc_h3;
              Dafny.ISequence<BasicTerm> _3543_input1 = _3532___mcc_h2;
              if (((new BigInteger((_3543_input1).Count)) != (new BigInteger((_3540_input2).Count))) || ((new BigInteger((_3541_output1).Count)) != (new BigInteger((_3538_output2).Count)))) {
                b = false;
                return b;
              } else {
                BigInteger _3544_i;
                _3544_i = BigInteger.Zero;
                while ((_3544_i) < (new BigInteger((_3541_output1).Count))) {
                  _System.Tuple2<BasicTerm, BasicTerm> _source35 = @_System.Tuple2<BasicTerm, BasicTerm>.create((_3541_output1).Select(_3544_i), (_3538_output2).Select(_3544_i));
                  {
                    BasicTerm _3545___mcc_h16 = ((_System.Tuple2<BasicTerm, BasicTerm>)_source35)._0;
                    BasicTerm _3546___mcc_h17 = ((_System.Tuple2<BasicTerm, BasicTerm>)_source35)._1;
                    BasicTerm _source36 = _3545___mcc_h16;
                    if (_source36.is_Value) {
                      BigInteger _3547___mcc_h18 = ((BasicTerm_Value)_source36).val;
                      BasicTerm _source37 = _3546___mcc_h17;
                      if (_source37.is_Value) {
                        BigInteger _3548___mcc_h19 = ((BasicTerm_Value)_source37).val;
                        {
                          BigInteger _3549_x2 = _3548___mcc_h19;
                          BigInteger _3550_x1 = _3547___mcc_h18;
                          if ((_3550_x1) != (_3549_x2)) {
                            b = false;
                            return b;
                          }
                        }
                      } else {
                        BigInteger _3551___mcc_h20 = ((BasicTerm_StackVar)_source37).id;
                        {
                          BigInteger _3552_x2 = _3551___mcc_h20;
                          BigInteger _3553_x1 = _3547___mcc_h18;
                          b = false;
                          return b;
                        }
                      }
                    } else {
                      BigInteger _3554___mcc_h21 = ((BasicTerm_StackVar)_source36).id;
                      BasicTerm _source38 = _3546___mcc_h17;
                      if (_source38.is_Value) {
                        BigInteger _3555___mcc_h22 = ((BasicTerm_Value)_source38).val;
                        {
                          BigInteger _3556_x2 = _3555___mcc_h22;
                          BigInteger _3557_x1 = _3554___mcc_h21;
                          b = false;
                          return b;
                        }
                      } else {
                        BigInteger _3558___mcc_h23 = ((BasicTerm_StackVar)_source38).id;
                        {
                          BigInteger _3559_x2 = _3558___mcc_h23;
                          BigInteger _3560_x1 = _3554___mcc_h21;
                          if (((__default.idsFromInput(_3543_input1)).Contains((_3560_x1))) && ((__default.idsFromInput(_3540_input2)).Contains((_3559_x2)))) {
                            if ((__default.getPos(_3543_input1, _3560_x1)) != (__default.getPos(_3540_input2, _3559_x2))) {
                              b = false;
                              return b;
                            }
                          } else if (((_3542_dict1).Contains((_3560_x1))) && ((_3539_dict2).Contains((_3559_x2)))) {
                            bool _3561_aux;
                            bool _out5;
                            _out5 = __default.compareDictElems(_3543_input1, _3540_input2, _3542_dict1, _3539_dict2, _3560_x1, _3559_x2, Dafny.Set<BigInteger>.FromElements(), Dafny.Set<BigInteger>.FromElements());
                            _3561_aux = _out5;
                            if (!(_3561_aux)) {
                              b = false;
                              return b;
                            }
                          } else {
                            b = false;
                            return b;
                          }
                        }
                      }
                    }
                  }
                  _3544_i = (_3544_i) + (BigInteger.One);
                }
                b = true;
                return b;
              }
            }
          }
        }
      }
      return b;
    }
  }
} // end of namespace _module
