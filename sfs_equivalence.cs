// Dafny program sfs_equivalence.dfy compiled into C#
// To recompile, use 'csc' with: /r:System.Numerics.dll
// and choosing /target:exe or /target:library
// You might also want to include compiler switches like:
//     /debug /nowarn:0164 /nowarn:0219 /nowarn:1717 /nowarn:0162 /nowarn:0168

using System;
using System.Numerics;
[assembly: DafnyAssembly.DafnySourceAttribute(@"
// Dafny 2.3.0.10506
// Command Line Options: /compile:2 /spillTargetCode:1 sfs_equivalence.dfy
// sfs_equivalence.dfy

datatype BasicTerm = Value(val: int) | StackVar(id: int)

datatype StackElem = Op(id: int, input_stack: seq<BasicTerm>) | COp(id: int, elem1: BasicTerm, elem2: BasicTerm)

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
    match input[0] { case Value(val) => idsFromInput(input[1..]) case StackVar(id) => {id} + idsFromInput(input[1..]) }
}

predicate allVarsAreStackVar(input: seq<BasicTerm>)
  decreases input
{
  if input == [] then
    true
  else
    match input[0] { case Value(val) => false case StackVar(id) => allVarsAreStackVar(input[1..]) }
}

predicate noRepeatedStackVar(input: seq<BasicTerm>, previously_ids: set<int>)
  decreases input
{
  if input == [] then
    true
  else
    match input[0] { case Value(val) => false case StackVar(id) => id !in previously_ids && noRepeatedStackVar(input[1..], previously_ids + {id}) }
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
  ensures match input[pos] { case Value(x) => false case StackVar(x) => x == id }
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
      match dict[key] case Op(id, l) => id == key && (forall i :: 0 <= i < |l| ==> match l[i] { case Value(x) => true case StackVar(id2) => id2 in idsFromInput(inputStack) || id2 in dict }) case COp(id, x1, x2) => id == key && match x1 { case Value(x) => true case StackVar(id2) => id2 in idsFromInput(inputStack) || id2 in dict } && match x2 { case Value(x) => true case StackVar(id2) => id2 in idsFromInput(inputStack) || id2 in dict }
}

predicate dictElementConverges(inputStack: seq<BasicTerm>, dict: map<int, StackElem>, key: int, previously_ids: set<int>)
  requires previously_ids <= dict.Keys
  requires key in dict
  requires idsInDictAreWellDelimited(inputStack, dict)
  decreases dict.Keys - previously_ids
{
  match dict[key]
  case Op(id, l) =>
    id !in previously_ids &&
    forall i :: 
      0 <= i < |l| ==>
        match l[i] { case Value(x) => true case StackVar(x1) => if x1 in idsFromInput(inputStack) then true else dictElementConverges(inputStack, dict, x1, previously_ids + {id}) }
  case COp(id, el1, el2) =>
    id !in previously_ids &&
    match el1 { case Value(x) => true case StackVar(x1) => (if x1 in idsFromInput(inputStack) then true else dictElementConverges(inputStack, dict, x1, previously_ids + {id})) } &&
    match el2 { case Value(x) => true case StackVar(x1) => if x1 in idsFromInput(inputStack) then true else dictElementConverges(inputStack, dict, x1, previously_ids + {id}) }
}

predicate dictIsWellDefined(inputStack: seq<BasicTerm>, dict: map<int, StackElem>)
  decreases inputStack, dict
{
  dict.Keys * idsFromInput(inputStack) == {} &&
  idsInDictAreWellDelimited(inputStack, dict) &&
  forall key: int :: 
    key in dict ==>
      dictElementConverges(inputStack, dict, key, {})
}

predicate outputIsWellDefined(inputStack: seq<BasicTerm>, dict: map<int, StackElem>, output: seq<BasicTerm>)
  decreases inputStack, dict, output
{
  forall elem: BasicTerm :: 
    elem in output ==>
      match elem { case Value(x) => true case StackVar(id) => id in dict || id in idsFromInput(inputStack) }
}

predicate isSFS(sfs: ASFS)
  decreases sfs
{
  match sfs
  case SFS(input, dict, output) =>
    initialInputIsWellDefined(input) &&
    dictIsWellDefined(input, dict) &&
    outputIsWellDefined(input, dict, output)
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
  case (Op(id1, l1), Op(id2, l2)) =>
    |l1| == |l2| &&
    forall i :: 
      0 <= i < |l1| ==>
        match (l1[i], l2[i]) { case (Value(x1), Value(x2)) => x1 == x2 case (StackVar(x1), StackVar(x2)) => (if x1 in idsFromInput(input1) && x2 in idsFromInput(input2) then getPos(input1, x1) == getPos(input2, x2) else if x1 in dict1 && x2 in dict2 then compareStackElem(input1, input2, dict1, dict2, x1, x2, prev_ids1 + {key1}, prev_ids2 + {key2}) else false) case (Value(x1), StackVar(x2)) => false case (StackVar(x1), Value(x2)) => false }
  case (COp(id1, el11, el12), COp(id2, el21, el22)) =>
    (match (el11, el21) { case (Value(x1), Value(x2)) => x1 == x2 case (StackVar(x1), StackVar(x2)) => (if x1 in idsFromInput(input1) && x2 in idsFromInput(input2) then getPos(input1, x1) == getPos(input2, x2) else if x1 in dict1 && x2 in dict2 then compareStackElem(input1, input2, dict1, dict2, x1, x2, prev_ids1 + {key1}, prev_ids2 + {key2}) else false) case (Value(x1), StackVar(x2)) => false case (StackVar(x1), Value(x2)) => false } && match (el12, el22) { case (Value(x1), Value(x2)) => x1 == x2 case (StackVar(x1), StackVar(x2)) => (if x1 in idsFromInput(input1) && x2 in idsFromInput(input2) then getPos(input1, x1) == getPos(input2, x2) else if x1 in dict1 && x2 in dict2 then compareStackElem(input1, input2, dict1, dict2, x1, x2, prev_ids1 + {key1}, prev_ids2 + {key2}) else false) case (Value(x1), StackVar(x2)) => false case (StackVar(x1), Value(x2)) => false }) || (match (el11, el22) { case (Value(x1), Value(x2)) => x1 == x2 case (StackVar(x1), StackVar(x2)) => (if x1 in idsFromInput(input1) && x2 in idsFromInput(input2) then getPos(input1, x1) == getPos(input2, x2) else if x1 in dict1 && x2 in dict2 then compareStackElem(input1, input2, dict1, dict2, x1, x2, prev_ids1 + {key1}, prev_ids2 + {key2}) else false) case (Value(x1), StackVar(x2)) => false case (StackVar(x1), Value(x2)) => false } && match (el12, el21) { case (Value(x1), Value(x2)) => x1 == x2 case (StackVar(x1), StackVar(x2)) => (if x1 in idsFromInput(input1) && x2 in idsFromInput(input2) then getPos(input1, x1) == getPos(input2, x2) else if x1 in dict1 && x2 in dict2 then compareStackElem(input1, input2, dict1, dict2, x1, x2, prev_ids1 + {key1}, prev_ids2 + {key2}) else false) case (Value(x1), StackVar(x2)) => false case (StackVar(x1), Value(x2)) => false })
  case (COp(id1, x1, y1), Op(id2, l2)) =>
    false
  case (Op(id1, l1), COp(id2, x2, y2)) =>
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
        match (output1[i], output2[i]) { case (Value(x1), Value(x2)) => x1 == x2 case (StackVar(x1), StackVar(x2)) => (if x1 in idsFromInput(input1) && x2 in idsFromInput(input2) then getPos(input1, x1) == getPos(input2, x2) else if x1 in dict1 && x2 in dict2 then compareStackElem(input1, input2, dict1, dict2, x1, x2, {}, {}) else false) case (StackVar(x1), Value(x2)) => false case (Value(x1), StackVar(x2)) => false }
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
  case (Op(id1, l1), Op(id2, l2)) =>
    if |l1| != |l2| {
      return false;
    } else {
      var i := 0;
      while i < |l1|
        invariant 0 <= i <= |l1|
        invariant forall j :: 0 <= j < i ==> match (l1[j], l2[j]) { case (Value(x1), Value(x2)) => x1 == x2 case (StackVar(x1), StackVar(x2)) => (if x1 in idsFromInput(input1) && x2 in idsFromInput(input2) then getPos(input1, x1) == getPos(input2, x2) else if x1 in dict1 && x2 in dict2 then compareStackElem(input1, input2, dict1, dict2, x1, x2, prev_ids1 + {key1}, prev_ids2 + {key2}) else false) case (Value(x1), StackVar(x2)) => false case (StackVar(x1), Value(x2)) => false }
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
  case (COp(id1, el11, el12), COp(id2, el21, el22)) =>
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
  case (COp(id1, x1, y1), Op(id2, l2)) =>
    return false;
  case (Op(id1, l1), COp(id2, x2, y2)) =>
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
        invariant forall j :: 0 <= j < i ==> match (output1[j], output2[j]) { case (Value(x1), Value(x2)) => x1 == x2 case (StackVar(x1), StackVar(x2)) => (if x1 in idsFromInput(input1) && x2 in idsFromInput(input2) then getPos(input1, x1) == getPos(input2, x2) else if x1 in dict1 && x2 in dict2 then compareStackElem(input1, input2, dict1, dict2, x1, x2, {}, {}) else false) case (StackVar(x1), Value(x2)) => false case (Value(x1), StackVar(x2)) => false }
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
  // set this option if you want to use System.Collections.Immutable and if you know what you're doing.
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
  using System.Collections.Immutable;
  using System.Linq;
#endif

  public class Set<T>
  {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    readonly ImmutableHashSet<T> setImpl;
    readonly bool containsNull;
    Set(ImmutableHashSet<T> d, bool containsNull) {
      this.setImpl = d;
      this.containsNull = containsNull;
    }
    public static readonly Set<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty, false);
    public static Set<T> FromElements(params T[] values) {
      return FromCollection(values);
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
    public static Set<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
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
#else
    readonly HashSet<T> setImpl;
    Set(HashSet<T> s) {
      this.setImpl = s;
    }
    public static readonly Set<T> Empty = new Set<T>(new HashSet<T>());
    public static Set<T> FromElements(params T[] values) {
      return FromCollection(values);
    }
    public static Set<T> FromCollection(IEnumerable<T> values) {
      var s = new HashSet<T>(values);
      return new Set<T>(s);
    }
    public static Set<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var s = new HashSet<T>(values);
      s.Add(oneMoreValue);
      return new Set<T>(s);
    }
    public int Count {
      get { return this.setImpl.Count; }
    }
    public long LongCount {
      get { return this.setImpl.Count; }
    }
    public IEnumerable<T> Elements {
      get {
        return this.setImpl;
      }
    }
#endif

    public static Set<T> _DafnyDefaultValue() {
      return Empty;
    }

    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".
    /// </summary>
    public IEnumerable<Set<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list, but don't include null
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
#else
        var s = new HashSet<T>();
#endif
        while (true) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
          // yield both the subset without null and, if null is in the original set, the subset with null included
          var ihs = s.ToImmutable();
          yield return new Set<T>(ihs, false);
          if (containsNull) {
            yield return new Set<T>(ihs, true);
          }
#else
          yield return new Set<T>(new HashSet<T>(s));
#endif
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
    public bool Equals(Set<T> other) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      return containsNull == other.containsNull && this.setImpl.SetEquals(other.setImpl);
#else
      return this.setImpl.Count == other.setImpl.Count && IsSubsetOf(other);
#endif
    }
    public override bool Equals(object other) {
      return other is Set<T> && Equals((Set<T>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      if (containsNull) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(default(T)) + 3);
      }
#endif
      foreach (var t in this.setImpl) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(t)+3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "{";
      var sep = "";
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      if (containsNull) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
#endif
      foreach (var t in this.setImpl) {
        s += sep + Dafny.Helpers.ToString(t);
        sep = ", ";
      }
      return s + "}";
    }
    public bool IsProperSubsetOf(Set<T> other) {
      return this.Count < other.Count && IsSubsetOf(other);
    }
    public bool IsSubsetOf(Set<T> other) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      if (this.containsNull && !other.containsNull) {
        return false;
      }
#endif
      if (other.setImpl.Count < this.setImpl.Count)
        return false;
      foreach (T t in this.setImpl) {
        if (!other.setImpl.Contains(t))
          return false;
      }
      return true;
    }
    public bool IsSupersetOf(Set<T> other) {
      return other.IsSubsetOf(this);
    }
    public bool IsProperSupersetOf(Set<T> other) {
      return other.IsProperSubsetOf(this);
    }
    public bool IsDisjointFrom(Set<T> other) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      if (this.containsNull && other.containsNull) {
        return false;
      }
      ImmutableHashSet<T> a, b;
#else
      HashSet<T> a, b;
#endif
      if (this.setImpl.Count < other.setImpl.Count) {
        a = this.setImpl; b = other.setImpl;
      } else {
        a = other.setImpl; b = this.setImpl;
      }
      foreach (T t in a) {
        if (b.Contains(t))
          return false;
      }
      return true;
    }
    public bool Contains<G>(G t) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      return t == null ? containsNull : t is T && this.setImpl.Contains((T)(object)t);
#else
      return (t == null || t is T) && this.setImpl.Contains((T)(object)t);
#endif
    }
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    public Set<T> Union(Set<T> other) {
      return new Set<T>(this.setImpl.Union(other.setImpl), containsNull || other.containsNull);
    }
    public Set<T> Intersect(Set<T> other) {
      return new Set<T>(this.setImpl.Intersect(other.setImpl), containsNull && other.containsNull);
    }
    public Set<T> Difference(Set<T> other) {
        return new Set<T>(this.setImpl.Except(other.setImpl), containsNull && !other.containsNull);
    }
#else
    public Set<T> Union(Set<T> other) {
      if (this.setImpl.Count == 0)
        return other;
      else if (other.setImpl.Count == 0)
        return this;
      HashSet<T> a, b;
      if (this.setImpl.Count < other.setImpl.Count) {
        a = this.setImpl; b = other.setImpl;
      } else {
        a = other.setImpl; b = this.setImpl;
      }
      var r = new HashSet<T>();
      foreach (T t in b)
        r.Add(t);
      foreach (T t in a)
        r.Add(t);
      return new Set<T>(r);
    }
    public Set<T> Intersect(Set<T> other) {
      if (this.setImpl.Count == 0)
        return this;
      else if (other.setImpl.Count == 0)
        return other;
      HashSet<T> a, b;
      if (this.setImpl.Count < other.setImpl.Count) {
        a = this.setImpl; b = other.setImpl;
      } else {
        a = other.setImpl; b = this.setImpl;
      }
      var r = new HashSet<T>();
      foreach (T t in a) {
        if (b.Contains(t))
          r.Add(t);
      }
      return new Set<T>(r);
    }
    public Set<T> Difference(Set<T> other) {
      if (this.setImpl.Count == 0)
        return this;
      else if (other.setImpl.Count == 0)
        return this;
      var r = new HashSet<T>();
      foreach (T t in this.setImpl) {
        if (!other.setImpl.Contains(t))
          r.Add(t);
      }
      return new Set<T>(r);
    }
#endif
  }

  public class MultiSet<T>
  {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    readonly ImmutableDictionary<T, int> dict;
#else
    readonly Dictionary<T, int> dict;
#endif
    readonly BigInteger occurrencesOfNull;  // stupidly, a Dictionary in .NET cannot use "null" as a key
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    MultiSet(ImmutableDictionary<T, int>.Builder d, BigInteger occurrencesOfNull) {
      dict = d.ToImmutable();
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, int>.Empty.ToBuilder(), BigInteger.Zero);
#else
    MultiSet(Dictionary<T, int> d, BigInteger occurrencesOfNull) {
      this.dict = d;
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static MultiSet<T> Empty = new MultiSet<T>(new Dictionary<T, int>(0), BigInteger.Zero);
#endif
    public static MultiSet<T> FromElements(params T[] values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var d = new Dictionary<T, int>(values.Length);
#endif
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          var i = 0;
          if (!d.TryGetValue(t, out i)) {
            i = 0;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }
    public static MultiSet<T> FromCollection(ICollection<T> values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var d = new Dictionary<T, int>();
#endif
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          var i = 0;
          if (!d.TryGetValue(t, out i)) {
            i = 0;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }
    public static MultiSet<T> FromSeq(Sequence<T> values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var d = new Dictionary<T, int>();
#endif
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values.Elements) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          var i = 0;
          if (!d.TryGetValue(t, out i)) {
            i = 0;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }
    public static MultiSet<T> FromSet(Set<T> values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var d = new Dictionary<T, int>();
#endif
      var containsNull = false;
      foreach (T t in values.Elements) {
        if (t == null) {
          containsNull = true;
        } else {
          d[t] = 1;
        }
      }
      return new MultiSet<T>(d, containsNull ? BigInteger.One : BigInteger.Zero);
    }

    public static MultiSet<T> _DafnyDefaultValue() {
      return Empty;
    }

    public bool Equals(MultiSet<T> other) {
      return other.IsSubsetOf(this) && this.IsSubsetOf(other);
    }
    public override bool Equals(object other) {
      return other is MultiSet<T> && Equals((MultiSet<T>)other);
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
        for (int i = 0; i < kv.Value; i++) {
          s += sep + t;
          sep = ", ";
        }
      }
      return s + "}";
    }
    public bool IsProperSubsetOf(MultiSet<T> other) {
      return !Equals(other) && IsSubsetOf(other);
    }
    public bool IsSubsetOf(MultiSet<T> other) {
      if (other.occurrencesOfNull < this.occurrencesOfNull) {
        return false;
      }
      foreach (T t in dict.Keys) {
        if (!other.dict.ContainsKey(t) || other.dict[t] < dict[t])
          return false;
      }
      return true;
    }
    public bool IsSupersetOf(MultiSet<T> other) {
      return other.IsSubsetOf(this);
    }
    public bool IsProperSupersetOf(MultiSet<T> other) {
      return other.IsProperSubsetOf(this);
    }
    public bool IsDisjointFrom(MultiSet<T> other) {
      if (occurrencesOfNull > 0 && other.occurrencesOfNull > 0) {
        return false;
      }
      foreach (T t in dict.Keys) {
        if (other.dict.ContainsKey(t))
          return false;
      }
      foreach (T t in other.dict.Keys) {
        if (dict.ContainsKey(t))
          return false;
      }
      return true;
    }

    public bool Contains<G>(G t) {
      return t == null ? occurrencesOfNull > 0 : t is T && dict.ContainsKey((T)(object)t);
    }
    public BigInteger Select<G>(G t) {
      if (t == null) {
        return occurrencesOfNull;
      } else if (t is T && dict.ContainsKey((T)(object)t)) {
        return dict[(T)(object)t];
      } else {
        return BigInteger.Zero;
      }
    }
    public MultiSet<T> Update<G>(G t, BigInteger i) {
      if (Select(t) == i) {
        return this;
      } else if (t == null) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
        var r = dict.ToBuilder();
#else
        var r = dict;
#endif
        return new MultiSet<T>(r, i);
      } else {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
        var r = dict.ToBuilder();
#else
        var r = new Dictionary<T, int>(dict);
#endif
        r[(T)(object)t] = (int)i;
        return new MultiSet<T>(r, occurrencesOfNull);
      }
    }
    public MultiSet<T> Union(MultiSet<T> other) {
      if (dict.Count + occurrencesOfNull == 0)
        return other;
      else if (other.dict.Count + other.occurrencesOfNull == 0)
        return this;
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var r = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var r = new Dictionary<T, int>();
#endif
      foreach (T t in dict.Keys) {
        var i = 0;
        if (!r.TryGetValue(t, out i)) {
          i = 0;
        }
        r[t] = i + dict[t];
      }
      foreach (T t in other.dict.Keys) {
        var i = 0;
        if (!r.TryGetValue(t, out i)) {
          i = 0;
        }
        r[t] = i + other.dict[t];
      }
      return new MultiSet<T>(r, occurrencesOfNull + other.occurrencesOfNull);
    }
    public MultiSet<T> Intersect(MultiSet<T> other) {
      if (dict.Count == 0 && occurrencesOfNull == 0)
        return this;
      else if (other.dict.Count == 0 && other.occurrencesOfNull == 0)
        return other;
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var r = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var r = new Dictionary<T, int>();
#endif
      foreach (T t in dict.Keys) {
        if (other.dict.ContainsKey(t)) {
          r.Add(t, other.dict[t] < dict[t] ? other.dict[t] : dict[t]);
        }
      }
      return new MultiSet<T>(r, other.occurrencesOfNull < occurrencesOfNull ? other.occurrencesOfNull : occurrencesOfNull);
    }
    public MultiSet<T> Difference(MultiSet<T> other) { // \result == this - other
      if (dict.Count == 0 && occurrencesOfNull == 0)
        return this;
      else if (other.dict.Count == 0 && other.occurrencesOfNull == 0)
        return this;
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var r = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var r = new Dictionary<T, int>();
#endif
      foreach (T t in dict.Keys) {
        if (!other.dict.ContainsKey(t)) {
          r.Add(t, dict[t]);
        } else if (other.dict[t] < dict[t]) {
          r.Add(t, dict[t] - other.dict[t]);
        }
      }
      return new MultiSet<T>(r, other.occurrencesOfNull < occurrencesOfNull ? occurrencesOfNull - other.occurrencesOfNull : BigInteger.Zero);
    }

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
          for (int i = 0; i < item.Value; i++) {
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
        foreach (var item in dict) {
          yield return item.Key;
        }
      }
    }
  }

  public class Map<U, V>
  {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    readonly ImmutableDictionary<U, V> dict;
#else
    readonly Dictionary<U, V> dict;
#endif
    readonly bool hasNullValue;  // true when "null" is a key of the Map
    readonly V nullValue;  // if "hasNullValue", the value that "null" maps to

#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    Map(ImmutableDictionary<U, V>.Builder d, bool hasNullValue, V nullValue) {
      dict = d.ToImmutable();
      this.hasNullValue = hasNullValue;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty.ToBuilder(), false, default(V));
#else
    Map(Dictionary<U, V> d, bool hasNullValue, V nullValue) {
      this.dict = d;
      this.hasNullValue = hasNullValue;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(new Dictionary<U, V>(), false, default(V));
#endif

    public static Map<U, V> FromElements(params Pair<U, V>[] values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
#else
      var d = new Dictionary<U, V>(values.Length);
#endif
      var hasNullValue = false;
      var nullValue = default(V);
      foreach (Pair<U, V> p in values) {
        if (p.Car == null) {
          hasNullValue = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullValue, nullValue);
    }
    public static Map<U, V> FromCollection(List<Pair<U, V>> values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
#else
      var d = new Dictionary<U, V>(values.Count);
#endif
      var hasNullValue = false;
      var nullValue = default(V);
      foreach (Pair<U, V> p in values) {
        if (p.Car == null) {
          hasNullValue = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullValue, nullValue);
    }
    public int Count {
      get { return dict.Count + (hasNullValue ? 1 : 0); }
    }
    public long LongCount {
      get { return dict.Count + (hasNullValue ? 1 : 0); }
    }
    public static Map<U, V> _DafnyDefaultValue() {
      return Empty;
    }

    public bool Equals(Map<U, V> other) {
      if (hasNullValue != other.hasNullValue || dict.Count != other.dict.Count) {
        return false;
      } else if (hasNullValue && !Dafny.Helpers.AreEqual(nullValue, other.nullValue)) {
        return false;
      }
      foreach (U u in dict.Keys) {
        V v1 = dict[u];
        V v2;
        if (!other.dict.TryGetValue(u, out v2)) {
          return false; // other dictionary does not contain this element
        }
        if (!Dafny.Helpers.AreEqual(v1, v2)) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      return other is Map<U, V> && Equals((Map<U, V>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      if (hasNullValue) {
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
      if (hasNullValue) {
        s += sep + Dafny.Helpers.ToString(default(U)) + " := " + Dafny.Helpers.ToString(nullValue);
        sep = ", ";
      }
      foreach (var kv in dict) {
        s += sep + Dafny.Helpers.ToString(kv.Key) + " := " + Dafny.Helpers.ToString(kv.Value);
        sep = ", ";
      }
      return s + "]";
    }
    public bool IsDisjointFrom(Map<U, V> other) {
      if (hasNullValue && other.hasNullValue) {
        return false;
      }
      foreach (U u in dict.Keys) {
        if (other.dict.ContainsKey(u))
          return false;
      }
      foreach (U u in other.dict.Keys) {
        if (dict.ContainsKey(u))
          return false;
      }
      return true;
    }
    public bool Contains<G>(G u) {
      return u == null ? hasNullValue : u is U && dict.ContainsKey((U)(object)u);
    }
    public V Select(U index) {
      // evidently, the following will throw some exception if "index" in not a key of the map
      return index == null && hasNullValue ? nullValue : dict[index];
    }
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    public Map<U, V> Update(U index, V val) {
      var d = dict.ToBuilder();
      if (index == null) {
        return new Map<U, V>(d, true, val);
      } else {
        d[index] = val;
        return new Map<U, V>(d, hasNullValue, nullValue);
      }
    }
#else
    public Map<U, V> Update(U index, V val) {
      if (index == null) {
        return new Map<U, V>(dict, true, val);
      } else {
        var d = new Dictionary<U, V>(dict);
        d[index] = val;
        return new Map<U, V>(d, hasNullValue, nullValue);
      }
    }
#endif
    public Set<U> Keys {
      get {
        if (hasNullValue) {
          return Dafny.Set<U>.FromCollectionPlusOne(dict.Keys, default(U));
        } else {
          return Dafny.Set<U>.FromCollection(dict.Keys);
        }
      }
    }
    public Set<V> Values {
      get {
        if (hasNullValue) {
          return Dafny.Set<V>.FromCollectionPlusOne(dict.Values, nullValue);
        } else {
          return Dafny.Set<V>.FromCollection(dict.Values);
        }
      }
    }
    public Set<_System.Tuple2<U, V>> Items {
      get {
        HashSet<_System.Tuple2<U, V>> result = new HashSet<_System.Tuple2<U, V>>();
        if (hasNullValue) {
          result.Add(_System.Tuple2<U, V>.create(default(U), nullValue));
        }
        foreach (KeyValuePair<U, V> kvp in dict) {
          result.Add(_System.Tuple2<U, V>.create(kvp.Key, kvp.Value));
        }
        return Dafny.Set<_System.Tuple2<U, V>>.FromCollection(result);
      }
    }
  }

  public class Sequence<T>
  {
    readonly T[] elmts;
    public Sequence(T[] ee) {
      elmts = ee;
    }
    public static Sequence<T> Empty {
      get {
        return new Sequence<T>(new T[0]);
      }
    }
    public static Sequence<T> FromElements(params T[] values) {
      return new Sequence<T>(values);
    }
    public static Sequence<char> FromString(string s) {
      return new Sequence<char>(s.ToCharArray());
    }
    public static Sequence<T> _DafnyDefaultValue() {
      return Empty;
    }
    public int Count {
      get { return elmts.Length; }
    }
    public long LongCount {
      get { return elmts.LongLength; }
    }
    public T[] Elements {
      get {
        return elmts;
      }
    }
    public IEnumerable<T> UniqueElements {
      get {
        var st = Set<T>.FromElements(elmts);
        return st.Elements;
      }
    }
    public T Select(ulong index) {
      return elmts[index];
    }
    public T Select(long index) {
      return elmts[index];
    }
    public T Select(uint index) {
      return elmts[index];
    }
    public T Select(int index) {
      return elmts[index];
    }
    public T Select(BigInteger index) {
      return elmts[(int)index];
    }
    public Sequence<T> Update(long index, T t) {
      T[] a = (T[])elmts.Clone();
      a[index] = t;
      return new Sequence<T>(a);
    }
    public Sequence<T> Update(ulong index, T t) {
      return Update((long)index, t);
    }
    public Sequence<T> Update(BigInteger index, T t) {
      return Update((long)index, t);
    }
    public bool Equals(Sequence<T> other) {
      int n = elmts.Length;
      return n == other.elmts.Length && EqualUntil(other, n);
    }
    public override bool Equals(object other) {
      return other is Sequence<T> && Equals((Sequence<T>)other);
    }
    public override int GetHashCode() {
      if (elmts == null || elmts.Length == 0)
        return 0;
      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ Dafny.Helpers.GetHashCode(elmts[i]);
      }
      return hashCode;
    }
    public override string ToString() {
      if (elmts is char[]) {
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
    bool EqualUntil(Sequence<T> other, int n) {
      for (int i = 0; i < n; i++) {
        if (!Dafny.Helpers.AreEqual(elmts[i], other.elmts[i]))
          return false;
      }
      return true;
    }
    public bool IsProperPrefixOf(Sequence<T> other) {
      int n = elmts.Length;
      return n < other.elmts.Length && EqualUntil(other, n);
    }
    public bool IsPrefixOf(Sequence<T> other) {
      int n = elmts.Length;
      return n <= other.elmts.Length && EqualUntil(other, n);
    }
    public Sequence<T> Concat(Sequence<T> other) {
      if (elmts.Length == 0)
        return other;
      else if (other.elmts.Length == 0)
        return this;
      T[] a = new T[elmts.Length + other.elmts.Length];
      System.Array.Copy(elmts, 0, a, 0, elmts.Length);
      System.Array.Copy(other.elmts, 0, a, elmts.Length, other.elmts.Length);
      return new Sequence<T>(a);
    }
    public bool Contains<G>(G g) {
      if (g == null || g is T) {
        var t = (T)(object)g;
        int n = elmts.Length;
        for (int i = 0; i < n; i++) {
          if (Dafny.Helpers.AreEqual(t, elmts[i]))
            return true;
        }
      }
      return false;
    }
    public Sequence<T> Take(long m) {
      if (elmts.LongLength == m)
        return this;
      T[] a = new T[m];
      System.Array.Copy(elmts, a, m);
      return new Sequence<T>(a);
    }
    public Sequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public Sequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public Sequence<T> Drop(long m) {
      if (m == 0)
        return this;
      T[] a = new T[elmts.Length - m];
      System.Array.Copy(elmts, m, a, 0, elmts.Length - m);
      return new Sequence<T>(a);
    }
    public Sequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public Sequence<T> Drop(BigInteger n) {
      if (n.IsZero)
        return this;
      return Drop((long)n);
    }
  }
  public struct Pair<A, B>
  {
    public readonly A Car;
    public readonly B Cdr;
    public Pair(A a, B b) {
      this.Car = a;
      this.Cdr = b;
    }
  }
  public partial class Helpers {
    public static bool AreEqual<G>(G a, G b) {
      return a == null ? b == null : a.Equals(b);
    }
    public static int GetHashCode<G>(G g) {
      return g == null ? 1001 : g.GetHashCode();
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
    public static G Default<G>() {
      System.Type ty = typeof(G);
      System.Reflection.MethodInfo mInfo = ty.GetMethod("_DafnyDefaultValue");
      if (mInfo != null) {
        G g = (G)mInfo.Invoke(null, null);
        return g;
      } else {
        return default(G);
      }
    }
    // Computing forall/exists quantifiers
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
    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new Sequence<T>((T[])array.Clone());
    }
    // In .NET version 4.5, it it possible to mark a method with "AggressiveInlining", which says to inline the
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
      var oth = other as _System.@Tuple2<T0,T1>;
      return oth != null && Dafny.Helpers.AreEqual(this._0, oth._0) && Dafny.Helpers.AreEqual(this._1, oth._1);
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
    static Tuple2<T0,T1> theDefault;
    public static Tuple2<T0,T1> Default {
      get {
        if (theDefault == null) {
          theDefault = new _System.@Tuple2<T0,T1>(Dafny.Helpers.Default<T0>(), Dafny.Helpers.Default<T1>());
        }
        return theDefault;
      }
    }
    public static Tuple2<T0,T1> _DafnyDefaultValue() { return Default; }
    public static Tuple2<T0,T1> create(T0 _0, T1 _1) {
      return new Tuple2<T0,T1>(_0, _1);
    }
    public bool is____hMake3 { get { return true; } }
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
      for (int i0 = 0; i0 < s0; i0++)
        a[i0] = z;
      return a;
    }
  }
} // end of namespace Dafny
namespace _System {


  public partial class nat {
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
    static Tuple0 theDefault;
    public static Tuple0 Default {
      get {
        if (theDefault == null) {
          theDefault = new _System.Tuple0();
        }
        return theDefault;
      }
    }
    public static Tuple0 _DafnyDefaultValue() { return Default; }
    public static Tuple0 create() {
      return new Tuple0();
    }
    public bool is____hMake0 { get { return true; } }
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
    static BasicTerm theDefault;
    public static BasicTerm Default {
      get {
        if (theDefault == null) {
          theDefault = new BasicTerm_Value(BigInteger.Zero);
        }
        return theDefault;
      }
    }
    public static BasicTerm _DafnyDefaultValue() { return Default; }
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
    static StackElem theDefault;
    public static StackElem Default {
      get {
        if (theDefault == null) {
          theDefault = new StackElem_Op(BigInteger.Zero, Dafny.Sequence<BasicTerm>.Empty);
        }
        return theDefault;
      }
    }
    public static StackElem _DafnyDefaultValue() { return Default; }
    public static StackElem create_Op(BigInteger id, Dafny.Sequence<BasicTerm> input__stack) {
      return new StackElem_Op(id, input__stack);
    }
    public static StackElem create_COp(BigInteger id, BasicTerm elem1, BasicTerm elem2) {
      return new StackElem_COp(id, elem1, elem2);
    }
    public bool is_Op { get { return this is StackElem_Op; } }
    public bool is_COp { get { return this is StackElem_COp; } }
    public BigInteger dtor_id {
      get {
        var d = this;
        if (d is StackElem_Op) { return ((StackElem_Op)d).id; }
        return ((StackElem_COp)d).id; 
      }
    }
    public Dafny.Sequence<BasicTerm> dtor_input__stack {
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
    public readonly BigInteger id;
    public readonly Dafny.Sequence<BasicTerm> input__stack;
    public StackElem_Op(BigInteger id, Dafny.Sequence<BasicTerm> input__stack) {
      this.id = id;
      this.input__stack = input__stack;
    }
    public override bool Equals(object other) {
      var oth = other as StackElem_Op;
      return oth != null && this.id == oth.id && Dafny.Helpers.AreEqual(this.input__stack, oth.input__stack);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.input__stack));
      return (int) hash;
    }
    public override string ToString() {
      string s = "StackElem.Op";
      s += "(";
      s += Dafny.Helpers.ToString(this.id);
      s += ", ";
      s += Dafny.Helpers.ToString(this.input__stack);
      s += ")";
      return s;
    }
  }
  public class StackElem_COp : StackElem {
    public readonly BigInteger id;
    public readonly BasicTerm elem1;
    public readonly BasicTerm elem2;
    public StackElem_COp(BigInteger id, BasicTerm elem1, BasicTerm elem2) {
      this.id = id;
      this.elem1 = elem1;
      this.elem2 = elem2;
    }
    public override bool Equals(object other) {
      var oth = other as StackElem_COp;
      return oth != null && this.id == oth.id && Dafny.Helpers.AreEqual(this.elem1, oth.elem1) && Dafny.Helpers.AreEqual(this.elem2, oth.elem2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.elem1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.elem2));
      return (int) hash;
    }
    public override string ToString() {
      string s = "StackElem.COp";
      s += "(";
      s += Dafny.Helpers.ToString(this.id);
      s += ", ";
      s += Dafny.Helpers.ToString(this.elem1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.elem2);
      s += ")";
      return s;
    }
  }

  public class ASFS {
    public readonly Dafny.Sequence<BasicTerm> input;
    public readonly Dafny.Map<BigInteger,StackElem> dict;
    public readonly Dafny.Sequence<BasicTerm> output;
    public ASFS(Dafny.Sequence<BasicTerm> input, Dafny.Map<BigInteger,StackElem> dict, Dafny.Sequence<BasicTerm> output) {
      this.input = input;
      this.dict = dict;
      this.output = output;
    }
    public override bool Equals(object other) {
      var oth = other as ASFS;
      return oth != null && Dafny.Helpers.AreEqual(this.input, oth.input) && Dafny.Helpers.AreEqual(this.dict, oth.dict) && Dafny.Helpers.AreEqual(this.output, oth.output);
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
    static ASFS theDefault;
    public static ASFS Default {
      get {
        if (theDefault == null) {
          theDefault = new ASFS(Dafny.Sequence<BasicTerm>.Empty, Dafny.Map<BigInteger,StackElem>.Empty, Dafny.Sequence<BasicTerm>.Empty);
        }
        return theDefault;
      }
    }
    public static ASFS _DafnyDefaultValue() { return Default; }
    public static ASFS create(Dafny.Sequence<BasicTerm> input, Dafny.Map<BigInteger,StackElem> dict, Dafny.Sequence<BasicTerm> output) {
      return new ASFS(input, dict, output);
    }
    public bool is_SFS { get { return true; } }
    public Dafny.Sequence<BasicTerm> dtor_input {
      get {
        return this.input;
      }
    }
    public Dafny.Map<BigInteger,StackElem> dtor_dict {
      get {
        return this.dict;
      }
    }
    public Dafny.Sequence<BasicTerm> dtor_output {
      get {
        return this.output;
      }
    }
  }

  public partial class __default {
    public static BigInteger getId(BasicTerm el) {
      BasicTerm _source0 = el;
 {
        BigInteger _767_x = ((BasicTerm_StackVar)_source0).id;
        return _767_x;
      }
    }
    public static Dafny.Set<BigInteger> idsFromInput(Dafny.Sequence<BasicTerm> input) {
      if ((input).Equals(Dafny.Sequence<BasicTerm>.FromElements())) {
        return Dafny.Set<BigInteger>.FromElements();
      } else  {
        BasicTerm _source1 = (input).Select(new BigInteger(0));
        if (_source1.is_Value) {
          BigInteger _768_val = ((BasicTerm_Value)_source1).val;
          return __default.idsFromInput((input).Drop(new BigInteger(1)));
        } else  {
          BigInteger _769_id = ((BasicTerm_StackVar)_source1).id;
          return (Dafny.Set<BigInteger>.FromElements(_769_id)).Union(__default.idsFromInput((input).Drop(new BigInteger(1))));
        }
      }
    }
    public static BigInteger atId(Dafny.Sequence<BasicTerm> input, BigInteger pos)
    {
      if ((pos) == (new BigInteger(0))) {
        BasicTerm _source2 = (input).Select(new BigInteger(0));
 {
          BigInteger _770_x = ((BasicTerm_StackVar)_source2).id;
          return _770_x;
        }
      } else  {
        return __default.atId(input, (pos) - (new BigInteger(1)));
      }
    }
    public static BigInteger getPos(Dafny.Sequence<BasicTerm> input, BigInteger id)
    {
      BasicTerm _source3 = (input).Select(new BigInteger(0));
 {
        BigInteger _771_x = ((BasicTerm_StackVar)_source3).id;
        if ((_771_x) == (id)) {
          return new BigInteger(0);
        } else  {
          return (new BigInteger(1)) + (__default.getPos((input).Drop(new BigInteger(1)), id));
        }
      }
    }
    public static void compareDictElems(Dafny.Sequence<BasicTerm> input1, Dafny.Sequence<BasicTerm> input2, Dafny.Map<BigInteger,StackElem> dict1, Dafny.Map<BigInteger,StackElem> dict2, BigInteger key1, BigInteger key2, Dafny.Set<BigInteger> prev__ids1, Dafny.Set<BigInteger> prev__ids2, out bool b)
    {
      b = false;
      _System.Tuple2<StackElem,StackElem> _source4 = @_System.Tuple2<StackElem,StackElem>.create((dict1).Select(key1), (dict2).Select(key2));
 {
        StackElem _772___ms_h0 = ((_System.Tuple2<StackElem,StackElem>)_source4)._0;
        StackElem _773___ms_h1 = ((_System.Tuple2<StackElem,StackElem>)_source4)._1;
        StackElem _source5 = _772___ms_h0;
        if (_source5.is_Op) {
          BigInteger _774_id1 = ((StackElem_Op)_source5).id;
          Dafny.Sequence<BasicTerm> _775_l1 = ((StackElem_Op)_source5).input__stack;
          StackElem _source6 = _773___ms_h1;
          if (_source6.is_Op) {
            BigInteger _776_id2 = ((StackElem_Op)_source6).id;
            Dafny.Sequence<BasicTerm> _777_l2 = ((StackElem_Op)_source6).input__stack;
            if ((new BigInteger((_775_l1).Count)) != (new BigInteger((_777_l2).Count))) {
              b = false;
              return;
            } else {
              BigInteger _778_i;
              _778_i = new BigInteger(0);
              while ((_778_i) < (new BigInteger((_775_l1).Count))) {
                _System.Tuple2<BasicTerm,BasicTerm> _source7 = @_System.Tuple2<BasicTerm,BasicTerm>.create((_775_l1).Select(_778_i), (_777_l2).Select(_778_i));
 {
                  BasicTerm _779___ms_h0 = ((_System.Tuple2<BasicTerm,BasicTerm>)_source7)._0;
                  BasicTerm _780___ms_h1 = ((_System.Tuple2<BasicTerm,BasicTerm>)_source7)._1;
                  BasicTerm _source8 = _779___ms_h0;
                  if (_source8.is_Value) {
                    BigInteger _781_x1 = ((BasicTerm_Value)_source8).val;
                    BasicTerm _source9 = _780___ms_h1;
                    if (_source9.is_Value) {
                      BigInteger _782_x2 = ((BasicTerm_Value)_source9).val;
                      if ((_781_x1) != (_782_x2)) {
                        b = false;
                        return;
                      }
                    } else  {
                      BigInteger _783_x2 = ((BasicTerm_StackVar)_source9).id;
                      b = false;
                      return;
                    }
                  } else  {
                    BigInteger _784_x1 = ((BasicTerm_StackVar)_source8).id;
                    BasicTerm _source10 = _780___ms_h1;
                    if (_source10.is_StackVar) {
                      BigInteger _785_x2 = ((BasicTerm_StackVar)_source10).id;
                      if (((__default.idsFromInput(input1)).Contains(_784_x1)) && ((__default.idsFromInput(input2)).Contains(_785_x2))) {
                        if ((__default.getPos(input1, _784_x1)) != (__default.getPos(input2, _785_x2))) {
                          b = false;
                          return;
                        }
                      } else if (((dict1).Contains(_784_x1)) && ((dict2).Contains(_785_x2))) {
                        bool _786_aux;
                        bool _out0;
                        __default.compareDictElems(input1, input2, dict1, dict2, _784_x1, _785_x2, (prev__ids1).Union(Dafny.Set<BigInteger>.FromElements(key1)), (prev__ids2).Union(Dafny.Set<BigInteger>.FromElements(key2)), out _out0);
                        _786_aux = _out0;
                        if (!(_786_aux)) {
                          b = false;
                          return;
                        }
                      } else {
                        b = false;
                        return;
                      }
                    } else  {
                      BigInteger _787_x2 = ((BasicTerm_Value)_source10).val;
                      b = false;
                      return;
                    }
                  }
                }
                _778_i = (_778_i) + (new BigInteger(1));
              }
              b = true;
              return;
            }
          } else  {
            BigInteger _788_id2 = ((StackElem_COp)_source6).id;
            BasicTerm _789_x2 = ((StackElem_COp)_source6).elem1;
            BasicTerm _790_y2 = ((StackElem_COp)_source6).elem2;
            b = false;
            return;
          }
        } else  {
          BigInteger _791_id1 = ((StackElem_COp)_source5).id;
          BasicTerm _792___mc_h0 = ((StackElem_COp)_source5).elem1;
          BasicTerm _793___mc_h1 = ((StackElem_COp)_source5).elem2;
          StackElem _source11 = _773___ms_h1;
          if (_source11.is_COp) {
            BigInteger _794_id2 = ((StackElem_COp)_source11).id;
            BasicTerm _795_el21 = ((StackElem_COp)_source11).elem1;
            BasicTerm _796_el22 = ((StackElem_COp)_source11).elem2;
            bool _797_b1;
            _797_b1 = true;
            _System.Tuple2<BasicTerm,BasicTerm> _source12 = @_System.Tuple2<BasicTerm,BasicTerm>.create(_792___mc_h0, _795_el21);
 {
              BasicTerm _798___ms_h0 = ((_System.Tuple2<BasicTerm,BasicTerm>)_source12)._0;
              BasicTerm _799___ms_h1 = ((_System.Tuple2<BasicTerm,BasicTerm>)_source12)._1;
              BasicTerm _source13 = _798___ms_h0;
              if (_source13.is_Value) {
                BigInteger _800_x1 = ((BasicTerm_Value)_source13).val;
                BasicTerm _source14 = _799___ms_h1;
                if (_source14.is_Value) {
                  BigInteger _801_x2 = ((BasicTerm_Value)_source14).val;
                  _797_b1 = (_800_x1) == (_801_x2);
                } else  {
                  BigInteger _802_x2 = ((BasicTerm_StackVar)_source14).id;
                  {
                    _797_b1 = false;
                  }
                }
              } else  {
                BigInteger _803_x1 = ((BasicTerm_StackVar)_source13).id;
                BasicTerm _source15 = _799___ms_h1;
                if (_source15.is_StackVar) {
                  BigInteger _804_x2 = ((BasicTerm_StackVar)_source15).id;
                  if (((__default.idsFromInput(input1)).Contains(_803_x1)) && ((__default.idsFromInput(input2)).Contains(_804_x2))) {
                    _797_b1 = (__default.getPos(input1, _803_x1)) == (__default.getPos(input2, _804_x2));
                  } else if (((dict1).Contains(_803_x1)) && ((dict2).Contains(_804_x2))) {
                    bool _out1;
                    __default.compareDictElems(input1, input2, dict1, dict2, _803_x1, _804_x2, (prev__ids1).Union(Dafny.Set<BigInteger>.FromElements(key1)), (prev__ids2).Union(Dafny.Set<BigInteger>.FromElements(key2)), out _out1);
                    _797_b1 = _out1;
                  } else {
                    _797_b1 = false;
                  }
                } else  {
                  BigInteger _805_x2 = ((BasicTerm_Value)_source15).val;
                  {
                    _797_b1 = false;
                  }
                }
              }
            }
            if (_797_b1) {
              _System.Tuple2<BasicTerm,BasicTerm> _source16 = @_System.Tuple2<BasicTerm,BasicTerm>.create(_793___mc_h1, _796_el22);
 {
                BasicTerm _806___ms_h0 = ((_System.Tuple2<BasicTerm,BasicTerm>)_source16)._0;
                BasicTerm _807___ms_h1 = ((_System.Tuple2<BasicTerm,BasicTerm>)_source16)._1;
                BasicTerm _source17 = _806___ms_h0;
                if (_source17.is_Value) {
                  BigInteger _808_x1 = ((BasicTerm_Value)_source17).val;
                  BasicTerm _source18 = _807___ms_h1;
                  if (_source18.is_Value) {
                    BigInteger _809_x2 = ((BasicTerm_Value)_source18).val;
                    _797_b1 = (_808_x1) == (_809_x2);
                  } else  {
                    BigInteger _810_x2 = ((BasicTerm_StackVar)_source18).id;
                    {
                      _797_b1 = false;
                    }
                  }
                } else  {
                  BigInteger _811_x1 = ((BasicTerm_StackVar)_source17).id;
                  BasicTerm _source19 = _807___ms_h1;
                  if (_source19.is_StackVar) {
                    BigInteger _812_x2 = ((BasicTerm_StackVar)_source19).id;
                    if (((__default.idsFromInput(input1)).Contains(_811_x1)) && ((__default.idsFromInput(input2)).Contains(_812_x2))) {
                      _797_b1 = (__default.getPos(input1, _811_x1)) == (__default.getPos(input2, _812_x2));
                    } else if (((dict1).Contains(_811_x1)) && ((dict2).Contains(_812_x2))) {
                      bool _out2;
                      __default.compareDictElems(input1, input2, dict1, dict2, _811_x1, _812_x2, (prev__ids1).Union(Dafny.Set<BigInteger>.FromElements(key1)), (prev__ids2).Union(Dafny.Set<BigInteger>.FromElements(key2)), out _out2);
                      _797_b1 = _out2;
                    } else {
                      _797_b1 = false;
                    }
                  } else  {
                    BigInteger _813_x2 = ((BasicTerm_Value)_source19).val;
                    {
                      _797_b1 = false;
                    }
                  }
                }
              }
              if (_797_b1) {
                b = true;
                return;
              }
            }
            _797_b1 = true;
            _System.Tuple2<BasicTerm,BasicTerm> _source20 = @_System.Tuple2<BasicTerm,BasicTerm>.create(_793___mc_h1, _795_el21);
 {
              BasicTerm _814___ms_h0 = ((_System.Tuple2<BasicTerm,BasicTerm>)_source20)._0;
              BasicTerm _815___ms_h1 = ((_System.Tuple2<BasicTerm,BasicTerm>)_source20)._1;
              BasicTerm _source21 = _814___ms_h0;
              if (_source21.is_Value) {
                BigInteger _816_x1 = ((BasicTerm_Value)_source21).val;
                BasicTerm _source22 = _815___ms_h1;
                if (_source22.is_Value) {
                  BigInteger _817_x2 = ((BasicTerm_Value)_source22).val;
                  _797_b1 = (_816_x1) == (_817_x2);
                } else  {
                  BigInteger _818_x2 = ((BasicTerm_StackVar)_source22).id;
                  {
                    _797_b1 = false;
                  }
                }
              } else  {
                BigInteger _819_x1 = ((BasicTerm_StackVar)_source21).id;
                BasicTerm _source23 = _815___ms_h1;
                if (_source23.is_StackVar) {
                  BigInteger _820_x2 = ((BasicTerm_StackVar)_source23).id;
                  if (((__default.idsFromInput(input1)).Contains(_819_x1)) && ((__default.idsFromInput(input2)).Contains(_820_x2))) {
                    _797_b1 = (__default.getPos(input1, _819_x1)) == (__default.getPos(input2, _820_x2));
                  } else if (((dict1).Contains(_819_x1)) && ((dict2).Contains(_820_x2))) {
                    bool _out3;
                    __default.compareDictElems(input1, input2, dict1, dict2, _819_x1, _820_x2, (prev__ids1).Union(Dafny.Set<BigInteger>.FromElements(key1)), (prev__ids2).Union(Dafny.Set<BigInteger>.FromElements(key2)), out _out3);
                    _797_b1 = _out3;
                  } else {
                    _797_b1 = false;
                  }
                } else  {
                  BigInteger _821_x2 = ((BasicTerm_Value)_source23).val;
                  {
                    _797_b1 = false;
                  }
                }
              }
            }
            if (_797_b1) {
              _System.Tuple2<BasicTerm,BasicTerm> _source24 = @_System.Tuple2<BasicTerm,BasicTerm>.create(_792___mc_h0, _796_el22);
 {
                BasicTerm _822___ms_h0 = ((_System.Tuple2<BasicTerm,BasicTerm>)_source24)._0;
                BasicTerm _823___ms_h1 = ((_System.Tuple2<BasicTerm,BasicTerm>)_source24)._1;
                BasicTerm _source25 = _822___ms_h0;
                if (_source25.is_Value) {
                  BigInteger _824_x1 = ((BasicTerm_Value)_source25).val;
                  BasicTerm _source26 = _823___ms_h1;
                  if (_source26.is_Value) {
                    BigInteger _825_x2 = ((BasicTerm_Value)_source26).val;
                    _797_b1 = (_824_x1) == (_825_x2);
                  } else  {
                    BigInteger _826_x2 = ((BasicTerm_StackVar)_source26).id;
                    {
                      _797_b1 = false;
                    }
                  }
                } else  {
                  BigInteger _827_x1 = ((BasicTerm_StackVar)_source25).id;
                  BasicTerm _source27 = _823___ms_h1;
                  if (_source27.is_StackVar) {
                    BigInteger _828_x2 = ((BasicTerm_StackVar)_source27).id;
                    if (((__default.idsFromInput(input1)).Contains(_827_x1)) && ((__default.idsFromInput(input2)).Contains(_828_x2))) {
                      _797_b1 = (__default.getPos(input1, _827_x1)) == (__default.getPos(input2, _828_x2));
                    } else if (((dict1).Contains(_827_x1)) && ((dict2).Contains(_828_x2))) {
                      bool _out4;
                      __default.compareDictElems(input1, input2, dict1, dict2, _827_x1, _828_x2, (prev__ids1).Union(Dafny.Set<BigInteger>.FromElements(key1)), (prev__ids2).Union(Dafny.Set<BigInteger>.FromElements(key2)), out _out4);
                      _797_b1 = _out4;
                    } else {
                      _797_b1 = false;
                    }
                  } else  {
                    BigInteger _829_x2 = ((BasicTerm_Value)_source27).val;
                    {
                      _797_b1 = false;
                    }
                  }
                }
              }
              b = _797_b1;
              return;
            } else {
              b = false;
              return;
            }
          } else  {
            BigInteger _830_id2 = ((StackElem_Op)_source11).id;
            Dafny.Sequence<BasicTerm> _831_l2 = ((StackElem_Op)_source11).input__stack;
            b = false;
            return;
          }
        }
      }
    }
    public static void areEquivalentSFS(ASFS sfs1, ASFS sfs2, out bool b)
    {
    TAIL_CALL_START: ;
      b = false;
      _System.Tuple2<ASFS,ASFS> _source28 = @_System.Tuple2<ASFS,ASFS>.create(sfs1, sfs2);
 {
        ASFS _832___ms_h0 = ((_System.Tuple2<ASFS,ASFS>)_source28)._0;
        ASFS _833___ms_h1 = ((_System.Tuple2<ASFS,ASFS>)_source28)._1;
        ASFS _source29 = _832___ms_h0;
 {
          Dafny.Sequence<BasicTerm> _834_input1 = ((ASFS)_source29).input;
          Dafny.Map<BigInteger,StackElem> _835_dict1 = ((ASFS)_source29).dict;
          Dafny.Sequence<BasicTerm> _836_output1 = ((ASFS)_source29).output;
          ASFS _source30 = _833___ms_h1;
 {
            Dafny.Sequence<BasicTerm> _837_input2 = ((ASFS)_source30).input;
            Dafny.Map<BigInteger,StackElem> _838_dict2 = ((ASFS)_source30).dict;
            Dafny.Sequence<BasicTerm> _839_output2 = ((ASFS)_source30).output;
            if (((new BigInteger((_834_input1).Count)) != (new BigInteger((_837_input2).Count))) || ((new BigInteger((_836_output1).Count)) != (new BigInteger((_839_output2).Count)))) {
              b = false;
              return;
            } else {
              BigInteger _840_i;
              _840_i = new BigInteger(0);
              while ((_840_i) < (new BigInteger((_836_output1).Count))) {
                _System.Tuple2<BasicTerm,BasicTerm> _source31 = @_System.Tuple2<BasicTerm,BasicTerm>.create((_836_output1).Select(_840_i), (_839_output2).Select(_840_i));
 {
                  BasicTerm _841___ms_h0 = ((_System.Tuple2<BasicTerm,BasicTerm>)_source31)._0;
                  BasicTerm _842___ms_h1 = ((_System.Tuple2<BasicTerm,BasicTerm>)_source31)._1;
                  BasicTerm _source32 = _841___ms_h0;
                  if (_source32.is_Value) {
                    BigInteger _843_x1 = ((BasicTerm_Value)_source32).val;
                    BasicTerm _source33 = _842___ms_h1;
                    if (_source33.is_Value) {
                      BigInteger _844_x2 = ((BasicTerm_Value)_source33).val;
                      if ((_843_x1) != (_844_x2)) {
                        b = false;
                        return;
                      }
                    } else  {
                      BigInteger _845_x2 = ((BasicTerm_StackVar)_source33).id;
                      b = false;
                      return;
                    }
                  } else  {
                    BigInteger _846_x1 = ((BasicTerm_StackVar)_source32).id;
                    BasicTerm _source34 = _842___ms_h1;
                    if (_source34.is_StackVar) {
                      BigInteger _847_x2 = ((BasicTerm_StackVar)_source34).id;
                      if (((__default.idsFromInput(_834_input1)).Contains(_846_x1)) && ((__default.idsFromInput(_837_input2)).Contains(_847_x2))) {
                        if ((__default.getPos(_834_input1, _846_x1)) != (__default.getPos(_837_input2, _847_x2))) {
                          b = false;
                          return;
                        }
                      } else if (((_835_dict1).Contains(_846_x1)) && ((_838_dict2).Contains(_847_x2))) {
                        bool _848_aux;
                        bool _out5;
                        __default.compareDictElems(_834_input1, _837_input2, _835_dict1, _838_dict2, _846_x1, _847_x2, Dafny.Set<BigInteger>.FromElements(), Dafny.Set<BigInteger>.FromElements(), out _out5);
                        _848_aux = _out5;
                        if (!(_848_aux)) {
                          b = false;
                          return;
                        }
                      } else {
                        b = false;
                        return;
                      }
                    } else  {
                      BigInteger _849_x2 = ((BasicTerm_Value)_source34).val;
                      b = false;
                      return;
                    }
                  }
                }
                _840_i = (_840_i) + (new BigInteger(1));
              }
              b = true;
              return;
            }
          }
        }
      }
    }
  }
} // end of namespace _module
