datatype BasicTerm = Value(val:int) | StackVar(id:int)
datatype StackElem = Op(id:int, input_stack:seq<BasicTerm>) | COp(id:int, elem1:BasicTerm, elem2:BasicTerm)
datatype ASFS = SFS(input:seq<BasicTerm>, dict:map<int,StackElem>, output:seq<BasicTerm>)

// Auxiliary predicates and functions

predicate isStackVar(el:BasicTerm)
{
    match el 
        case Value(x)    => false 
        case StackVar(x) => true
}

function method getId(el:BasicTerm) : int
requires isStackVar(el)
{
    match el 
        case StackVar(x) => x
}

// Input related predicates, functions and lemmas
 
function method idsFromInput (input:seq<BasicTerm>) : (sol:set<int>)
decreases input
ensures forall elem :: elem in sol ==> StackVar(elem) in input
{
    if input == [] then {}
    else 
        match input[0] {
            case Value(val)   => {}
            case StackVar(id) => {id} + idsFromInput(input[1..])
        }
}

predicate allVarsAreStackVar (input:seq<BasicTerm>)
decreases input
{
    if input == [] then true 
    else 
        match input[0] {
            case Value(val)   => false 
            case StackVar(id) => allVarsAreStackVar(input[1..])
        }
}

predicate noRepeatedStackVar (input:seq<BasicTerm>, previously_ids:set<int>)
decreases input
{
    if input == [] then true 
    else 
        match input[0] {
            case Value(val)   => false 
            case StackVar(id) => id !in previously_ids && noRepeatedStackVar(input[1..], previously_ids + {id})
        }
}


function method atId(input:seq<BasicTerm>, pos:int) : (id:int)
requires 0 <= pos < |input|
requires allVarsAreStackVar(input)
ensures StackVar(id) in input
ensures id in idsFromInput(input)
{
    if pos == 0 then match input[0] case StackVar(x) => x else atId(input, pos - 1)
}

function method getPos(input:seq<BasicTerm>, id:int) : (pos:int)
requires id in idsFromInput(input)
requires allVarsAreStackVar(input)
ensures 0 <= pos < |input|
ensures match input[pos] {case Value(x) => false case StackVar(x) => x == id} 

{
    match input[0] 
        case StackVar(x) => if x == id then 0 else 1 + getPos(input[1..], id)
}


predicate initialInputIsWellDefined (input:seq<BasicTerm>)
{
    allVarsAreStackVar(input) && noRepeatedStackVar(input, {})
}


predicate idsInDictAreWellDelimited(inputStack:seq<BasicTerm>, dict:map<int, StackElem>) 
{
    forall key :: key in dict ==>
        match dict[key]
            case Op(id, l) =>
                id == key && 
                (forall i :: 0 <= i < |l| ==> match l[i]{
                        case Value(x) => true 
                        case StackVar(id2) =>  (id2 in idsFromInput(inputStack) || id2 in dict)})
            case COp(id, x1, x2) => 
                id == key &&
                match x1 {
                        case Value(x) => true 
                        case StackVar(id2) => id2 in idsFromInput(inputStack) || id2 in dict
                    } 
                    && match x2 {
                        case Value(x) => true 
                        case StackVar(id2) => id2 in idsFromInput(inputStack) || id2 in dict
                    }
}

predicate dictElementConverges(inputStack:seq<BasicTerm>, dict:map<int, StackElem>, key:int, previously_ids:set<int>)
decreases dict.Keys - previously_ids
requires previously_ids <= dict.Keys
requires key in dict
requires idsInDictAreWellDelimited(inputStack, dict)
{
    match dict[key]
        case Op(id, l)       => 
            id !in previously_ids &&
            forall i :: 0 <= i < |l|  ==> match l[i] {
                case Value(x) => true 
                case StackVar(x1) => if x1 in idsFromInput(inputStack) then true else dictElementConverges(inputStack, dict, x1, previously_ids + {id} )}
        case COp(id, el1, el2) =>
            id !in previously_ids &&
            match el1 {
                case Value(x) => true 
                case StackVar(x1) => if x1 in idsFromInput(inputStack) then true else dictElementConverges(inputStack, dict, x1, previously_ids + {id} )}
            && 
            match el2 {
                case Value(x) => true 
                case StackVar(x1) => if x1 in idsFromInput(inputStack) then true else dictElementConverges(inputStack, dict, x1, previously_ids + {id} )}
}

predicate dictIsWellDefined(inputStack:seq<BasicTerm>, dict:map<int, StackElem>)
{
    (dict.Keys * idsFromInput(inputStack) == {}) && idsInDictAreWellDelimited(inputStack, dict) 
    && (forall key :: key in dict ==> dictElementConverges(inputStack, dict, key, {}))
}

// Output related definitions

predicate outputIsWellDefined(inputStack:seq<BasicTerm>, dict:map<int, StackElem>, output:seq<BasicTerm>)
{
    forall elem :: elem in output ==> match elem {case Value(x) => true case StackVar(id) => id in dict || id in idsFromInput(inputStack)}
}

// SFS related definitions

predicate isSFS(sfs:ASFS)
{
    match sfs 
        case SFS(input, dict, output) => initialInputIsWellDefined(input) && dictIsWellDefined(input, dict) && outputIsWellDefined(input, dict, output)
}

// Comparison related predicates: (b:bool)


predicate compareStackElem(input1:seq<BasicTerm>, input2:seq<BasicTerm>, dict1:map<int, StackElem>, dict2:map<int, StackElem>, 
                           key1:int, key2:int, prev_ids1:set<int>, prev_ids2:set<int>)
decreases |dict1.Keys - prev_ids1|
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
{
    match (dict1[key1], dict2[key2])
        case (Op(id1, l1), Op(id2, l2)) => 
            |l1| == |l2| &&
            forall i :: 0 <= i < |l1|  ==> 
                match (l1[i], l2[i]) {
                    case (Value(x1), Value(x2)) => x1 == x2 
                    case (StackVar(x1), StackVar(x2)) => 
                        if (x1 in idsFromInput(input1) && x2 in idsFromInput(input2)) 
                                then getPos(input1, x1) == getPos(input2, x2)
                        else if (x1 in dict1 && x2 in dict2) 
                                then 
                                    compareStackElem(input1, input2, dict1, dict2, x1, x2, prev_ids1 + {key1}, prev_ids2 + {key2})
                        else false
                    case (Value(x1), StackVar(x2)) => false
                    case (StackVar(x1), Value(x2)) => false
                }
        case (COp(id1, el11, el12), COp(id2, el21, el22))  => 
            (match (el11, el21) {
                case (Value(x1), Value(x2)) => x1 == x2 
                case (StackVar(x1), StackVar(x2)) => 
                    if (x1 in idsFromInput(input1) && x2 in idsFromInput(input2)) 
                        then getPos(input1, x1) == getPos(input2, x2)
                    else if (x1 in dict1 && x2 in dict2) 
                        then 
                            compareStackElem(input1, input2, dict1, dict2, x1, x2, prev_ids1 + {key1}, prev_ids2 + {key2})
                    else false
                case (Value(x1), StackVar(x2)) => false
                case (StackVar(x1), Value(x2)) => false
            } &&
            match (el12, el22) {
                case (Value(x1), Value(x2)) => x1 == x2 
                case (StackVar(x1), StackVar(x2)) => 
                    if (x1 in idsFromInput(input1) && x2 in idsFromInput(input2)) 
                        then getPos(input1, x1) == getPos(input2, x2)
                    else if (x1 in dict1 && x2 in dict2) 
                        then 
                            compareStackElem(input1, input2, dict1, dict2, x1, x2, prev_ids1 + {key1}, prev_ids2 + {key2})
                    else false
                case (Value(x1), StackVar(x2)) => false
                case (StackVar(x1), Value(x2)) => false
            }) ||
            (match (el11, el22) {
                case (Value(x1), Value(x2)) => x1 == x2 
                case (StackVar(x1), StackVar(x2)) => 
                    if (x1 in idsFromInput(input1) && x2 in idsFromInput(input2)) 
                        then getPos(input1, x1) == getPos(input2, x2)
                    else if (x1 in dict1 && x2 in dict2) 
                        then 
                            compareStackElem(input1, input2, dict1, dict2, x1, x2, prev_ids1 + {key1}, prev_ids2 + {key2})
                    else false
                case (Value(x1), StackVar(x2)) => false
                case (StackVar(x1), Value(x2)) => false
            } &&
            match (el12, el21) {
                case (Value(x1), Value(x2)) => x1 == x2 
                case (StackVar(x1), StackVar(x2)) => 
                    if (x1 in idsFromInput(input1) && x2 in idsFromInput(input2)) 
                        then getPos(input1, x1) == getPos(input2, x2)
                    else if (x1 in dict1 && x2 in dict2) 
                        then 
                            compareStackElem(input1, input2, dict1, dict2, x1, x2, prev_ids1 + {key1}, prev_ids2 + {key2})
                    else false
                case (Value(x1), StackVar(x2)) => false
                case (StackVar(x1), Value(x2)) => false
            })
        case (COp(id1, x1, y1), Op(id2, l2))  => false 
        case (Op(id1, l1), COp(id2, x2, y2))  => false
}

predicate areEquivalent(sfs1:ASFS, sfs2:ASFS)
requires isSFS(sfs1)
requires isSFS(sfs2)
{
    match (sfs1, sfs2) 
        case (SFS(input1, dict1, output1), SFS(input2, dict2, output2)) => |input1| == |input2| && |output1| == |output2| 
        && (forall i :: 0 <= i < |output1| ==> match (output1[i], output2[i])
        {
            case (Value(x1), Value(x2)) => x1 == x2 
            case (StackVar(x1), StackVar(x2)) => 
                if (x1 in idsFromInput(input1) && x2 in idsFromInput(input2)) 
                    then getPos(input1, x1) == getPos(input2, x2) 
                else if (x1 in dict1 && x2 in dict2)
                    then compareStackElem(input1, input2, dict1, dict2, x1, x2, {}, {})
                else false
            case (StackVar(x1), Value(x2)) => false 
            case (Value(x1), StackVar(x2)) => false
        })
}


// Verification related methods

method compareDictElems(input1:seq<BasicTerm>, input2:seq<BasicTerm>, dict1:map<int, StackElem>, dict2:map<int, StackElem>, 
                           key1:int, key2:int, prev_ids1:set<int>, prev_ids2:set<int>) returns (b:bool)
decreases |dict1.Keys - prev_ids1|
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
{
    match (dict1[key1], dict2[key2])
        case (Op(id1, l1), Op(id2, l2)) => 
            if (|l1| != |l2|) {
                return false;
            }
            else {
                var i := 0;
                while (i < |l1|) 
                decreases |l1| - i 
                invariant 0 <= i <= |l1|
                invariant forall j :: 0 <= j < i  ==> 
                    match (l1[j], l2[j]) {
                        case (Value(x1), Value(x2)) => x1 == x2 
                        case (StackVar(x1), StackVar(x2)) => 
                            if (x1 in idsFromInput(input1) && x2 in idsFromInput(input2)) 
                                    then getPos(input1, x1) == getPos(input2, x2)
                            else if (x1 in dict1 && x2 in dict2) 
                                    then 
                                        compareStackElem(input1, input2, dict1, dict2, x1, x2, prev_ids1 + {key1}, prev_ids2 + {key2})
                            else false
                        case (Value(x1), StackVar(x2)) => false
                        case (StackVar(x1), Value(x2)) => false
                    }
                {
                    match (l1[i], l2[i]) {
                        case (Value(x1), Value(x2)) => 
                            if (x1 != x2) {
                                return false;
                            } 
                        case (StackVar(x1), StackVar(x2)) => 
                            if (x1 in idsFromInput(input1) && x2 in idsFromInput(input2)) {
                                if (getPos(input1, x1) != getPos(input2, x2)){
                                    return false;
                                }      
                            }                               
                            else if (x1 in dict1 && x2 in dict2) {
                                var aux := compareDictElems(input1, input2, dict1, dict2, x1, x2, prev_ids1 + {key1}, prev_ids2 + {key2});
                                if (!aux){
                                    return false;
                                }
                                
                            }
                            else {
                                return false;
                            }
                        case (Value(x1), StackVar(x2)) => return false;
                        case (StackVar(x1), Value(x2)) => return false;
                    }
                    i := i + 1;
                }
            return true;
        }   
        case (COp(id1, el11, el12), COp(id2, el21, el22))  => 

            var b1 := true;
            
            match (el11, el21) {
                case (Value(x1), Value(x2)) => 
                    b1 := (x1 == x2); 
                case (StackVar(x1), StackVar(x2)) => 
                    if (x1 in idsFromInput(input1) && x2 in idsFromInput(input2)) {
                        b1 :=  getPos(input1, x1) == getPos(input2, x2);
                    }
                    else if (x1 in dict1 && x2 in dict2) {
                        b1 := compareDictElems(input1, input2, dict1, dict2, x1, x2, prev_ids1 + {key1}, prev_ids2 + {key2});
                    }        
                    else {
                        b1 := false;
                    }
                case (Value(x1), StackVar(x2)) =>
                    {
                        b1 := false;
                    }
                case (StackVar(x1), Value(x2)) => {
                    b1 := false;
                }
            }

            var b2 := true;

            match (el12, el22) {
                case (Value(x1), Value(x2)) => 
                    b2 := (x1 == x2); 
                case (StackVar(x1), StackVar(x2)) => 
                    if (x1 in idsFromInput(input1) && x2 in idsFromInput(input2)) {
                        b2 :=  getPos(input1, x1) == getPos(input2, x2);
                    }
                    else if (x1 in dict1 && x2 in dict2) {
                        b2 := compareDictElems(input1, input2, dict1, dict2, x1, x2, prev_ids1 + {key1}, prev_ids2 + {key2});
                    }        
                    else {
                        b2 := false;
                    }
                case (Value(x1), StackVar(x2)) =>
                    {
                        b2 := false;
                    }
                case (StackVar(x1), Value(x2)) => {
                    b2 := false;
                }
            }

            if (b1 && b2){
                return true;
            } 

            b1 := true;
            
            match (el12, el21) {
                case (Value(x1), Value(x2)) => 
                    b1 := (x1 == x2); 
                case (StackVar(x1), StackVar(x2)) => 
                    if (x1 in idsFromInput(input1) && x2 in idsFromInput(input2)) {
                        b1 :=  getPos(input1, x1) == getPos(input2, x2);
                    }
                    else if (x1 in dict1 && x2 in dict2) {
                        b1 := compareDictElems(input1, input2, dict1, dict2, x1, x2, prev_ids1 + {key1}, prev_ids2 + {key2});
                    }        
                    else {
                        b1 := false;
                    }
                case (Value(x1), StackVar(x2)) =>
                    {
                        b1 := false;
                    }
                case (StackVar(x1), Value(x2)) => {
                    b1 := false;
                }
            }

            b2 := true;

            match (el11, el22) {
                case (Value(x1), Value(x2)) => 
                    b2 := (x1 == x2); 
                case (StackVar(x1), StackVar(x2)) => 
                    if (x1 in idsFromInput(input1) && x2 in idsFromInput(input2)) {
                        b2 :=  getPos(input1, x1) == getPos(input2, x2);
                    }
                    else if (x1 in dict1 && x2 in dict2) {
                        b2 := compareDictElems(input1, input2, dict1, dict2, x1, x2, prev_ids1 + {key1}, prev_ids2 + {key2});
                    }        
                    else {
                        b2 := false;
                    }
                case (Value(x1), StackVar(x2)) =>
                    {
                        b2 := false;
                    }
                case (StackVar(x1), Value(x2)) => {
                    b1 := false;
                }
            }

            if (b1 && b2){
                return true;
            } 
            else {
                return false;
            }
            
        case (COp(id1, x1, y1), Op(id2, l2))  => return false; 
        case (Op(id1, l1), COp(id2, x2, y2))  => return false;
}


method areEquivalentSFS(sfs1:ASFS, sfs2:ASFS) returns (b:bool)
requires isSFS(sfs1)
requires isSFS(sfs2)
ensures b == areEquivalent(sfs1, sfs2)
{
    match (sfs1, sfs2) 
        case (SFS(input1, dict1, output1), SFS(input2, dict2, output2)) => 
            if(|input1| != |input2| || |output1| != |output2|){
                return false;
            } 
            else {
                var i := 0;
                while i < |output1| 
                decreases |output1| - i
                invariant 0 <= i <= |output1|
                invariant (forall j :: 0 <= j < i ==> match (output1[j], output2[j])
                    {
                        case (Value(x1), Value(x2)) => x1 == x2 
                        case (StackVar(x1), StackVar(x2)) => 
                            if (x1 in idsFromInput(input1) && x2 in idsFromInput(input2)) 
                                then getPos(input1, x1) == getPos(input2, x2) 
                            else if (x1 in dict1 && x2 in dict2)
                                then compareStackElem(input1, input2, dict1, dict2, x1, x2, {}, {})
                            else false
                        case (StackVar(x1), Value(x2)) => false 
                        case (Value(x1), StackVar(x2)) => false
                    })
                {
                    match (output1[i], output2[i])
                    {
                        case (Value(x1), Value(x2)) => 
                            if(x1 != x2) {
                                return false;
                            } 
                        case (StackVar(x1), StackVar(x2)) => 
                            if (x1 in idsFromInput(input1) && x2 in idsFromInput(input2))
                            {
                                if getPos(input1, x1) != getPos(input2, x2){
                                    return false;
                                }
                            }
                            else if (x1 in dict1 && x2 in dict2) 
                            {
                                var aux := compareDictElems(input1, input2, dict1, dict2, x1, x2, {}, {});
                                if !aux{
                                    return false;
                                }
                            }
                            else {
                                return false;
                            }
                        case (StackVar(x1), Value(x2)) => return false; 
                        case (Value(x1), StackVar(x2)) => return false;
                    }
                    i := i + 1;
                }
                return true;
            }
}


/*
lemma initialInputProperties(input:seq<BasicTerm>, previously_ids:set<int>)
requires initialInputIsWellDefined(input, previously_ids)
ensures idsFromInput(input) * previously_ids == {}
ensures |input| > 0 ==> idsFromInput(input[1..]) < idsFromInput(input)
{
}
predicate mapInjective<U,V>(m: map<U,V>)
{
	forall a,b :: a in m && b in m ==> (a != b ==> m[a] != m[b])
}
function obtainTransformationAuxiliar(initial1:seq<BasicTerm>, initial2:seq<BasicTerm>, previously_ids1:set<int>, previously_ids2:set<int>) : (sol:map<int,int>)
decreases initial1
requires initialInputIsWellDefined(initial1, previously_ids1)
requires initialInputIsWellDefined(initial2, previously_ids2)
requires |initial1| == |initial2|
requires previously_ids1 * idsFromInput(initial1) == {}
requires previously_ids2 * idsFromInput(initial2) == {}
ensures sol.Keys == idsFromInput(initial1)
ensures sol.Values == idsFromInput(initial2)
ensures mapInjective(sol)
{
    if |initial1| == 0 
        then map[]
    else  
        match (initial1[0], initial2[0])
            case (StackVar(id1), StackVar(id2)) => 
                initialInputProperties(initial1, previously_ids1);
                initialInputProperties(initial2, previously_ids2);
                var previous_map := obtainTransformationAuxiliar(initial1[1..], initial2[1..], previously_ids1 + {id1}, previously_ids2 + {id2}); 
                previous_map[id1 := id2] 
}
function obtainTransformation(initial1:seq<BasicTerm>, initial2:seq<BasicTerm>) : (sol:map<int,int>)
requires initialInputIsWellDefined(initial1, {})
requires initialInputIsWellDefined(initial2, {})
requires |initial1| == |initial2|
ensures sol.Keys == idsFromInput(initial1)
ensures sol.Values == idsFromInput(initial2)
ensures mapInjective(sol)
{
    obtainTransformationAuxiliar(initial1, initial2, {}, {})
}/*
lemma initialInputProperties(input:seq<BasicTerm>, previously_ids:set<int>)
requires initialInputIsWellDefined(input, previously_ids)
ensures idsFromInput(input) * previously_ids == {}
ensures |input| > 0 ==> idsFromInput(input[1..]) < idsFromInput(input)
{
}
predicate mapInjective<U,V>(m: map<U,V>)
{
	forall a,b :: a in m && b in m ==> (a != b ==> m[a] != m[b])
}
function obtainTransformationAuxiliar(initial1:seq<BasicTerm>, initial2:seq<BasicTerm>, previously_ids1:set<int>, previously_ids2:set<int>) : (sol:map<int,int>)
decreases initial1
requires initialInputIsWellDefined(initial1, previously_ids1)
requires initialInputIsWellDefined(initial2, previously_ids2)
requires |initial1| == |initial2|
requires previously_ids1 * idsFromInput(initial1) == {}
requires previously_ids2 * idsFromInput(initial2) == {}
ensures sol.Keys == idsFromInput(initial1)
ensures sol.Values == idsFromInput(initial2)
ensures mapInjective(sol)
{
    if |initial1| == 0 
        then map[]
    else  
        match (initial1[0], initial2[0])
            case (StackVar(id1), StackVar(id2)) => 
                initialInputProperties(initial1, previously_ids1);
                initialInputProperties(initial2, previously_ids2);
                var previous_map := obtainTransformationAuxiliar(initial1[1..], initial2[1..], previously_ids1 + {id1}, previously_ids2 + {id2}); 
                previous_map[id1 := id2] 
}
function obtainTransformation(initial1:seq<BasicTerm>, initial2:seq<BasicTerm>) : (sol:map<int,int>)
requires initialInputIsWellDefined(initial1, {})
requires initialInputIsWellDefined(initial2, {})
requires |initial1| == |initial2|
ensures sol.Keys == idsFromInput(initial1)
ensures sol.Values == idsFromInput(initial2)
ensures mapInjective(sol)
{
    obtainTransformationAuxiliar(initial1, initial2, {}, {})
}*/