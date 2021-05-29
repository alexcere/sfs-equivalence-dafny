datatype Term = Value(val:int) | StackVar(id:int)

function stackVariableFromSeq(stack:seq<Term>): (result:set<int>) 
decreases stack
ensures |stack| > 0 ==> match stack[0] {case Value(x) => true case StackVar(x) => x in result}
{
    if stack == [] then {} else match stack[0] {case Value(x) => stackVariableFromSeq(stack[1..]) case StackVar(x) => {x} + stackVariableFromSeq(stack[1..])}
}


lemma idsInInputAreInStackVariableFromSeq(stack:seq<Term>, result:set<int>)
decreases stack
requires stackVariableFromSeq(stack) <= result
ensures forall i :: 0 <= i < |stack| ==> match stack[i] {case Value(x) => true case StackVar(x) => x in result}
{
    if |stack| > 0 {
        assert match stack[0] {case Value(x) => true case StackVar(x) => x in result};
        idsInInputAreInStackVariableFromSeq(stack[1..], result);
        assert forall elem :: elem in stack[1..] ==> match elem {case Value(x) => true case StackVar(x) => x in result};
        assert stack[0..1] + stack[1..] == stack;
    }
}

lemma idsAreOpsKeysOrInput(input:seq<Term>, elem:Term, operations:map<int, (seq<Term>, bool)>, previously_visited:seq<int>) 
requires forall i :: i in previously_visited ==> i in operations
requires multiset(previously_visited) <= multiset(operations.Keys)
requires elementIsCorrect(input, elem, operations, previously_visited)
ensures match elem {case Value(x) => true case StackVar(x) => x in (operations.Keys + stackVariableFromSeq(input))}
{
    match elem 
        case StackVar(x) => assert x in operations || StackVar(x) in input; 
                            idsInInputAreInStackVariableFromSeq(input, stackVariableFromSeq(input));
                            assert StackVar(x) in input ==> x in stackVariableFromSeq(input);
        case Value(x) =>
}


predicate elementIsCorrect (input:seq<Term>, elem:Term, operations:map<int, (seq<Term>, bool)>, previously_visited:seq<int>) 
decreases |multiset(operations.Keys) - multiset(previously_visited)|
requires forall i :: i in previously_visited ==> i in operations
requires multiset(previously_visited) <= multiset(operations.Keys)
{
    match elem 
        case Value(x) => true  // A numerical value is directly correct
        case StackVar(id) => 
            (id in operations && id !in previously_visited && (forall other_elem :: other_elem in operations[id].0 ==> 
            match other_elem 
                case Value(_)      => true 
                case StackVar(id2) => StackVar(id2) in input || elementIsCorrect(input, other_elem, operations, previously_visited + [id]) 
            )) 
            || StackVar(id) in input 
}

// Condition: output stack variables are correct
predicate seqIsCorrect (input:seq<Term>, sequence:seq<Term>, operations:map<int, (seq<Term>, bool)>) {
    forall elem :: elem in sequence ==> elementIsCorrect(input, elem, operations, [])
}

lemma seqCorrectImplies(input:seq<Term>, sequence:seq<Term>, operations:map<int, (seq<Term>, bool)>)
decreases sequence
requires seqIsCorrect(input, sequence, operations)
ensures forall i :: 0 <= i < |sequence| ==> match sequence[i] {case Value(x) => true case StackVar(x) => x in (operations.Keys + stackVariableFromSeq(input))}
{
    if |sequence| > 0 {
        idsAreOpsKeysOrInput(input, sequence[0], operations, []);
        seqCorrectImplies(input, sequence[1..], operations);
        assert sequence[0..1] + sequence[1..] == sequence;
    }
}

// Condition: all input stack variables are correct and conmutative ones has size two
predicate operationsAreCorrect (input:seq<Term>, operations:map<int, (seq<Term>, bool)>){
    forall key :: key in operations ==> elementIsCorrect(input, StackVar(key), operations, []) && 
        (seqIsCorrect(input, operations[key].0, operations) && (operations[key].1 ==> |operations[key].0| == 2))
 }


lemma operationsCorrectImpliesAux(input:seq<Term>, current_idx:set<int>, operations:map<int, (seq<Term>, bool)>)
decreases current_idx
requires operationsAreCorrect(input, operations)
requires current_idx <= operations.Keys
ensures forall key :: key in current_idx ==> key in (operations.Keys + stackVariableFromSeq(input)) &&
    (forall i :: 0 <= i < |operations[key].0| ==> match (operations[key].0)[i] {case Value(x) => true case StackVar(x) => x in (operations.Keys + stackVariableFromSeq(input))})
{
    if current_idx != {} {
        var x :| x in current_idx;
        idsAreOpsKeysOrInput(input, StackVar(x), operations, []);
        seqCorrectImplies(input, operations[x].0, operations);
        operationsCorrectImpliesAux(input, current_idx - {x}, operations);
    }
}

lemma operationsCorrectImpliesCorrect(input:seq<Term>, operations:map<int, (seq<Term>, bool)>)
requires operationsAreCorrect(input, operations)
ensures forall key :: key in operations.Keys ==>
    (forall i :: 0 <= i < |operations[key].0| ==> match (operations[key].0)[i] 
    {case Value(x) => true case StackVar(x) => x in (operations.Keys + stackVariableFromSeq(input))})

{
    operationsCorrectImpliesAux(input, operations.Keys, operations);
}

// Condition
predicate outputIsCorrect (input:seq<Term>, output:seq<Term>, operations:map<int, (seq<Term>, bool)>){
    seqIsCorrect(input, output, operations)
}


// Condition: all terms in the stack are stack variables and no index is repeated
predicate inputIsCorrect (input:seq<Term>, previously_visited:seq<int>) 
decreases input 
{
    if input == [] then true else 
        match input[0]
            case Value(x) => false 
            case StackVar(x) => x !in previously_visited && inputIsCorrect(input[1..], previously_visited + [x])  
}



predicate isSFS (input:seq<Term>, output:seq<Term>, ops:map<int, (seq<Term>, bool)>) {
    inputIsCorrect(input, []) && operationsAreCorrect(input, ops) && outputIsCorrect(input, output, ops) && (stackVariableFromSeq(input) !! ops.Keys)
}

lemma SFSproperties(input:seq<Term>, output:seq<Term>, ops:map<int, (seq<Term>, bool)>)
requires isSFS(input, output, ops)
ensures forall i :: 0 <= i < |output| ==> match output[i] {case Value(x) => true case StackVar(x) => x in (ops.Keys + stackVariableFromSeq(input))}
ensures forall key :: key in ops.Keys ==> (forall i :: 0 <= i < |ops[key].0| ==> 
    match (ops[key].0)[i] {case Value(x) => true case StackVar(x) => x in (ops.Keys + stackVariableFromSeq(input))})
{
    operationsCorrectImpliesCorrect(input, ops);
    seqCorrectImplies(input, output, ops);
}

predicate equivalentElement(el1:Term, el2:Term, dict:map<int, int>) 
requires match el1 {case Value(x1) => true case StackVar(x1) => x1 in dict}
{
    match (el1, el2)
        case (Value(x1), Value(x2)) => x1 == x2 
        case (StackVar(x1), StackVar(x2)) => dict[x1] == x2
        case (Value(x1), StackVar(x2)) => false
        case (StackVar(x1), Value(x2)) => false
}

predicate equivalentSeq(seq1:seq<Term>, seq2:seq<Term>, dict:map<int,int>)
requires forall i :: 0 <= i < |seq1| ==> match seq1[i] {case Value(x1) => true case StackVar(x1) => x1 in dict}
{
    |seq1| == |seq2| && (forall i :: 0 <= i < |seq1| ==> equivalentElement(seq1[i], seq2[i], dict))
}

predicate equivalentConmSeq(seq1:seq<Term>, seq2:seq<Term>, dict:map<int,int>)
requires |seq1| == 2
requires |seq2| == 2
requires forall i :: 0 <= i < |seq1| ==> match seq1[i] {case Value(x1) => true case StackVar(x1) => x1 in dict}
{
    (equivalentElement(seq1[0], seq2[0], dict) && equivalentElement(seq1[1], seq2[1], dict)) || 
    (equivalentElement(seq1[0], seq2[1], dict) && equivalentElement(seq1[1], seq2[0], dict))
}

predicate equivalentOps(op1:map<int, (seq<Term>, bool)>, op2:map<int, (seq<Term>, bool)>, dict:map<int, int>)
requires forall el1 :: (el1 in op1 ==> el1 in dict && (op1[el1].1 ==> |op1[el1].0| == 2) &&
    (forall i :: 0 <= i < |op1[el1].0| ==> match op1[el1].0[i] {case Value(x1) => true case StackVar(x1) => x1 in dict} ))
requires forall el2 :: (el2 in op2 ==> el2 in dict.Values && (op2[el2].1 ==> |op2[el2].0| == 2) &&
    (forall i :: 0 <= i < |op2[el2].0| ==> match op2[el2].0[i] {case Value(x1) => true case StackVar(x1) => x1 in dict.Values} ))
requires forall el1 :: el1 in op1 ==> el1 in dict && dict[el1] in op2
{
    forall el1 :: el1 in op1 ==> (op1[el1].1 ==> op2[dict[el1]].1 && equivalentConmSeq(op1[el1].0, op2[dict[el1]].0, dict)) 
        && (!op1[el1].1 ==> !op2[dict[el1]].1 && equivalentSeq(op1[el1].0, op2[dict[el1]].0, dict))
}

// predicate equivalentOp(operations:map<int, (seq<Term>, bool)>, dict:map<int, int>)

lemma wellDefinedDict(in1:seq<Term>, out:seq<Term>, ops:map<int, (seq<Term>, bool)>, general_set:set<int>)
requires isSFS(in1, out, ops)
requires general_set == stackVariableFromSeq(in1) + ops.Keys
ensures forall i :: 0 <= i < |out| ==> match out[i] {case Value(x) => true case StackVar(x) => x in general_set}
ensures forall i :: 0 <= i < |in1| ==> match in1[i] {case Value(x) => true case StackVar(x) => x in general_set}
ensures forall key :: key in ops ==> (forall i :: 0 <= i < |ops[key].0| ==> match (ops[key].0)[i] {case Value(x) => true case StackVar(x) => x in general_set})
{
    SFSproperties(in1, out, ops);
    idsInInputAreInStackVariableFromSeq(in1, stackVariableFromSeq(in1));
}   

predicate mapInjective<U,V>(m: map<U,V>)
{
	forall a,b :: a in m && b in m ==> (a != b ==> m[a] != m[b])
}

predicate mapIsWellDefined(input1:seq<Term>, output1:seq<Term>, ops1:map<int, (seq<Term>, bool)>, 
                           input2:seq<Term>, output2:seq<Term>, ops2:map<int, (seq<Term>, bool)>, 
                           dict:map<int, int>)
{
    (dict.Keys == stackVariableFromSeq(input1) + ops1.Keys) && 
    (dict.Values == stackVariableFromSeq(input2) + ops2.Keys) &&
    (mapInjective(dict)) && (forall key :: key in ops1 ==> dict[key] in ops2) && 
    (forall key :: key in stackVariableFromSeq(input1) ==> dict[key] in stackVariableFromSeq(input2)) &&
    (forall value :: value in ops2 ==> (exists key :: key in ops1 && dict[key] == value)) &&  
    (forall value :: value in stackVariableFromSeq(input2) ==> (exists key :: key in stackVariableFromSeq(input1) && dict[key] == value)) &&
    (forall key :: key in ops1 ==> ops1[key].1 == ops2[dict[key]].1)
}

predicate equivalentSFS(input1:seq<Term>, output1:seq<Term>, ops1:map<int, (seq<Term>, bool)>, 
                        input2:seq<Term>, output2:seq<Term>, ops2:map<int, (seq<Term>, bool)>, 
                        dict:map<int, int>)
requires isSFS(input1, output1, ops1)
requires isSFS(input2, output2, ops2)
requires mapIsWellDefined(input1, output1, ops1, input2, output2, ops2, dict)
{
    wellDefinedDict(input1, output1, ops1, dict.Keys);
    wellDefinedDict(input2, output2, ops2, dict.Values);
    equivalentSeq(input1, input2, dict) && equivalentSeq(output1, output2, dict) && equivalentOps(ops1, ops2, dict)
}
