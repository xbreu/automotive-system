function emptyLists<T>(size : nat) : seq<seq<T>>
	ensures |emptyLists<T>(size)| == size
	ensures forall i :: 0 <= i < size ==> emptyLists<T>(size)[i] == []
	ensures flatten<T>(emptyLists<T>(size)) == []
{
	if size == 0 then
		[]
	else
		[[]] + emptyLists(size - 1)
}

function flatten<T>(sequences : seq<seq<T>>) : seq<T>
{
	if |sequences| == 0 then
		[]
	else
		sequences[0] + flatten(sequences[1..])
}

function firstNonEmpty<T>(sequences : seq<seq<T>>) : nat
	requires flatten<T>(sequences) != []
	ensures 0 <= firstNonEmpty<T>(sequences) < |sequences|
	ensures |sequences[firstNonEmpty<T>(sequences)]| > 0
	ensures forall k :: 0 <= k < |sequences| && sequences[k] != []
	==> firstNonEmpty<T>(sequences) <= k
{
	if sequences[0] != [] then
		0
	else
		1 + firstNonEmpty(sequences[1..])
}

function addTo<T>(sequences : seq<seq<T>>, priority : nat, value : T) : seq<seq<T>>
	requires 0 < priority <= |sequences|
	ensures |addTo(sequences, priority, value)| == |sequences|
	ensures |flatten(addTo(sequences, priority, value))| == |flatten(sequences)| + 1
	ensures forall i :: 0 <= i < |sequences| && i != index(priority) ==> addTo(sequences, priority, value)[i] == sequences[i]
	ensures addTo(sequences, priority, value)[index(priority)] == sequences[index(priority)] + [value] 
{
	var changeIndex := index(priority);
	if changeIndex == 0 then
		[sequences[0] + [value]] + sequences[1..]
	else
		[sequences[0]] + addTo(sequences[1..], priority - 1, value)
}

function removeFrom<T>(sequences : seq<seq<T>>, priority : nat) : seq<seq<T>>
	requires 0 < priority <= |sequences|
	requires |sequences[index(priority)]| > 0 
	ensures |removeFrom(sequences, priority)| == |sequences|
	ensures |flatten(removeFrom(sequences, priority))| == |flatten(sequences)| - 1
	ensures forall i :: 0 <= i < |sequences| && i != index(priority) ==> removeFrom(sequences, priority)[i] == sequences[i]
	ensures removeFrom(sequences, priority)[index(priority)] == sequences[index(priority)][1..]
{
	var changeIndex := index(priority);
	if changeIndex == 0 then
		[sequences[0][1..]] + sequences[1..]
	else
		[sequences[0]] + removeFrom(sequences[1..], priority - 1)
}

function method index(priority : nat) : nat
	requires 0 < priority
	ensures 0 <= index(priority)
{
	priority - 1
}

function priority(index : nat) : nat
	ensures 0 < priority(index)
{
	index + 1
}

lemma flattenEmptyImpliesAllEmpty<T>(sequences : seq<seq<T>>)
  ensures (|flatten(sequences)| == 0) <==>
	  (forall i :: 0 <= i < |sequences| ==> sequences[i] == [])
{
	if (|flatten(sequences)| == 0) {
		assert flatten(sequences) == [];
		if |sequences| == 0 {
			assert forall i :: 0 <= i < |sequences| ==> sequences[i] == [];
		} else {
			assert sequences[0] == [];
			flattenEmptyImpliesAllEmpty(sequences[1..]);
		}
	}
}
