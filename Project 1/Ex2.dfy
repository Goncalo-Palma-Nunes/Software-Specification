function inBounds(i: nat, arr: array<nat>) : bool {
  if (0 <= i && i < arr.Length)
    then true
    else false
}

method noRepetitionsQuadratic(arr : array<nat>) returns (b: bool) 
   ensures forall i: nat, j: nat :: (inBounds(i, arr) && // Given any two indices of arr
                           inBounds(j, arr) && // iff they are different, the mapped values differ
                           i != j) 
                           <==> // if and only if
                           (inBounds(i, arr) &&
                           inBounds(j, arr) &&
                           arr[i] != arr[j])
 {
  var i := 0; 
  b := true; 

  while (i < arr.Length)
    // Problema quando i = 0? 0 <= k1 < 0  ---> contradição?
    // Invariante: Tudo até ao i (exclusive) não está repetido no array
    invariant forall k1: nat, k2: nat :: (
      (0 <= k1 < i && k1 < arr.Length && 0 <= k2 < arr.Length && k1 != k2)
      <==> // if and only if
      (0 <= k1 < i && k1 < arr.Length && 0 <= k2 < arr.Length && arr[k1] != arr[k2])
    )
  {

    var v := arr[i];   
    var j := 0;
  
    while (j < arr.Length)
      //  Invariante: Tudo até ao j (exclusive), com j != i, não é i igual a arr[i]
      invariant forall k: nat :: (0 <= k < j && j != i) <==> (k < arr.Length && arr[k] != arr[i])
    {
      var u := arr[j]; 
      if ((j != i) && (u == v)) {
        b := false; 
        return; 
      }
      j := j+1;
    }
    i := i+1; 
  }
}




method noRepetitionsLinear(arr : array<nat>) returns (b: bool)
{
}
