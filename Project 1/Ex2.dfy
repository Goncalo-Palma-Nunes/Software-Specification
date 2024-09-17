function inBounds(i: nat, arr: array<nat>) : bool {
  if (0 <= i && i < arr.Length)
    then true
    else false
}

method noRepetitionsQuadratic(arr : array<nat>) returns (b: bool) 
  ensures b == true ==> forall i: nat, j: nat :: 
                        inBounds(i, arr) && inBounds(j, arr) && i != j
                        ==> arr[i] != arr[j]
  ensures b == false ==> forall i: nat, j: nat :: 
                          inBounds(i, arr) && inBounds(j, arr) && arr[i] != arr[j]
                          ==> i != j
 {
  var i := 0; 
  b := true; 

  while (i < arr.Length)
    // Invariante: Tudo até ao i (exclusive) não está repetido no array
    invariant 0 <= i <= arr.Length
    invariant forall k1, k2 :: (0 <= k1 < i && 0 <= k2 < arr.Length && k1 != k2)
                              ==> arr[k1] != arr[k2]
  {

    var v := arr[i];   
    var j := 0;
  
    while (j < arr.Length)
      //  Invariante: Tudo, até ao j (exclusive), não é i igual a arr[i]
      invariant 0 <= j <= arr.Length
      invariant forall k :: (0 <= k < j && k != i) ==> arr[k] != arr[i]
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
  b := true; 
  var j := 0;

  var max_val := 0;
  var min_val := 0;
  while (j < arr.Length) // O(n) - One pass through array
    invariant 0 <= j <= arr.Length
  {
    var v := arr[j]; 
    if (v > max_val) {
       max_val := v;
    }
    if (v < min_val) {
       min_val := v;
    }
    j := j+1;
  }
  
  j := 0;
  // Podemos assumir max_val como uma constante / muito menor que n?
  var table := new bool[max_val + 1](x => false); // O(max_val) - Initialize table

  while (j < arr.Length) // O(n) - One pass through array
    invariant 0 <= j <= arr.Length
  {
    var v := arr[j]; 
    if (table[v]) {
      b := false; 
      return; 
    }
    table[v] := true;
    j := j+1;
  }

  // O(n) + O(n) + O(max_val) = O(max(n, max_val))  
}
