function inBounds(i: nat, arr: array<nat>) : bool {
  if (0 <= i && i < arr.Length)
    then true
    else false
}

method noRepetitionsQuadratic(arr : array<nat>) returns (b: bool) 
  // ensures b ==> forall i: nat, j: nat :: 
  //                       inBounds(i, arr) && inBounds(j, arr) && i != j
  //                       ==> arr[i] != arr[j]
  ensures !b ==> exists i: nat, j: nat :: 
                        inBounds(i, arr) && inBounds(j, arr) && arr[i] == arr[j] && i != j
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
   ensures b ==> forall i: nat, j: nat :: 
                         inBounds(i, arr) && inBounds(j, arr) && i != j
                         ==> arr[i] != arr[j]
  ensures !b ==> exists i: nat, j: nat :: 
                        inBounds(i, arr) && inBounds(j, arr) && arr[i] == arr[j] && i != j
{
  if (arr[..] == []) {
    b := true;
    return;
  }

  var j := 0;

  var max_val := arr[0];
  var min_val := arr[0];
  while (j < arr.Length) // O(n) - One pass through array
    invariant 0 <= j <= arr.Length
    // Tudo o que vimos até agora é no máximo max_val
    invariant forall k :: (0 <= k < j) ==> arr[k] <= max_val
    // Tudo o que vimos até agora é no mínimo min_val
    invariant forall k :: (0 <= k < j) ==> arr[k] >= min_val
    invariant max_val >= min_val
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
  var table := new bool[max_val + 1](x => false);

  while (j < arr.Length) // O(n) - One pass through array
    invariant 0 <= j <= arr.Length
    // Se o valor num índice do array ainda não visto é verdade na tabela,
    // então existe esse valor num índice anterior já visto
    invariant forall k :: ((k >= j) && (k < arr.Length) && table[arr[k]] ==>
                      exists k1 :: (0 <= k1 < j) && arr[k1] == arr[k])
    // Quaisqueres dois índices k e k1 já vistos, o valor nesses índices é diferente
    invariant forall k, k1 :: (0 <= k < j && 0 <= k1 < j && k != k1) ==> arr[k] != arr[k1]
    // Se vimos um número k, então existe um índice de arr já visto onde esse número está
    invariant forall k :: (0 <= k < max_val) && table[k]
                      ==> exists k1 :: (0 <= k1 < j) && arr[k1] == k               
    // Se ainda não vimos uma entrada k, então a tabela diz que não vimos
    invariant exists k :: ((k > j) && (k < arr.Length) ==> !table[arr[k]])
    // Tudo o que vimos até agora está a true na tabela
    invariant forall k :: (0 <= k < j) ==> table[arr[k]]
  {
    var v := arr[j];
    if (table[v]) {
      b := false; 
      return;
    }
    table[v] := true;
    j := j+1;
  }

  // O(n) + O(n) = O(n)  

  assert j == arr.Length;

  b := true;
  return;
}
