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
  {

    var v := arr[i];   
    var j := 0;
  
    while (j < arr.Length) 
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
