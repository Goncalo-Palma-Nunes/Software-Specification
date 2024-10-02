include "Ex3.dfy"

module Ex5 {
  
  import Ex3=Ex3

  function allFalse(tbl : array<bool>) : bool
    reads tbl
  {
    forall i :: 0 <= i < tbl.Length ==> !tbl[i]
  }

  lemma existsTrue(tbl : array<bool>)
    requires exists i :: 0 <= i < tbl.Length && tbl[i]
    ensures allFalse(tbl) == false
    {
    }

  lemma 

  class Set {
    var tbl : array<bool>  
    var list : Ex3.Node?

    ghost var content : set<nat>
    ghost var footprint : set<Ex3.Node>

    ghost function Valid() : bool
      reads this, this.footprint, this.list, this.tbl
    {
      if (this.list == null)
        then 
          this.footprint == {}
          &&
          this.content == {}
          &&
          allFalse(this.tbl)
        else 
          this.footprint == this.list.footprint
          &&
          this.content == this.list.content
          &&
          this.list.val in this.content
          &&
          0 <= this.list.val < this.tbl.Length
          &&
          tbl[this.list.val]
          &&
          this.list.Valid()
    }
      
    constructor (size : nat)
      ensures Valid()
      ensures this.tbl.Length == size && forall i :: 0 <= i < size ==> !this.tbl[i]
      ensures this.list == null
      ensures this.content == {} && this.footprint == {}
    {
      tbl := new bool[size](x => false);
      list := null;

      content := {};
      footprint := {};
    }


    method mem (v : nat) returns (b : bool)
    {
    }
    
    method add (v : nat) 
    {
    }

    method union(s : Set) returns (r : Set)
    {
    }

    method inter(s : Set) returns (r : Set)
    {
    }

  }

}