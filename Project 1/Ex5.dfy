include "Ex3.dfy"

module Ex5 {
  
  import Ex3=Ex3

  function allFalse(tbl : array<bool>) : bool
    reads tbl
  {
    forall i :: 0 <= i < tbl.Length ==> !tbl[i]
  }

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
          &&
          !allFalse(this.tbl)
          &&
          ((this.list.val in this.content) <==> this.tbl[this.list.val])
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
      requires Valid()
      ensures b == (v in this.content)
    {
      b := false;
      if (v < this.tbl.Length) {
        b := this.tbl[v]; // O(1) lookup
      }

      return;
    }
    
    method add (v : nat)
      requires Valid()
      ensures Valid()
      // Se o valor é válido, então a tabela tem de estar a true
      ensures v < this.tbl.Length ==> this.tbl[v]
      // Se o valor é válido, então o valor do nó é o valor
      ensures v < this.tbl.Length ==> this.list.val == v
      // Se o valor já está no set, então continua a estar
      ensures v in old(this.content) ==> v in this.content
      // Se o valor é válido, então estará no set
      ensures v < this.tbl.Length ==> v in this.content
      // Se o valor é inválido, nada muda
      ensures v >= this.tbl.Length ==> 
                        (
                          this.content == old(this.content)
                          && this.footprint == old(this.footprint)
                        )
      ensures fresh(this.footprint - old(this.footprint))
      modifies this.tbl, this
    {
      if (v >= this.tbl.Length) {
        return;
      }

      var n: Ex3.Node;
      if (this.list == null) {
        n := new Ex3.Node(v); // O(1)
      } 
      else {
        if (this.tbl[v]) {
          assert v in this.content;
          return;
        }
        n := this.list.add(v); // O(1)
      }
      this.list := n;
      this.tbl[v] := true; // O(1)
      this.content := this.list.content;
      this.footprint := this.list.footprint;
      return;
    }

    method union(s : Set) returns (r : Set)
    {
    }

    method inter(s : Set) returns (r : Set)
    {
    }

  }

}