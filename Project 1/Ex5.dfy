include "Ex3.dfy"

module Ex5 {
  
  import Ex3=Ex3

  function allFalse(tbl : array<bool>) : bool
    reads tbl
  {
    forall i :: 0 <= i < tbl.Length ==> !tbl[i]
  }

  function max(a : nat, b : nat) : nat
  {
    if (a > b) then a else b
  }

  lemma maxComparison(a : nat, b : nat)
    ensures max(a, b) == a ==> a >= b
  {
  }

  lemma maxCommutativity(a : nat, b : nat)
    ensures max(a, b) == max(b, a)
  {
  }

  lemma maxTransitivity(a : nat, b : nat, c : nat)
    ensures max(a, b) == a && max(b, c) == b ==> max(a, c) == a
  {
  }

  lemma maxCeil(a : nat, b : nat)
    ensures max(a, b) >= a && max(a, b) >= b
          && (max(a, b) == a || max(a, b) == b)
  {
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
          this.list.Valid()
          &&
          (forall v : nat :: v in this.content <==> 0 <= v < this.tbl.Length && tbl[v])
          &&
          (forall n : Ex3.Node :: n in this.footprint ==> 
                                    && n.val in this.content
                                    && n in this.list.footprint
                                    && this.tbl[n.val])
          &&
          (forall v : nat :: v in this.content ==>
                v in this.list.content
                &&
                (exists n : Ex3.Node :: n in this.footprint && n.val == v 
                                        && n in this.list.footprint)
          )
          &&
          (forall i : nat :: 0 <= i < this.tbl.Length ==>
                (this.tbl[i] == (exists n : Ex3.Node :: n in this.footprint && n.val == i))
                &&
                (this.tbl[i] ==> i in this.content)
          ) 
    }
      
    constructor (size : nat)
      ensures Valid()
      ensures this.tbl.Length == size && (forall i :: 0 <= i < size ==> !this.tbl[i])
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
      ensures this.tbl.Length == old(this.tbl.Length)
      // Se o valor é válido, então a tabela tem de estar a true
      ensures v < this.tbl.Length ==> this.tbl[v]
      // Se o valor é válido, então o valor do nó é o valor
      ensures v < this.tbl.Length && !this.tbl[v] ==> this.list.val == v
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
      requires this.Valid() && s.Valid()
      ensures r.Valid()
      //ensures forall v :: 0 <= v < this.tbl.Length <= r.tbl.Length ==> this.tbl[v] ==> r.tbl[v]
      //ensures forall v :: 0 <= v < s.tbl.Length <= r.tbl.Length ==> s.tbl[v] ==> r.tbl[v]
      ensures fresh(r)
      ensures fresh(r.footprint)
      ensures r.footprint != this.footprint && r.footprint != s.footprint
      ensures r.content == this.content + s.content
    {
      // find largest table
      var bigger := max(this.tbl.Length, s.tbl.Length);
      r := new Set(bigger);

      var curr := this.list;
      assert r.tbl.Length == bigger;
      assert r.tbl.Length == max(this.tbl.Length, s.tbl.Length);
      assert r.tbl.Length >= this.tbl.Length;
      assert r.tbl.Length >= s.tbl.Length;
      assert r.tbl.Length == this.tbl.Length || r.tbl.Length == s.tbl.Length;
      while (curr != null)
        invariant fresh(r.footprint)
        invariant curr != null ==> curr.Valid()
        invariant this.Valid()
        invariant r.Valid()
        invariant this.content == old(this.content)
        invariant curr != null ==> r.content == this.content - curr.content
        invariant curr == null ==> r.content == this.content
        invariant r.footprint!!this.footprint && r.footprint!!s.footprint
        // invariant forall v :: 0 <= v < curr ==> this.tbl[v] ==> r.tbl[v]
        decreases if (curr != null)
                    then curr.footprint
                  else {}
      {
        r.add(curr.val);
        curr := curr.next;
      }
    }

    method inter(s : Set) returns (r : Set)
    {
    }

  }

}
