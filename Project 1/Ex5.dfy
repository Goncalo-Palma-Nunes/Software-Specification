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
          (forall v : nat :: v in this.content <==> 0 <= v < this.tbl.Length && this.tbl[v])
          &&
          (forall n : Ex3.Node :: n in this.footprint ==> 
                                    && n.val in this.content
                                    && n in this.list.footprint
                                    && this.tbl[n.val])
          &&
          (forall i : nat :: 0 <= i < this.tbl.Length ==>
                (this.tbl[i] == (exists n : Ex3.Node :: n in this.footprint && n.val == i))
                &&
                (this.tbl[i] == (i in this.content))
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
      requires Valid() && v < this.tbl.Length
      ensures Valid()
      ensures this.tbl.Length == old(this.tbl.Length)
      ensures this.tbl[v]
      ensures v in this.content
      ensures fresh(this.footprint - old(this.footprint))
      ensures old(this.tbl) == this.tbl
      modifies this.tbl, this
    {
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
      ensures fresh(r.footprint)
      ensures r.footprint != this.footprint && r.footprint != s.footprint
      ensures r.content == this.content + s.content
    {
      // find largest table
      var bigger := max(this.tbl.Length, s.tbl.Length);
      r := new Set(bigger);

      var curr := this.list;
      while (curr != null)
        invariant this.Valid()
        invariant r.Valid()
        invariant curr != null ==> curr.val in this.content && curr.Valid()
        invariant curr != null ==> r.content == this.content - curr.content
        invariant curr == null ==> r.content == this.content
        invariant r.footprint!!this.footprint
        invariant fresh(r.footprint)
        decreases if (curr != null)
                    then curr.footprint
                  else {}
      {
        r.add(curr.val);
        curr := curr.next;
      }

      curr := s.list;
      while (curr != null)
        invariant s.Valid()
        invariant r.Valid()
        invariant curr != null ==> curr.val in s.content && curr.Valid()
        invariant curr != null ==> r.content == this.content + (s.content - curr.content)
        invariant curr != null ==> curr.val in s.content
        invariant curr == null ==> r.content == this.content + s.content
        invariant r.footprint!!s.footprint && r.footprint!!this.footprint
        invariant fresh(r.footprint)
        decreases if (curr != null)
                    then curr.footprint
                  else {}
      {
        r.add(curr.val);
        curr := curr.next;
      }
    }

    method inter(s : Set) returns (r : Set)
      requires this.Valid() && s.Valid()
      ensures r.Valid()
      ensures r.content == this.content * s.content
      ensures fresh(r.footprint)
    {
      var biggest := max(this.tbl.Length, s.tbl.Length);
      r := new Set(biggest);

      var curr := this.list;
      var seen := new Set(biggest);
      while (curr != null)
        invariant curr != null ==> curr.Valid()
        invariant s.Valid()
        invariant r.Valid()
        invariant curr != null ==> this.content == seen.content + curr.content
        invariant fresh(r.footprint)
        invariant curr == null ==> r.content == this.content * s.content
        invariant curr != null ==>
                  forall v : nat :: v in r.content ==> v in this.content * s.content
        invariant curr != null ==> 
                  forall v : nat :: v in this.content * s.content && v !in curr.content ==> v in r.content
        decreases if (curr != null)
                    then curr.footprint
                  else {}
      {
        var inS := s.mem(curr.val);
        if (inS) {
          r.add(curr.val);
        }
        seen.add(curr.val);
        curr := curr.next;
      }
    }

  }

}
