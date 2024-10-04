
module Ex3 {

  class Node {

    var val : nat
    var next : Node?

    ghost var footprint : set<Node>
    ghost var content : set<nat> 

    ghost function Valid() : bool 
      reads this, this.footprint 
      decreases footprint
    {
      this in this.footprint 
      &&
      if (this.next == null)
        then 
          this.footprint == { this }
          && 
          this.content == { this.val }
        else 
          this.next in this.footprint
          &&
          this !in this.next.footprint
          &&      
          this.footprint == { this } + this.next.footprint 
          &&
          this.content == { this.val } + this.next.content
          &&
          this.next.Valid()
    }

    constructor (v : nat)
      ensures Valid()
      ensures this.val == v && this.next == null && this.content == {v} && this.footprint == {this}
    {
      this.val := v;
      this.next := null;
      this.footprint := {this};
      this.content := {v};
    }

    method add(v : nat) returns (r : Node)
      requires Valid()
      ensures r.Valid()
      ensures r.content == {v} + this.content && r.footprint == {r} + this.footprint
      ensures r.val == v
      ensures fresh(r)
    {
      r := new Node(v);
      r.next := this;

      r.footprint := {r} + this.footprint;
      r.content := {v} + this.content;
    }

    method mem(v : nat) returns (b : bool)
      requires Valid()
      ensures b == (v in this.content)
    {
      var curr := this;
      b := false;

      ghost var setAux: set<int> := {};
      while (curr != null)
        invariant curr != null ==> curr.Valid()
        invariant curr != null ==> this.content == setAux + curr.content
        invariant curr == null ==> this.content == setAux
        invariant v !in setAux
        decreases if (curr != null)
                    then curr.footprint
                  else {}
      {
        if (curr.val == v) {
          b := true;
          return;
        }
        setAux := setAux + {curr.val};
        curr := curr.next;
      }

      return;
    }

    method copy() returns (n : Node)
      requires Valid()
      ensures n.Valid()
      ensures n.content == this.content 
      ensures fresh(n) && fresh(n.footprint)
      decreases footprint
    {
      n := new Node(this.val);
      if (this.next != null) {
        var aux := this.next.copy(); 
        n.next := aux; 
        n.content := { n.val } + aux.content; 
        n.footprint := { n } + aux.footprint;
      }
    }

  }
}
