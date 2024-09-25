include "Ex3.dfy"

module Ex4 {
  import Ex3=Ex3

  class Set {
    var list : Ex3.Node?

    ghost var footprint : set<Ex3.Node>
    ghost var content : set<nat>

    ghost function Valid() : bool 
      reads this, footprint, this.list
    {
      if (this.list == null)
        then 
          footprint == {}
          &&
          content == {}
        else 
          footprint == list.footprint
          &&
          content == list.content
          &&
          list.Valid()
    }

    constructor () 
      ensures Valid() && this.content == {} && this.footprint == {}
    {
      list := null; 
      footprint := {}; 
      content := {};      
    }


    method mem (v : nat) returns (b : bool)
      requires Valid()
      ensures b == (v in this.content)
    {
      b := false;
      if (this.list != null) {
        b := this.list.mem(v);
      }
      return;

      /*
        A condição "this !in this.next.footprint" na função Valid() da classe Node
        garante que não há ciclos numa lista válida. Se houvesse, teria de ser possível
        chegar a "this" a partir de um dos nós seguintes. Como para um nó ser válido, ele não
        pode estar no footprint do nó seguinte, não pode haver ciclos.

        O método mem da classe Node percorre a lista até ao fim. Sendo que não há ciclos,
        o método termina e nunca visita um mesmo nó duas vezes. Assim sendo, percorre
        no máximo O(n) nós
      */
    }


    method add (v : nat)
      requires Valid()
      ensures Valid()
      ensures this.content == {v} + old(this.content)
      ensures this.footprint == {this.list} + old(this.footprint)
      modifies this // do we need to say it modifies footprint?
    {
      if (this.list == null) {
        var n := new Ex3.Node(v); // Criar um nó é O(1)
        this.list := n; // Associar o nó à lista é O(1)

        // this.list == null ==> this.add(v) in O(1)
      } 
      else {
        this.list := this.list.add(v);

        /*
          O método add da classe Node está em O(1), pois só cria
          um nó, mete-o a apontar para a antiga cabeça da lista
          e atualiza cada ghost var com um assignment O(1)

          this.list != null ==> this.add(v) in O(1)
        */
      }
      this.footprint := this.list.footprint; // O(1)
      this.content := this.list.content; // O(1)

      /*
        this.add(v) in O(1)
        Qualquer função em O(1) está em O(n)
      */
    }

    method copy() returns (r : Set)
      requires Valid()
      ensures r.Valid()
      ensures r.content == this.content
      ensures fresh(r)
    {
      r := new Set();
      if (this.list != null) {
        r.list := this.list.copy();
        r.footprint := r.list.footprint;
        r.content := r.list.content;
      }
      return;
    }


    method union(s : Set) returns (r : Set)
      requires Valid() && s.Valid()
      ensures r.Valid()
      ensures r.content == this.content + s.content
      ensures r.footprint == this.footprint + s.footprint
    {
      /* Se o set não está vazio, então a união dele com outro tem, pelo menos, 
      todos os elementos desse set */
      r := this.copy();

      var curr := s.list;
      while (curr != null)
        invariant curr != null ==> curr.Valid()
        invariant s.Valid() && this.Valid()
        invariant r.Valid()
        decreases if (curr != null)
                    then curr.footprint
                  else {}
      {
        var inR := r.mem(curr.val); // O(n)
        if (!inR) {
          r.add(curr.val); // O(1)
        }
        curr := curr.next; // O(1)
      }

      return;
    }


  method inter(s : Set) returns (r : Set)
    {
      

    }
  }

}

