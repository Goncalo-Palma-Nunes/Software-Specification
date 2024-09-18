datatype uop = Neg 
datatype bop = Plus | Minus 

datatype aexpr =
  Var(seq<nat>)
  | Val(nat)
  | UnOp(uop, aexpr)
  | BinOp(bop, aexpr, aexpr)
 
datatype code = 
  | VarCode(seq<nat>)  
  | ValCode(nat)       
  | UnOpCode(uop)      
  | BinOpCode(bop)     

function Serialize(a : aexpr) : seq<code> 
{
  match a {
    case Var(s) => [ VarCode(s) ]
    case Val(i) => [ ValCode(i) ]
    case UnOp(op, a1) => Serialize(a1) + [ UnOpCode(op) ]
    case BinOp(op, a1, a2) => Serialize(a2) + Serialize(a1) + [ BinOpCode(op) ]
  }
}


/*
  Ex1.1
*/
function Deserialize(cs : seq<code>) : seq<aexpr> 
{
	reconstruct(cs, [])
}

function reconstruct(cs : seq<code>, aes : seq<aexpr>) : seq<aexpr>
	decreases cs, aes
	requires forall k : int :: 0 <= k < cs.Length && cs[k].UnOpCode? 
	 ==> aes.Length > 0 // TODO idk if this works or necessary TODO
	requires forall k : int :: 0 <= k < cs.Length && cs[k].BinOpCode? 
	 ==> aes.Length > 1 // TODO possibly not necessary
{
	if (cs == [])
	then aes
	else
		match cs[0] {
			case VarCode(s) => reconstruct(cs[1..], [Var(s)] + aes)
			case ValCode(i) => reconstruct(cs[1..], [Val(i)] + aes)
			case UnOpCode(op) => reconstruct(cs[1..], [UnOp(op, aes[0])] + aes[1..])
			case BinOpCode(op) => reconstruct(cs[1..], [BinOp(op, aes[0], aes[1])] + aes[2..])
		}
}


/*
  Ex1.2
*/
lemma DeserializeProperty(e : aexpr)
  ensures Deserialize(Serialize(e)) == [ e ]
{
	calc {
		Deserialize(Serialize(e));
		== { deserializePropertyAux(e, [], []); }
	}
}

lemma deserializePropertyAux(e : aexpr, cs : seq<code>, aes : seq<aexpr>)
	ensures reconstruct(Serialize(e) + cs, ts) == reconstruct(cs, [e] + ts)
	// ensures Deserialize(Serialize(e)+cs) == Deserialize(cs) + [e] // idk if this is preferable
{
	match e {
		// base case??
		case Var(s) => 
		 calc {
			reconstruct(Serialize(e) + cs, ts);
			==
			reconstruct(Serialize(Var(s)) + cs, ts); // by case
			==
			reconstruct([VarCode(s)] + cs, ts); // by def of Serialize
			==
			reconstruct(cs, [Var(s)] + ts); // by def of reconstruct
			==
			reconstruct(cs, [e] + ts); // by case
		 }
		case Val(i) =>
		 calc {
			reconstruct(Serialize(e) + cs, ts);
			==
			reconstruct(Serialize(Val(i)) + cs, ts); // by case
			==
			reconstruct([ValCode(i)] + cs, ts); // by def of Serialize
			==
			reconstruct(cs, [Val(i)] + ts); // by def of reconstruct
			==
			reconstruct(cs, [e] + ts); // by case
		 }
		// induction case
		case UnOp(op, expr) =>
		 // assert?
		 calc {
			reconstruct(Serialize(e) + cs, ts);
			==
			reconstruct(Serialize(UnOp(op, expr)) + cs, ts); // by case
			==
			reconstruct(Serialize(expr) + [UnOpCode(op)] + cs, ts); // def Serialize
			== { deserializePropertyAux(expr, [UnOpCode(op)]+cs, ts); }
			reconstruct([UnOpCode(op)] + cs, [expr] + ts); // IH
			==
			reconstruct(cs, [UnOp(op, expr)] + ts); // def reconstruct
			==
			reconstruct(cs, [e] + ts); // case
		 }
		case BinOp(op, expr1, expr2) =>
		 assert [expr1] + ([expr2] + ts) == [expr1, expr2] + ts;
		 calc {
			reconstruct(Serialize(e) + cs, ts);
			==
			reconstruct(Serialize(BinOp(op, expr1, expr2)) + cs, ts); // by case
			==
			reconstruct(Serialize(expr2) + Serialize(expr1) + [BinOpCode(op)] + cs, ts); // def Serialize
			== { deserializePropertyAux(expr2, (Serialize(expr1)+[BinOpCode(op)]+cs), ts); }
			reconstruct(Serialize(expr1) + [BinOpCode(op)] + cs, [expr2] + ts); // IH
			== { deserializePropertyAux(expr1, [BinOpCode(op)]+cs, [expr2] + ts); }
			reconstruct([BinOpCode(op)] + cs, [expr1] + ([expr2] + ts)); // IH
			==
			reconstruct([BinOpCode(op)] + cs, [expr1, expr2] + ts); // properties of sequences
			==
			reconstruct(cs, [BinOp(op, expr1, expr2)] + ts); // def reconstruct
			==
			reconstruct(cs, [e] + ts); // case
		 }
	}
}

/*
  Ex1.3
*/
function SerializeCodes(cs : seq<code>) : seq<nat> 
{

}

function DeserializeCodes(ints : seq<nat>) : seq<code> {
  
}


/*
  Ex1.4
*/
lemma DeserializeCodesProperty(cs : seq<code>)
  ensures DeserializeCodes(SerializeCodes(cs)) == cs
{
}

/*
  Ex1.5
*/
function FullSerialize(e : aexpr) : seq<nat> {
 
}

function FullDeserealize(nats : seq<nat>) : seq<aexpr> {
 
}

/*
  Ex1.6
*/
lemma FullDeserealizeProperty(e : aexpr)
  ensures FullDeserealize(FullSerialize(e)) == [ e ]
{
    
}
