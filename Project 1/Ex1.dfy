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
{
	if (cs == [])
	then aes
	else reconstruct(cs[1..], reconstructAux(cs[0], aes))
}

function reconstructAux (cd : code, aes: seq<aexpr>) : seq<aexpr> {
  match cd {
    case VarCode(s) => [Var(s)] + aes
	case ValCode(i) => [Val(i)] + aes
	case UnOpCode(op) =>
		if |aes| < 1 then [ ]
		else [ UnOp(op, aes[0]) ] + aes[1..]
	case BinOpCode(op) =>
		if |aes| < 2 then [ ]
		else [ BinOp(op, aes[1], aes[0]) ] + aes[2..]
  }
}


/*
  Ex1.2
*/
lemma DeserializeProperty(e : aexpr)
  ensures Deserialize(Serialize(e)) == [ e ]
{
	match e {
		case Var(s) => 
			calc {
				Deserialize(Serialize(e));
				== // by case
				Deserialize(Serialize(Var(s)));
				== // by def of Serialize
				Deserialize([VarCode(s)]);
				== // unfolding Deserialize definition
				reconstruct([VarCode(s)], []);
				== // unfolding reconstruct definition
				reconstruct([], [Var(s)] + []);
				== // properties of sequences
				reconstruct([], [Var(s)]);
				== // defintion of reconstruct
				[Var(s)];
				== // by case
				[e];
			}
	}
}

lemma ReconstructAfterSerializingLemma (t : aexpr, cds : seq<code>, ts : seq<aexpr>) 
  ensures reconstruct(Serialize(t)+cds, ts) == reconstruct(cds, [ t ] + ts) {

	match t {
		case Var(s) => 
			calc {
				reconstruct(Serialize(t)+cds, ts);
				== // by case
				reconstruct(Serialize(Var(s))+cds, ts);
				== // by unfolding def of Serialize
				reconstruct([VarCode(s)]+cds, ts);
				== // by unfolding def of reconstruct
				reconstruct(cds, [Var(s)]+ts);
				== // by case
				reconstruct(cds, [t]+ts);
			}
		case Val(i) =>
			calc {
				reconstruct(Serialize(t)+cds, ts);
				== // by case
				reconstruct(Serialize(Val(i))+cds, ts);
				== // by unfolding def of Serialize
				reconstruct([ValCode(i)]+cds, ts);
				== // by unfolding def of reconstruct
				reconstruct(cds, [Val(i)]+ts);
				== // by case
				reconstruct(cds, [t]+ts);
			}
		case UnOp(op, expr) =>
			calc {
				reconstruct(Serialize(t)+cds, ts);
				== // by case
				reconstruct(Serialize(UnOp(op, expr)) + cds, ts);
				== // by unfolding def of Serialize
				reconstruct(Serialize(expr) + [UnOpCode(op)] + cds, ts);
				//==
			}
		case BinOp(op, expr1, expr2) =>
		    assert Serialize(expr2) + Serialize(expr1) + [ BinOpCode(op) ] + cds == Serialize(expr2) + (Serialize(expr1) + [ BinOpCode(op) ] + cds);
			assert Serialize(expr1) + [BinOpCode(op)] + cds == Serialize(expr1) + ([BinOpCode(op)] + cds); 
			assert  [ expr1 ] + ([ expr2 ] + ts) == [ expr1, expr2] + ts;
			calc {
				reconstruct(Serialize(t)+cds, ts);
				== // by case
				reconstruct(Serialize(BinOp(op, expr1, expr2)) + cds, ts);
				== // by unfolding def of Serialize
				reconstruct(Serialize(expr2) + Serialize(expr1) + [BinOpCode(op)] + cds, ts);
				== { ReconstructAfterSerializingLemma(expr2, Serialize(expr1) + [BinOpCode(op)] + cds, ts); }
				reconstruct(Serialize(expr1) + [BinOpCode(op)] + cds, [expr2] + ts);
				== { ReconstructAfterSerializingLemma(expr1, [BinOpCode(op)] + cds, [expr2] + ts); }
				reconstruct([BinOpCode(op)] + cds, [expr1] + ([expr2] + ts));
				== // properties of sequences
				reconstruct([BinOpCode(op)] + cds, [expr1, expr2] + ts);
				== // by unfolding def of reconstruct
				reconstruct(cds, [BinOp(op, expr1, expr2)] + ts);
				== // by case
				reconstruct(cds, [t] + ts);
			}
	}
}

// /*
//   Ex1.3
// */
// function SerializeCodes(cs : seq<code>) : seq<nat> 
// {

// }

// function DeserializeCodes(ints : seq<nat>) : seq<code> {
  
// }


// /*
//   Ex1.4
// */
// lemma DeserializeCodesProperty(cs : seq<code>)
//   ensures DeserializeCodes(SerializeCodes(cs)) == cs
// {
// }

// /*
//   Ex1.5
// */
// function FullSerialize(e : aexpr) : seq<nat> {
 
// }

// function FullDeserealize(nats : seq<nat>) : seq<aexpr> {
 
// }

// /*
//   Ex1.6
// */
// lemma FullDeserealizeProperty(e : aexpr)
//   ensures FullDeserealize(FullSerialize(e)) == [ e ]
// {
    
// }
