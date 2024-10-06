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
		else [ BinOp(op, aes[0], aes[1]) ] + aes[2..]
  }
}


/*
  Ex1.2
*/
lemma DeserializeProperty(e : aexpr)
  ensures Deserialize(Serialize(e)) == [ e ]
{
	assert Serialize(e) + [] == Serialize(e);
	calc {
		Deserialize(Serialize(e));
		== // by def of Deserialize
		reconstruct(Serialize(e), []);
		== { ReconstructAfterSerializingLemma(e, [], []); }
		reconstruct([], [e]);
		== // by def of reconstruct
		[e];
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
			assert Serialize(expr) + [UnOpCode(op)] + cds == Serialize(expr) + ([UnOpCode(op)] + cds);
			calc {
				reconstruct(Serialize(t)+cds, ts);
				== // by case
				reconstruct(Serialize(UnOp(op, expr)) + cds, ts);
				== // by unfolding def of Serialize
				reconstruct(Serialize(expr) + [UnOpCode(op)] + cds, ts);
				== { ReconstructAfterSerializingLemma(expr, [UnOpCode(op)] + cds, ts); }
				reconstruct([UnOpCode(op)] + cds, [expr] + ts);
				== // by unfolding def of reconstruct
				reconstruct(cds, [UnOp(op, expr)] + ts);
				== // by case
				reconstruct(cds, [t] + ts);
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

/*
  Ex1.3
*/
function seqSize(s : seq<nat>) : nat
{
	if s == [] then 0
	else 1 + seqSize(s[1..])
}

function SerializeBop(op : bop) : seq<nat>
{
	match op {
		case Plus => [0]
		case Minus => [1]
	}
}

function SerializeUop(op : uop) : seq<nat>
{
	match op {
		case Neg => [0]
	}
}

function SerializeCodes(cs : seq<code>) : seq<nat> 
{
	if cs == [] then []
	else match cs[0] {
		// Para o VarCode o 0 é a tag e o tamanho do seq<nat> é o primeiro elemento seguinte
		case VarCode(s: seq<nat>) => [0] + [seqSize(s)] + s + SerializeCodes(cs[1..])
		case BinOpCode(op: bop) => [1] + SerializeBop(op) + SerializeCodes(cs[1..])
		case UnOpCode(op: uop) => [2] + SerializeUop(op) + SerializeCodes(cs[1..])
		case ValCode(i: nat) => [3] + [i] + SerializeCodes(cs[1..])
	}

}

function DeserializeBop(n: nat) : bop
{
	if n == 0 then Plus
	else Minus
}

function DeserializeUop(n: nat) : uop
{
	Neg
}

function DeserializeCodes(ints : seq<nat>) : seq<code> {
  if |ints| < 2 then [] // Ou vazio ou mal formado (Têm todos tag + algo)
  else match ints[0] {
    case 0 =>
	  var size := ints[1];
	  if |ints| < 2 + size then []
	  else
		[VarCode(ints[2..2+size])] + DeserializeCodes(ints[2+size..])
	case 1 => 
	  [BinOpCode(DeserializeBop(ints[1]))] + DeserializeCodes(ints[2..])
	case 2 => 
	  [UnOpCode(DeserializeUop(ints[1]))] + DeserializeCodes(ints[2..])
	case 3 => 
	  [ValCode(ints[1])] + DeserializeCodes(ints[2..])
	case _ => [] // Isto nunca acontece na realidade
  }
}


/*
  Ex1.4
*/
lemma DeserializeCodesProperty(cs : seq<code>)
  ensures DeserializeCodes(SerializeCodes(cs)) == cs


// lemma DeserializeCodesProperty(cs : seq<code>)
//   ensures DeserializeCodes(SerializeCodes(cs)) == cs
// {
//   if cs == [] {
//     calc {
//       DeserializeCodes(SerializeCodes(cs));
//       == // by case
//       DeserializeCodes(SerializeCodes([]));
//       == // by def of SerializeCodes
//       DeserializeCodes([]);
//       == // by def of DeserializeCodes
//       [];
//       == // by case
//       cs;
//     }
//   }
//   else {
//     calc {
//       DeserializeCodes(SerializeCodes(cs));
//     }
//   }
// }

/*
  Ex1.5
*/
function FullSerialize(e : aexpr) : seq<nat> {
 SerializeCodes(Serialize(e))
}

function FullDeserealize(nats : seq<nat>) : seq<aexpr> {
  Deserialize(DeserializeCodes(nats))
}

/*
  Ex1.6
*/
lemma FullDeserealizeProperty(e : aexpr)
  ensures FullDeserealize(FullSerialize(e)) == [ e ]
{
  match e {
    
    case Var(s) =>
      calc {
        FullDeserealize(FullSerialize(e));
        == // by case
        FullDeserealize(FullSerialize(Var(s)));
        == // by def of FullSerialize
        FullDeserealize(SerializeCodes(Serialize(Var(s))));
        == // by def of Serialize
        FullDeserealize(SerializeCodes([VarCode(s)]));
        == // by def of FullDeserealize
        Deserialize(DeserializeCodes(SerializeCodes([VarCode(s)])));
        == { DeserializeCodesProperty([VarCode(s)]); }
        Deserialize([VarCode(s)]);
        == { DeserializeProperty(Var(s)); }
        [Var(s)];
        == // by case
        [e];
      }
      case Val(i) =>
        calc {
          FullDeserealize(FullSerialize(e));
          == // by case
          FullDeserealize(FullSerialize(Val(i)));
          == // by def of FullSerialize
          FullDeserealize(SerializeCodes(Serialize(Val(i))));
          == // by def of Serialize
          FullDeserealize(SerializeCodes([ValCode(i)]));
          == // by def of FullDeserealize
          Deserialize(DeserializeCodes(SerializeCodes([ValCode(i)])));
          == { DeserializeCodesProperty([ValCode(i)]); }
          Deserialize([ValCode(i)]);
          == { DeserializeProperty(Val(i)); }
          [Val(i)];
          == // by case
          [e];
        }
      case UnOp(op, expr) =>
        calc {
          FullDeserealize(FullSerialize(e));
          == // by case
          FullDeserealize(FullSerialize(UnOp(op, expr)));
          == // by def of FullSerialize
          FullDeserealize(SerializeCodes(Serialize(UnOp(op, expr))));
          == // by def of Serialize
          FullDeserealize(SerializeCodes(Serialize(expr) + [UnOpCode(op)]));
          == // by def of FullDeserealize
          Deserialize(DeserializeCodes(SerializeCodes(Serialize(expr) + [UnOpCode(op)])));
          == { DeserializeCodesProperty(Serialize(expr) + [UnOpCode(op)]); }
          Deserialize(Serialize(expr) + [UnOpCode(op)]);
          == { DeserializeProperty(UnOp(op, expr)); }
          [UnOp(op, expr)];
          == // by case
          [e];
        }
      case BinOp(op, expr1, expr2) =>
        calc {
          FullDeserealize(FullSerialize(e));
          == // by case
          FullDeserealize(FullSerialize(BinOp(op, expr1, expr2)));
          == // by def of FullSerialize
          FullDeserealize(SerializeCodes(Serialize(BinOp(op, expr1, expr2))));
          == // by def of Serialize
          FullDeserealize(SerializeCodes(Serialize(expr2) + Serialize(expr1) + [BinOpCode(op)]));
          == // by def of FullDeserealize
          Deserialize(DeserializeCodes(SerializeCodes(Serialize(expr2) + Serialize(expr1) + [BinOpCode(op)])));
          == { DeserializeCodesProperty(Serialize(expr2) + Serialize(expr1) + [BinOpCode(op)]); }
          Deserialize(Serialize(expr2) + Serialize(expr1) + [BinOpCode(op)]);
          == { DeserializeProperty(BinOp(op, expr1, expr2)); }
          [BinOp(op, expr1, expr2)];
          == // by case
          [e];
        }
  }
}
