standard library package DataFunctions {
	doc
	/*
	 * This package defines the abstract base functions corresponding to all the unary and binary operators 
	 * in the KerML expression notation that might be defined on various kinds of DataValues.
	 */

	private import Base::DataValue;
	private import ScalarValues::Boolean;
	private import ControlFunctions::reduce;
	private import Assertion::Lean;

	abstract function '==' specializes BaseFunctions::'==' { in x: DataValue[0..1]; in y: DataValue[0..1];
		return : Boolean[1];
		@Lean{l="BEq.beq";}
	}
	function '===' specializes BaseFunctions::'==='{ in x: DataValue[0..1]; in y: DataValue[0..1];
		return : Boolean[1] = x == y;
		doc /* @Lean points at the real but `unsafe` ptrEq primitive (pointer/reference
		 * identity) -- Lean's pure logic has no notion of object identity distinct
		 * from value equality (values are immutable), so this is an operational,
		 * not logical, match; note the body above still just delegates to == */
		@Lean{l="ptrEq";}
	}

	abstract function '+' { in x: DataValue[1]; in y: DataValue[0..1]; return : DataValue[1];
		@Lean{l="Add.add";} }
	abstract function '-' { in x: DataValue[1]; in y: DataValue[0..1]; return : DataValue[1];
		@Lean{l="Sub.sub";} }
	abstract function '*' { in x: DataValue[1]; in y: DataValue[1]; return : DataValue[1];
		@Lean{l="Mul.mul";} }
	abstract function '/' { in x: DataValue[1]; in y: DataValue[1]; return : DataValue[1];
		@Lean{l="Div.div";} }
	abstract function '**' { in x: DataValue[1]; in y: DataValue[1]; return : DataValue[1];
		@Lean{l="HPow.hPow";} }
	abstract function '^' { in x: DataValue[1]; in y: DataValue[1]; return : DataValue[1];
		@Lean{l="HPow.hPow";} }
	abstract function '%' { in x: DataValue[1]; in y: DataValue[1]; return : DataValue[1];
		@Lean{l="Mod.mod";} }

	abstract function 'not' { in x: DataValue[1]; return : DataValue[1];
		@Lean{l="Complement.complement";} }
	abstract function 'xor' { in x: DataValue[1]; in y: DataValue[1]; return : DataValue[1];
		@Lean{l="XorOp.xor";} }

	abstract function '~' { in x: DataValue[1]; return : DataValue[1];
		@Lean{l="Complement.complement";} }
	abstract function '|' { in x: DataValue[1]; in y: DataValue[1]; return : DataValue[1];
		@Lean{l="OrOp.or";} }
	abstract function '&' { in x: DataValue[1]; in y: DataValue[1]; return : DataValue[1];
		@Lean{l="AndOp.and";} }

	abstract function '<' { in x: DataValue[1]; in y: DataValue[1]; return : Boolean[1];
		@Lean{l="fun x y => decide (x < y)";} }
	abstract function '>' { in x: DataValue[1]; in y: DataValue[1]; return : Boolean[1];
		@Lean{l="fun x y => decide (y < x)";} }
	abstract function '<=' { in x: DataValue[1]; in y: DataValue[1]; return : Boolean[1];
		@Lean{l="fun x y => decide (x ≤ y)";} }
	abstract function '>=' { in x: DataValue[1]; in y: DataValue[1]; return : Boolean[1];
		@Lean{l="fun x y => decide (y ≤ x)";} }

	abstract function max { in x: DataValue[1]; in y: DataValue[1]; return : DataValue[1];
		@Lean{l="max";} }
	abstract function min { in x: DataValue[1]; in y: DataValue[1]; return : DataValue[1];
		@Lean{l="min";} }

	abstract function '..' { in lower: DataValue[1]; in upper: DataValue[1]; return : DataValue[0..*] ordered;
		doc /* Finset.Icc requires LocallyFiniteOrder (and transitively Preorder), which
		 * an arbitrary unordered DataValue is not guaranteed to have */
		@Lean{l="Finset.Icc";}
	}
}