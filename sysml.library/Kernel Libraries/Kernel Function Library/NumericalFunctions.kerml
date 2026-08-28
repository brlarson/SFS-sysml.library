standard library package NumericalFunctions {
	doc
	/*
	 * This package defines abstract functions on Numerical values for general arithmetic and comparison operations.
	 */

	public import ScalarValues::*;
	private import ControlFunctions::reduce;
	private import Assertion::Lean;


	abstract function isZero{ in x: NumericalValue[1]; return : Boolean;
		@Lean{l="fun x => x = Zero.zero";} }
	abstract function isUnit{ in x : NumericalValue[1]; return : Boolean;
		@Lean{l="fun x => x = One.one";} }

	abstract function abs{ in x: NumericalValue[1]; return : NumericalValue[1];
		@Lean{l="abs";} }

	abstract function '+' specializes ScalarFunctions::'+' { in x: NumericalValue[1]; in y: NumericalValue[0..1]; return : NumericalValue[1];
		@Lean{l="Add.add";} }
	abstract function '-' specializes ScalarFunctions::'-' { in x: NumericalValue[1]; in y: NumericalValue[0..1]; return : NumericalValue[1];
		@Lean{l="Sub.sub";} }
	abstract function '*' specializes ScalarFunctions::'*' { in x: NumericalValue[1]; in y: NumericalValue[1]; return : NumericalValue[1];
		@Lean{l="Mul.mul";} }
	abstract function '/' specializes ScalarFunctions::'/' { in x: NumericalValue[1]; in y: NumericalValue[1]; return : NumericalValue[1];
		@Lean{l="Div.div";} }
	abstract function '**' specializes ScalarFunctions::'**' { in x: NumericalValue[1]; in y: NumericalValue[1]; return : NumericalValue[1];
		@Lean{l="HPow.hPow";} }
	abstract function '^' specializes ScalarFunctions::'^' { in x: NumericalValue[1]; in y: NumericalValue[1]; return : NumericalValue[1];
		@Lean{l="HPow.hPow";} }
	abstract function '%' specializes ScalarFunctions::'%' { in x: NumericalValue[1]; in y: NumericalValue[1]; return : NumericalValue[1];
		@Lean{l="Mod.mod";} }
	abstract function 'div' specializes ScalarFunctions::'div' { in x: NumericalValue[1]; in y: NumericalValue[1]; return : NumericalValue[1];
		@Lean{l="Div.div";} }

	abstract function '<' specializes ScalarFunctions::'<' { in x: NumericalValue[1]; in y: NumericalValue[1]; return : Boolean[1];
		@Lean{l="fun x y => decide (x < y)";} }
	abstract function '>' specializes ScalarFunctions::'>' { in x: NumericalValue[1]; in y: NumericalValue[1]; return : Boolean[1];
		@Lean{l="fun x y => decide (y < x)";} }
	abstract function '<=' specializes ScalarFunctions::'<=' { in x: NumericalValue[1]; in y: NumericalValue[1]; return : Boolean[1];
		@Lean{l="fun x y => decide (x ≤ y)";} }
	abstract function '>=' specializes ScalarFunctions::'>=' { in x: NumericalValue[1]; in y: NumericalValue[1]; return : Boolean[1];
		@Lean{l="fun x y => decide (y ≤ x)";} }

	abstract function max specializes ScalarFunctions::max { in x: NumericalValue[1]; in y: NumericalValue[1]; return : NumericalValue[1];
		@Lean{l="max";} }
	abstract function min specializes ScalarFunctions::min { in x: NumericalValue[1]; in y: NumericalValue[1]; return : NumericalValue[1];
		@Lean{l="min";} }

	abstract function sum { in collection: NumericalValue[0..*]; return : NumericalValue[1];
		@Lean{l="List.sum";} }
	abstract function product { in collection: NumericalValue[0..*]; return : NumericalValue[1];
		@Lean{l="List.prod";} }
	
	function sum0 { in collection: NumericalValue[0..*]; in zero: NumericalValue[1];
 		inv { isZero(zero as NumericalValue) }
// 		inv { isZero(zero) }
        return : NumericalValue = collection->reduce '+' ?? zero;
		@Lean{l="fun collection zero => collection.foldl Add.add zero";}
	}

	function product1 { in collection: NumericalValue[0..*]; in one: NumericalValue[1];
		inv { isUnit(one as NumericalValue) }
//		inv { isUnit(one) }
        return : NumericalValue = collection->reduce '*' ?? one;
		@Lean{l="fun collection one => collection.foldl Mul.mul one";}
	}
}