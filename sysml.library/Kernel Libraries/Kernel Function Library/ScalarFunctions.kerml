standard library package ScalarFunctions {
	doc
	/*
	 * This package defines abstract functions that specialize the DataFunctions for use with ScalarValues. 
	 */

	public import ScalarValues::*;
	private import Assertion::Lean;

	abstract function '+' specializes DataFunctions::'+' { in x: ScalarValue[1]; in y: ScalarValue[0..1]; return : ScalarValue[1];
		@Lean{l="Add.add";} }
	abstract function '-' specializes DataFunctions::'-' { in x: ScalarValue[1]; in y: ScalarValue[0..1]; return : ScalarValue[1];
		@Lean{l="Sub.sub";} }
	abstract function '*' specializes DataFunctions::'*' { in x: ScalarValue[1]; in y: ScalarValue[1]; return : ScalarValue[1];
		@Lean{l="Mul.mul";} }
	abstract function '/' specializes DataFunctions::'/' { in x: ScalarValue[1]; in y: ScalarValue[1]; return : ScalarValue[1];
		@Lean{l="Div.div";} }
	abstract function '**' specializes DataFunctions::'**' { in x: ScalarValue[1]; in y: ScalarValue[1]; return : ScalarValue[1];
		@Lean{l="HPow.hPow";} }
	abstract function '^' specializes DataFunctions::'^' { in x: ScalarValue[1]; in y: ScalarValue[1]; return : ScalarValue[1];
		@Lean{l="HPow.hPow";} }
	abstract function '%' specializes DataFunctions::'%' { in x: ScalarValue[1]; in y: ScalarValue[1]; return : ScalarValue[1];
		@Lean{l="Mod.mod";} }
	abstract function 'div' { in x: ScalarValue[1]; in y: ScalarValue[1]; return : ScalarValue[1];
		@Lean{l="Div.div";} }

	abstract function 'not' specializes DataFunctions::'not' { in x: ScalarValue[1]; return : ScalarValue[1];
		@Lean{l="Complement.complement";} }
	abstract function 'xor' specializes DataFunctions::'xor' { in x: ScalarValue[1]; in y: ScalarValue[1]; return : ScalarValue[1];
		@Lean{l="XorOp.xor";} }

	abstract function '~' specializes DataFunctions::'~' { in x: ScalarValue[1]; return : ScalarValue[1];
		@Lean{l="Complement.complement";} }
	abstract function '|' specializes DataFunctions::'|' { in x: ScalarValue[1]; in y: ScalarValue[1]; return : ScalarValue[1];
		@Lean{l="OrOp.or";} }
	abstract function '&' specializes DataFunctions::'&' { in x: ScalarValue[1]; in y: ScalarValue[1]; return : ScalarValue[1];
		@Lean{l="AndOp.and";} }

	abstract function '<' specializes DataFunctions::'<' { in x: ScalarValue[1]; in y: ScalarValue[1]; return : Boolean[1];
		@Lean{l="fun x y => decide (x < y)";} }
	abstract function '>' specializes DataFunctions::'>' { in x: ScalarValue[1]; in y: ScalarValue[1]; return : Boolean[1];
		@Lean{l="fun x y => decide (y < x)";} }
	abstract function '<=' specializes DataFunctions::'<=' { in x: ScalarValue[1]; in y: ScalarValue[1]; return : Boolean[1];
		@Lean{l="fun x y => decide (x ≤ y)";} }
	abstract function '>=' specializes DataFunctions::'>=' { in x: ScalarValue[1]; in y: ScalarValue[1]; return : Boolean[1];
		@Lean{l="fun x y => decide (y ≤ x)";} }

	abstract function max specializes DataFunctions::max { in x: ScalarValue[1]; in y: ScalarValue[1]; return : ScalarValue[1];
		@Lean{l="max";} }
	abstract function min specializes DataFunctions::min { in x: ScalarValue[1]; in y: ScalarValue[1]; return : ScalarValue[1];
		@Lean{l="min";} }

	abstract function '..' specializes DataFunctions::'..' { in lower: ScalarValue[1]; in upper: ScalarValue[1]; return : ScalarValue[0..*];
		doc /* Finset.Icc requires LocallyFiniteOrder (and transitively Preorder), which
		 * an arbitrary unordered ScalarValue is not guaranteed to have */
		@Lean{l="Finset.Icc";}
	}
}