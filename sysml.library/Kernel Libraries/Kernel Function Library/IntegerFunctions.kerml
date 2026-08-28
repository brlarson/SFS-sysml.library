standard library package IntegerFunctions {
	doc
	/*
	 * This package defines functions on Integer values, including concrete specializations of the 
	 * general arithmetic and comparison operations.
	 */

	public import ScalarValues::*;
	private import Assertion::Lean;

	function abs specializes RationalFunctions::abs { in x: Integer[1]; return : Natural[1];
		@Lean{l="Int.natAbs";} }

	function '+' specializes RationalFunctions::'+' { in x: Integer[1]; in y: Integer[0..1]; return : Integer[1];
		@Lean{l="Int.add";} }
	function '-' specializes RationalFunctions::'-' { in x: Integer[1]; in y: Integer[0..1]; return : Integer[1];
		@Lean{l="Int.sub";} }
	function '*' specializes RationalFunctions::'*' { in x: Integer[1]; in y: Integer[1]; return : Integer[1];
		@Lean{l="Int.mul";} }
	function '/' specializes RationalFunctions::'/' { in x: Integer[1]; in y: Integer[1]; return : Rational[1];
		@Lean{l="fun x y => (x : ℚ) / (y : ℚ)";} }
	function 'div' specializes NumericalFunctions::'div' { in x: Integer[1]; in y: Integer[1]; return : Integer[1];
		@Lean{l="Int.ediv";} }
	function '**' specializes RationalFunctions::'**' { in x: Integer[1]; in y: Natural[1]; return : Integer[1];
		@Lean{l="Int.pow";} }
	function '^' specializes RationalFunctions::'^' { in x: Integer[1]; in y: Natural[1]; return : Integer[1];
		@Lean{l="Int.pow";} }
	function '%' specializes NumericalFunctions::'%' { in x: Integer[1]; in y: Integer[1]; return : Integer[1];
		@Lean{l="Int.emod";} }

	function '<' specializes RationalFunctions::'<' { in x: Integer[1]; in y: Integer[1]; return : Boolean[1];
		@Lean{l="Int.decLt";} }
	function '>' specializes RationalFunctions::'>' { in x: Integer[1]; in y: Integer[1]; return : Boolean[1];
		@Lean{l="fun x y => Int.decLt y x";} }
	function '<=' specializes RationalFunctions::'<=' { in x: Integer[1]; in y: Integer[1]; return : Boolean[1];
		@Lean{l="Int.decLe";} }
	function '>=' specializes RationalFunctions::'>=' { in x: Integer[1]; in y: Integer[1]; return : Boolean[1];
		@Lean{l="fun x y => Int.decLe y x";} }

	function max specializes RationalFunctions::max { in x: Integer[1]; in y: Integer[1]; return : Integer[1];
		@Lean{l="max";} }
	function min specializes RationalFunctions::min { in x: Integer[1]; in y: Integer[1]; return : Integer[1];
		@Lean{l="min";} }

	function '==' specializes DataFunctions::'==' { in x: Integer[0..1]; in y: Integer[0..1]; return : Boolean[1];
		@Lean{l="Int.decEq";} }

	function '..' specializes ScalarFunctions::'..' { in lower: Integer[1]; in upper: Integer[1]; return : Integer[0..*];
		@Lean{l="Finset.Icc";} }

	function ToString specializes RationalFunctions::ToString { in x: Integer[1]; return : String[1];
		@Lean{l="toString";} }
	function ToNatural { in x: Integer[1]; return : Natural[1];
		@Lean{l="Int.toNat";} }
	function ToInteger { in x: String[1]; return : Integer[1];
		@Lean{l="String.toInt?";} }

	function sum specializes RationalFunctions::sum { in collection: Integer[0..*];
		return : Integer[1] default NumericalFunctions::sum0(collection, 0);
		@Lean{l="List.sum";}
	}

	function product specializes RationalFunctions::product { in collection: Integer[0..*];
		return : Integer[1] default NumericalFunctions::product1(collection, 1);
		@Lean{l="List.prod";}
	}
}
