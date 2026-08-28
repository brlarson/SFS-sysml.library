standard library package NaturalFunctions {
	doc
	/*
	 * This package defines functions on Natural values, including concrete specialization of the 
	 * general arithmetic and comparison operations.
	 *  SFS:  "/" changed to "div"
	 */

	public import ScalarValues::*;
	private import Assertion::Lean;

	function '+' specializes IntegerFunctions::'+' { in x: Natural[1]; in y: Natural[0..1]; return : Natural[1];
		@Lean{l="Nat.add";} }
	function '*' specializes IntegerFunctions::'*' { in x: Natural[1]; in y: Natural[1]; return : Natural[1];
		@Lean{l="Nat.mul";} }
	function 'div' specializes IntegerFunctions::'div' { in x: Natural[1]; in y: Natural[1]; return : Natural[1];
		@Lean{l="Nat.div";} }
	function '%' specializes IntegerFunctions::'%' { in x: Natural[1]; in y: Natural[1]; return : Natural[1];
		@Lean{l="Nat.mod";} }

	function '<' specializes IntegerFunctions::'<' { in x: Natural[1]; in y: Natural[1]; return : Boolean[1];
		@Lean{l="Nat.decLt";} }
	function '>' specializes IntegerFunctions::'>' { in x: Natural[1]; in y: Natural[1]; return : Boolean[1];
		@Lean{l="fun x y => Nat.decLt y x";} }
	function '<=' specializes IntegerFunctions::'<=' { in x: Natural[1]; in y: Natural[1]; return : Boolean[1];
		@Lean{l="Nat.decLe";} }
	function '>=' specializes IntegerFunctions::'>=' { in x: Natural[1]; in y: Natural[1]; return : Boolean[1];
		@Lean{l="fun x y => Nat.decLe y x";} }

	function max specializes IntegerFunctions::max { in x: Natural[1]; in y: Natural[1]; return : Natural[1];
		@Lean{l="max";} }
	function min specializes IntegerFunctions::min { in x: Natural[1]; in y: Natural[1]; return : Natural[1];
		@Lean{l="min";} }

	function '==' specializes IntegerFunctions::'==' { in x: Natural[0..1]; in y: Natural[0..1]; return : Boolean[1];
		@Lean{l="Nat.decEq";} }

	function ToString specializes IntegerFunctions::ToString { in x: Natural[1]; return : String[1];
		@Lean{l="Nat.repr";} }
	function ToNatural{ in x: String[1]; return : Natural[1];
		@Lean{l="String.toNat?";} }
}
