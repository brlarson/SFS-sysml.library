standard library package BooleanFunctions {
	doc
	/*
	 * This package defines functions on Boolean values, including those corresponding to 
	 * (non-conditional) logical operators in the KerML expression notation.
	 */

	public import ScalarValues::*;
	private import Assertion::Lean;

	function 'not' specializes ScalarFunctions::'not' { in x: Boolean[1]; return : Boolean[1];
		@Lean{l="Bool.not";} }
	function 'xor' specializes ScalarFunctions::'xor' { in x: Boolean[1]; in y: Boolean[1]; return : Boolean[1];
		@Lean{l="Bool.xor";} }

	function '|' specializes ScalarFunctions::'|' { in x: Boolean[1]; in y: Boolean[1]; return : Boolean[1];
		@Lean{l="Bool.or";} }
	function '&' specializes ScalarFunctions::'&' { in x: Boolean[1]; in y: Boolean[1]; return : Boolean[1];
		@Lean{l="Bool.and";} }

	function '==' specializes DataFunctions::'==' { in x: Boolean[0..1]; in y: Boolean[0..1]; return : Boolean[1];
		@Lean{l="Bool.decEq";} }

	function ToString specializes BaseFunctions::ToString { in x: Boolean[1]; return : String[1];
		@Lean{l="fun b => if b then \"true\" else \"false\"";} }
	function ToBoolean { in x: String[1]; return : Boolean[1];
		@Lean{l="fun s => s == \"true\"";} }

}
	
