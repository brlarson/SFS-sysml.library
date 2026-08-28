standard library package StringFunctions {
	doc
	/*
	 * This package defines functions on String values, including those corresponding to string concatenation 
	 * and comparison operators in the KerML expression notation.
	 */

	public import ScalarValues::*;
	private import Assertion::Lean;

	function '+' specializes ScalarFunctions::'+' { in x: String[1]; in y:String[1]; return : String[1];
		@Lean{l="String.append";}
	}

	function Length{ in x: String[1]; return : Natural[1];
		@Lean{l="String.length";}
	}
	function Substring{ in x: String[1]; in lower: Integer[1]; in upper: Integer[1]; return : String[1];
		@Lean{l="fun s lower upper =>"+
			" String.ofList ((s.toList.drop (lower.toNat - 1)).take (upper.toNat - lower.toNat + 1))";}
	}

	function '<' specializes ScalarFunctions::'<' { in x: String[1]; in y: String[1]; return : Boolean[1];
		@Lean{l="String.decidableLT";}
	}
	function '>' specializes ScalarFunctions::'>' { in x: String[1]; in y: String[1]; return : Boolean[1];
		@Lean{l="fun x y => String.decidableLT y x";}
	}
	function '<=' specializes ScalarFunctions::'<=' { in x: String[1]; in y: String[1]; return : Boolean[1];
		@Lean{l="String.decLE";}
	}
	function '>=' specializes ScalarFunctions::'>=' { in x: String[1]; in y: String[1]; return : Boolean[1];
		@Lean{l="fun x y => String.decLE y x";}
	}

	function '==' specializes DataFunctions::'==' { in x: String[0..1]; in y: String[0..1]; return : Boolean[1];
		@Lean{l="String.decEq";}
	}

	function ToString specializes BaseFunctions::ToString { in x: String[1];
		return : String[1] = x;
		@Lean{l="id";}
	}
}
