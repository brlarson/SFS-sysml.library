standard library package ComplexFunctions {
	doc
	/*
	 * This package defines functions on Complex values, including concrete specializations of the 
	 * general arithmetic and comparison operations.
	 */

	public import ScalarValues::*;
	private import Assertion::Lean;
		
	feature i: Complex[1] = rect(0.0, 1.0);
	
	function rect { in re: Real[1]; in im: Real[1]; return : Complex[1];
		@Lean{l="Complex.mk";} }
	function polar { in abs: Real[1]; in arg: Real[1]; return : Complex[1];
		doc /* abs * e^(i * arg) */
		@Lean{l="fun abs arg => (↑abs : ℂ) * Complex.exp (↑arg * Complex.I)";} }
	
	function re { in x: Complex[1]; return : Real[1];
		@Lean{l="Complex.re";} }
	function im { in x: Complex[1]; return : Real[1];
		@Lean{l="Complex.im";} }
	
	function isZero specializes NumericalFunctions::isZero { in x : Complex[1];
		return : Boolean[1] = re(x) == 0.0 and im(x) == 0.0;
		@Lean{l="fun x => x = (0 : ℂ)";}
	}
	function isUnit specializes NumericalFunctions::isUnit { in x : Complex[1];
		return : Boolean[1] = re(x) == 1.0 and im(x) == 0.0;
		@Lean{l="fun x => x = (1 : ℂ)";}
	}
	
	function abs specializes NumericalFunctions::abs { in x: Complex[1]; return : Real[1];
		@Lean{l="Complex.norm";} }
	function arg { in x: Complex[1]; return : Real[1];
		@Lean{l="Complex.arg";} }
	
	function '+' specializes NumericalFunctions::'+' { in x: Complex[1]; in y: Complex[0..1]; return : Complex[1]; 
		@Lean{l="Complex.add";} }
	function '-' specializes NumericalFunctions::'-' { in x: Complex[1]; in y: Complex[0..1]; return : Complex[1];
		@Lean{l="Complex.sub";} }
	function '*' specializes NumericalFunctions::'*' { in x: Complex[1]; in y: Complex[1]; return : Complex[1];
		@Lean{l="Complex.mul";} }
	function '/' specializes NumericalFunctions::'/' { in x: Complex[1]; in y: Complex[1]; return : Complex[1];
		@Lean{l="Complex.div";} }
	function '**' specializes NumericalFunctions::'**' { in x: Complex[1]; in y: Complex[1]; return : Complex[1];
		@Lean{l="Complex.cpow";} }
	function '^' specializes NumericalFunctions::'^' { in x: Complex[1]; in y: Complex[1]; return : Complex[1];
		@Lean{l="Complex.cpow";} }
	
	function '==' specializes DataFunctions::'==' { in x: Complex[0..1]; in y: Complex[0..1]; return : Boolean[1];
		@Lean{l="Complex.decEq";} }
	
	function ToString specializes BaseFunctions::ToString { in x: Complex[1]; return : String[1];
		@Lean{l="fun x => toString x.re ++ \" + \" ++ toString x.im ++ \"*I\"";} }
	function ToComplex { in x: String[1]; return : Complex[1];
		@Lean{l="fun s => match s.splitOn \" + \" with | [r, i] => Complex.mk r.toFloat! (i.dropRight 2).toFloat! | _ => 0";} }
	
	function sum specializes NumericalFunctions::sum { in collection: Complex[0..*];
		return : Complex[1] default NumericalFunctions::sum0(collection, rect(0.0, 0.0));
		@Lean{l="List.sum";}
	}

	function product specializes NumericalFunctions::product { in collection: Complex[0..*];
		return : Complex[1] default NumericalFunctions::product1(collection, rect(1.0, 0.0));
		@Lean{l="List.prod";}
	}
}
