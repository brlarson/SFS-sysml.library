standard library package RealFunctions {
	doc
	/*
	 * This package defines Functions on Real values, including concrete specializations of the 
	 * general arithmetic and comparison operations.
	 */

	public import ScalarValues::*;
	private import Assertion::Lean;

	function re :> ComplexFunctions::re{ in x: Real[1];
        return : Real[1] = x;
        @Lean{l="id";}
	}
	function im :> ComplexFunctions::im{ in x: Real[1];
        return : Real[1] = 0.0;
        @Lean{l="fun _ => (0 : ℝ)";}
	}

	function abs specializes ComplexFunctions::abs { in x: Real[1]; return : Real[1];
		@Lean{l="abs";} }
	function arg specializes ComplexFunctions::arg { in x: Real[1];
        return : Real[1] = 0.0;
        @Lean{l="fun _ => (0 : ℝ)";}
	}

	function '+' specializes ComplexFunctions::'+' { in x: Real[1]; in y: Real[0..1]; return : Real[1];
		@Lean{l="Real.add";} }
	function '-' specializes ComplexFunctions::'-' { in x: Real[1]; in y: Real[0..1]; return : Real[1];
		@Lean{l="Real.sub";} }
	function '*' specializes ComplexFunctions::'*' { in x: Real[1]; in y: Real[1]; return : Real[1];
		@Lean{l="Real.mul";} }
	function '/' specializes ComplexFunctions::'/' { in x: Real[1]; in y: Real[1]; return : Real[1];
		@Lean{l="Real.div";} }
	function '**' specializes ComplexFunctions::'**' { in x: Real[1]; in y: Real[1]; return : Real[1];
		@Lean{l="Real.rpow";} }
	function '^' specializes ComplexFunctions::'^' { in x: Real[1]; in y: Real[1]; return : Real[1];
		@Lean{l="Real.rpow";} }

	function '<' specializes NumericalFunctions::'<' { in x: Real[1]; in y: Real[1]; return : Boolean[1];
		@Lean{l="Real.decidableLT";} }
	function '>' specializes NumericalFunctions::'>' { in x: Real[1]; in y: Real[1]; return : Boolean[1];
		@Lean{l="fun x y => Real.decidableLT y x";} }
	function '<=' specializes NumericalFunctions::'<=' { in x: Real[1]; in y: Real[1]; return : Boolean[1];
		@Lean{l="Real.decidableLE";} }
	function '>=' specializes NumericalFunctions::'>=' { in x: Real[1]; in y: Real[1]; return : Boolean[1];
		@Lean{l="fun x y => Real.decidableLE y x";} }

	function max specializes NumericalFunctions::max { in x: Real[1]; in y: Real[1]; return : Real[1];
		@Lean{l="max";} }
	function min specializes NumericalFunctions::min { in x: Real[1]; in y: Real[1]; return : Real[1];
		@Lean{l="min";} }

	function '==' specializes ComplexFunctions::'==' { in x: Real[0..1]; in y: Real[0..1]; return : Boolean[1];
		@Lean{l="Real.decidableEq";} }

	function sqrt{ in x: Real[1]; return : Real[1];
		@Lean{l="Real.sqrt";} }

	function floor{ in x: Real[1]; return : Integer[1];
		@Lean{l="Int.floor";} }
	function round{ in x: Real[1]; return : Integer[1];
		@Lean{l="round";} }

	function ToString specializes ComplexFunctions::ToString { in x: Real[1]; return : String[1];
		@Lean{l="fun x => toString (Int.floor x) ++ \".\" ++ toString (Int.floor ((x - Int.floor x) * 1000000))";} }
	function ToInteger{ in x: Real[1]; return : Integer[1];
		@Lean{l="round";} }
	function ToRational{ in x: Real[1]; return : Rational[1]; }
	function ToReal{ in x: String[1]; return : Real[1];
		@Lean{l="fun s => match s.splitOn \".\" with"+
			" | [w, f] => ((w.toInt! : ℚ) + (f.toNat! : ℚ) / 10 ^ f.length : ℝ)"+
			" | _ => (s.toInt! : ℝ)";} }

	function sum specializes ComplexFunctions::sum { in collection: Real[0..*];
        return : Real default NumericalFunctions::sum0(collection, 0.0);
        @Lean{l="List.sum";}
	}

	function product specializes ComplexFunctions::product { in collection: Real[0..*];
        return : Real default NumericalFunctions::product1(collection, 1.0);
        @Lean{l="List.prod";}
	}
}
