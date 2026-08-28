standard library package RationalFunctions {
	doc
	/*
	 * This package defines Functions on Rational values, including concrete specializations of the 
	 * general arithmetic and comparison operations.
	 */

	public import ScalarValues::*;
	private import Assertion::Lean;

	function rat { in numer: Integer[1]; in denum: Integer[1]; return : Rational[1];
		@Lean{l="Rat.divInt";} }
	function numer { in rat: Rational[1]; return : Integer[1];
		@Lean{l="Rat.num";} }
	function denom { in rat: Rational[1]; return : Integer[1];
		@Lean{l="Rat.den";} }

	function abs specializes RealFunctions::abs { in x: Rational[1]; return : Rational[1];
		@Lean{l="Rat.abs";} }

	function '+' specializes RealFunctions::'+' { in x: Rational[1]; in y: Rational[0..1]; return : Rational[1];
		@Lean{l="Rat.add";} }
	function '-' specializes RealFunctions::'-' { in x: Rational[1]; in y: Rational[0..1]; return : Rational[1];
		@Lean{l="Rat.sub";} }
	function '*' specializes RealFunctions::'*' { in x: Rational[1]; in y: Rational[1]; return : Rational[1];
		@Lean{l="Rat.mul";} }
	function '/' specializes RealFunctions::'/' { in x: Rational[1]; in y: Rational[1]; return : Rational[1];
		@Lean{l="Rat.div";} }
	function '**' specializes RealFunctions::'**' { in x: Rational[1]; in y: Natural[1]; return : Rational[1];
		doc /* exponent narrowed to Natural: a Rational base raised to a non-natural Rational
		 * power need not itself be Rational (no HPow instance for Rational^Rational) */
		@Lean{l="HPow.hPow";}
	}
	function '^' specializes RealFunctions::'^' { in x: Rational[1]; in y: Natural[1]; return : Rational[1];
		doc /* exponent narrowed to Natural: a Rational base raised to a non-natural Rational
		 * power need not itself be Rational (no HPow instance for Rational^Rational) */
		@Lean{l="HPow.hPow";}
	}

	function '<' specializes RealFunctions::'<' { in x: Rational[1]; in y: Rational[1]; return : Boolean[1];
		@Lean{l="Rat.blt";} }
	function '>' specializes RealFunctions::'>' { in x: Rational[1]; in y: Rational[1]; return : Boolean[1];
		@Lean{l="fun a b => Rat.blt b a";} }
	function '<=' specializes RealFunctions::'<=' { in x: Rational[1]; in y: Rational[1]; return : Boolean[1];
		@Lean{l="fun a b => !Rat.blt b a";} }
	function '>=' specializes RealFunctions::'>=' { in x: Rational[1]; in y: Rational[1]; return : Boolean[1];
		@Lean{l="fun a b => !Rat.blt a b";} }

	function max specializes RealFunctions::max { in x: Rational[1]; in y: Rational[1]; return : Rational[1];
		@Lean{l="max";} }
	function min specializes RealFunctions::min { in x: Rational[1]; in y: Rational[1]; return : Rational[1];
		@Lean{l="min";} }

	function '==' specializes RealFunctions::'==' { in x: Rational[0..1]; in y: Rational[0..1]; return : Boolean[1];
		@Lean{l="decEq";} }

	function gcd{ in x: Rational[1]; in y: Rational[1]; return : Integer[1];
		doc /* no @Lean: gcd of two arbitrary Rationals is not a standard Mathlib notion --
		 * every nonzero Rational is a unit in the field ℚ, so "gcd" here has no
		 * canonical meaning the way it does for Integer/Natural */
	}

	function floor specializes RealFunctions::floor { in x: Rational[1]; return : Integer[1];
		@Lean{l="Rat.floor";} }
	function round specializes RealFunctions::round { in x: Rational[1]; return : Integer[1];
		@Lean{l="round";} }

	function ToString specializes RealFunctions::ToString { in x: Rational[1]; return : String[1];
		@Lean{l="toString";} }
	function ToInteger{ in x: Rational[1]; return : Integer[1];
		@Lean{l="round";} }
	function ToRational{ in x: String[1]; return : Rational[1];
		@Lean{l="fun s => match s.splitOn \"/\" with"+
			" | [n, d] => mkRat n.toInt! d.toNat!"+
			" | _ => mkRat s.toInt! 1";} }

	function sum specializes RealFunctions::sum { in collection: Rational[0..*];
		return : Rational[1] default NumericalFunctions::sum0(collection, rat(0, 1));
		@Lean{l="List.sum";}
	}

	function product specializes RealFunctions::product { in collection: Rational[0..*];
		return : Rational[1] default NumericalFunctions::product1(collection, rat(1, 1));
		@Lean{l="List.prod";}
	}
}
