standard library package TrigFunctions {
	doc
	/*
	 * This package defines basic trigonometric functions on real numbers.
	 */

	public import ScalarValues::Real;
	private import Assertion::Lean;

	feature pi : Real {
		@Lean{l="Real.pi";}
	}
	inv piPrecision { RealFunctions::round(pi * 1E20) == 314159265358979323846.0 }

	function deg { in theta_rad : Real[1];
		return : Real[1] = theta_rad * 180 / pi;
		@Lean{l="fun theta_rad => theta_rad * 180 / Real.pi";}
	}
	function rad { in theta_deg : Real;
		return : Real[1] = theta_deg * pi / 180;
		@Lean{l="fun theta_deg => theta_deg * Real.pi / 180";}
	}

	datatype UnitBoundedReal :> Real {
		inv unitBound { -1.0 <= that & that <= 1.0 }
	}

	function sin { in theta : Real[1]; return : UnitBoundedReal[1];
		@Lean{l="Real.sin";}
	}
	function cos { in theta : Real[1]; return : UnitBoundedReal[1];
		@Lean{l="Real.cos";}
	}
	function tan { in theta : Real[1];
        return : Real = sin(theta) / cos(theta);
		@Lean{l="Real.tan";}
	}
	function cot { in theta : Real;
        return : Real = cos(theta) / sin(theta);
		@Lean{l="Real.cot";}
	}

	function arcsin { in x : UnitBoundedReal[1]; return : Real[1];
		@Lean{l="Real.arcsin";}
	}
	function arccos { in x : UnitBoundedReal[1]; return : Real[1];
		@Lean{l="Real.arccos";}
	}
	function arctan { in x : Real[1]; return : Real[1];
		@Lean{l="Real.arctan";}
	}
}