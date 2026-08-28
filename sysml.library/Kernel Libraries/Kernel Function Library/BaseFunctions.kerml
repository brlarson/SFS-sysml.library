standard library package BaseFunctions {
	doc
	/*
	 * This package defines a basic set of functions defined on all kinds of values. 
	 * Most correspond to similarly named operators in the KerML expression syntax.
	 */

	private import Base::Anything;
	private import Objects::Object;
	private import Metaobjects::Metaobject;
	private import KerML::Metaclass;
	private import ScalarValues::*;
	private import Assertion::Lean;

	abstract function '=='{ in x: Anything[0..1]; in y: Anything[0..1];
		return : Boolean[1];
		@Lean{l="BEq.beq";}
	}
	function '!='{ in x: Anything[0..1]; in y: Anything[0..1];
		return : Boolean[1] = not (x == y);
		@Lean{l="fun x y => !BEq.beq x y";}
	}

	abstract function '==='{ in x: Anything[0..1]; in y: Anything[0..1];
		return : Boolean[1];
		@Lean{l="ptrEq";}
	}
	function '!=='{ in x: Anything[0..1]; in y: Anything[0..1];
		return : Boolean[1] = not (x === y);
		@Lean{l="fun x y => !ptrEq x y";}
	}

	abstract function ToString{ in x: Anything[0..1];
		return : String;
		@Lean{l="toString";}
	}
	
	abstract function '['{ in x: Anything[0..*] nonunique; in y: Anything[0..*] nonunique;
		return : Anything[0..*] nonunique;
		// No @Lean: the operator's exact intended semantics aren't clear enough from
		// this signature alone (two arbitrary sequences in, one out) to ground even a
		// best-effort lambda.
	}
	abstract function '#'{ in seq: Anything[0..*] ordered nonunique; in index: Positive[1..*] ordered nonunique;
		return : Anything[0..1];
		// No @Lean: multi-index chained access over Anything, which Lean4SFS models as
		// an opaque type (no concrete List/indexable structure to fold over, unlike
		// SequenceFunctions::'#''s single-index sibling, which operates on a real
		// modeled List).
	}
	abstract function ','{ in seq1: Anything[0..*] ordered nonunique; in seq2: Anything[0..*] ordered nonunique;
		return : Anything[0..*] ordered nonunique;
		@Lean{l="List.append";}
	}

    abstract function 'all'{
     	return : Object[0..*];
		// No @Lean: this is a model query ("every Object that exists"), not a
		// computation over inputs -- there is no notion of "every value of a type" as
		// a finite runtime list in Lean4SFS's model (it has no operands to compute
		// from at all).
    }

	abstract function 'istype'{
		in seq: Anything[0..*];
		in 'type': Anything;
		return : Boolean[1];
		// No @Lean: a dynamic runtime type-classification check ("is this value
		// classified by type"). Lean's type system is static, and Lean4SFS
		// deliberately doesn't model KerML's reflective metamodel (classification,
		// metaclasses, ...) -- there is no real Lean/Mathlib concept of dynamic
		// classification membership to point at.
	}

	abstract function 'hastype'{
		in seq: Anything[0..*];
		in 'type': Anything;
		return : Boolean;
		// No @Lean: same reflective/dynamic-classification category as 'istype' above.
	}

	abstract function '@'{
		in seq: Anything[0..*];
		in 'type': Anything;
		return : Boolean[1];
		// No @Lean: same reflective/dynamic-classification category as 'istype' above.
	}

	abstract function '@@'{
		in seq: Metaobject[0..*];
		in 'type': Metaobject;
		return : Boolean[1];
		// No @Lean: same reflective/dynamic-classification category as 'istype' above,
		// at the metaobject level.
	}

	abstract function 'as'{
		in seq: Anything[0..*] ordered nonunique;
		return : Anything[0..*] ordered nonunique;
		// No @Lean for type coersion
	}

	abstract function 'meta'{
		in seq: Metaobject[0..*] ordered nonunique;
		return : Metaobject[0..*] ordered nonunique;
		// No @Lean: extracts the metaobject-level representation of a sequence
		// (KerML reflection) -- no metaobject/reflection layer is modeled in
		// Lean4SFS to build a real reference against.
	}

}