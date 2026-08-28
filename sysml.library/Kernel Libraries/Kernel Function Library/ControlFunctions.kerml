standard library package ControlFunctions {
	doc
	/*
	 * This package defines functions that correspond to operators in the KerML expression notation 
	 * for which one or more operands are expressions whose evaluation is determined by another operand.
	 */

	private import Base::Anything;
	private import ScalarValues::ScalarValue;
	private import ScalarValues::Boolean;
	private import ScalarFunctions::min;
	private import ScalarFunctions::max;
	private import Assertion::Lean;

	abstract function '.' {
		in feature source : Anything[0..*] nonunique {
	  		abstract feature target : Anything[0..*] nonunique;
	  	}
	  	private feature chain chains source.target;
	    chain
		// No @Lean: this represents KerML's own dot-chain FeatureChaining syntax
		// (source.target) itself, not a runtime function -- there is no generic
		// "any feature access" concept in Lean4SFS to point at, unlike every
		// other function in this file, which computes over already-modeled
		// List/Bool values.
	}

	abstract function 'if' {
		in test: Boolean[1];
		in expr thenValue[0..1] { return : Anything[0..*] ordered nonunique; }
		in expr elseValue[0..1] { return : Anything[0..*] ordered nonunique; }
		return : Anything[0..*] ordered nonunique;
		@Lean{l="cond";}
	}

	abstract function '??' {
		in firstValue: Anything[0..*] ordered nonunique;
		in expr secondValue[0..1] { return : Anything[0..*] ordered nonunique; }
		return : Anything[0..*] ordered nonunique;
		@Lean{l="fun a b => if a.isEmpty then b else a";}
	}

	function 'and' {
		in firstValue: Boolean[1];
		in expr secondValue[0..1] { return : Boolean[1]; }
		return : Boolean[1];
		@Lean{l="and";}
	}

	function 'or'{
		in firstValue: Boolean[1];
		in expr secondValue[0..1] { return : Boolean[1]; }
		return : Boolean[1];
		@Lean{l="or";}
	}

	function 'implies'{
		in firstValue: Boolean[1];
		in expr secondValue[0..1] { return : Boolean[1]; }
		return : Boolean[1];
		@Lean{l="fun a b => !a || b";}
	}

	abstract function collect {
		in collection: Anything[0..*] ordered nonunique;
		in expr mapper[0..*] { in argument: Anything[1]; return : Anything[0..*] ordered nonunique; }
		return : Anything[0..*] ordered nonunique;
		@Lean{l="List.map";}
	}

	abstract function select {
		in collection: Anything[0..*] ordered nonunique;
		in expr selector[0..*] { in argument: Anything[1]; return : Boolean[1]; }
		return : Anything[0..*] ordered nonunique;
		@Lean{l="List.filter";}
	}

	function selectOne {
		in collection: Anything[0..*] ordered nonunique;
		in expr selector1[0..*] { in argument: Anything[1]; return : Boolean[1]; }
//SFS get error: Invocation expression must invoke a `Behavior` or a feature typed by a single `Behavior`sysideinvocation-expression-instantiated-type
		return : Anything[0..1]; // = collection->select {in x; selector1(x)}#(1);
		@Lean{l="List.find?";}
	}

	abstract function reject{
		in collection: Anything[0..*] ordered nonunique;
		in expr rejector[0..*] { in argument: Anything[1]; return : Boolean[1]; }
		return : Anything[0..*] ordered nonunique;
		@Lean{l="fun l p => l.filter (fun x => !p x)";}
	}

	abstract function reduce {
		in collection: Anything[0..*] ordered nonunique;
		in expr reducer[0..*] { in firstArg: Anything[1]; in secondArg: Anything[1]; return : Anything[1]; }
		return : Anything[0..*] ordered nonunique;
		// No List.foldl1 in Lean core (fold-without-seed); lambda mirrors the KerML
		// signature's own "empty in, empty out" shape via Option instead of a seed value.
		@Lean{l="fun l f => match l with | [] => none | x :: xs => some (xs.foldl f x)";}
	}

	abstract function forAll {
		in collection: Anything[0..*] ordered nonunique;
		in expr test[0..*] { in argument: Anything[1]; return : Boolean[1]; }
		return : Boolean[1];
		@Lean{l="List.all";}
	}

	abstract function exists {
		in collection: Anything[0..*] ordered nonunique;
		in expr test[0..*] { in argument: Anything[1]; return : Boolean[1]; }
		return : Boolean[1];
		@Lean{l="List.any";}
	}

	function allTrue {
		in collection: Boolean[0..*];
		return : Boolean[1] = collection->forAll {in x; x};
		@Lean{l="List.and";}
	}

	function anyTrue {
		in collection: Boolean[0..*];
		return : Boolean[1] = collection->exists {in x; x};
		@Lean{l="List.or";}
	}
	
	function minimize {
		in collection: ScalarValue[1..*];
		in expr fn[0..*] { in argument: ScalarValue[1]; return : ScalarValue[1]; }
//SFS get error: Invocation expression must invoke a `Behavior` or a feature typed by a single `Behavior`sysideinvocation-expression-instantiated-type
		return : ScalarValue[1];  // = collection->collect {in x; fn(x as ScalarValue)}->reduce min;
//		return : ScalarValue[1] = collection->collect {in x; fn(x)}->reduce min;
		@Lean{l="fun collection fn => (collection.map fn).min?";}
	}

	function maximize {
		in collection: ScalarValue[1..*];
		in expr fn[0..*] { in argument: ScalarValue[1]; return : ScalarValue[1]; }
//SFS get error: Invocation expression must invoke a `Behavior` or a feature typed by a single `Behavior`sysideinvocation-expression-instantiated-type
		return : ScalarValue; // = collection->collect {in x; fn(x as ScalarValue)}->reduce max;
//		return : ScalarValue = collection->collect {in x; fn(x)}->reduce max;
		@Lean{l="fun collection fn => (collection.map fn).max?";}
	}
	
}