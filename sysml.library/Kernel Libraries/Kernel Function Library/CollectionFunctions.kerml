standard library package CollectionFunctions {
	doc
	/*
	 * This package defines functions on Collections (as defined in the Collections package). 
	 * For functions on general sequences of values, see the SequenceFunctions package.
	 */

	private import Base::Anything;
	private import ScalarValues::*;
	private import SequenceFunctions::equals;
	private import SequenceFunctions::includes;
	private import ControlFunctions::exists;
	private import Assertion::Lean;
	public import Collections::*;

	function '==' specializes BaseFunctions::'==' { in col1: Collection[0..1]; in col2: Collection[0..1];
		return : Boolean[1] = col1.elements->equals(col2.elements);
		@Lean{l="fun x y => x = y";}
	}

	function size { in col: Collection[1];
		return : Natural[1] = SequenceFunctions::size(col.elements);
		@Lean{l="List.length";}
	}

	function isEmpty { in col: Collection[1];
		return : Boolean[1] = SequenceFunctions::isEmpty(col.elements);
		@Lean{l="List.isEmpty";}
	}

	function notEmpty { in col: Collection[1];
		return : Boolean[1] = SequenceFunctions::notEmpty(col.elements);
		@Lean{l="fun seq => !List.isEmpty seq";}
	}

	function contains { in col: Collection[1]; in values: Anything[*];
		return : Boolean[1] = col.elements->includes(values);
		@Lean{l="fun seq1 seq2 => List.Subset seq2 seq1";}
	}

	function containsAll { in col1: Collection[1]; in col2: Collection[2];
		return : Boolean[1] = contains(col1, col2.elements);
		@Lean{l="fun seq1 seq2 => List.Subset seq2 seq1";}
	}

	function head { in col: OrderedCollection[1];
		return : Anything[0..1] = SequenceFunctions::head(col.elements);
		@Lean{l="List.head?";}
	}

	function tail { in col: OrderedCollection[1];
		return : Anything[0..*] ordered nonunique = SequenceFunctions::tail(col.elements);
		@Lean{l="List.tail";}
	}

	function last { in col: OrderedCollection[1];
		return : Anything[0..1] = SequenceFunctions::last(col.elements);
		@Lean{l="List.getLast?";}
	}

	function '#' specializes BaseFunctions::'#' { in col: OrderedCollection[1]; in index: Positive[1];
		// Cast ensures this function is not called recursively if the elements of col are OrderedCollections.
		return : Anything[0..1] = (col.elements as Anything)#(index);
		@Lean{l="fun seq i => seq[i - 1]?";}
	}
	
	function 'array#' specializes BaseFunctions::'#' { in arr: Array[1]; in indexes: Positive[n] ordered nonunique;		
		private feature n : Natural[1] = arr.rank;
		
		// Assumes row-major ordering for elements.
		private function index { in arr: Array[1]; in i : Natural; in indexes : Positive[1..*];
			if i <= 1? indexes#(1) else arr.dimensions#(i) * (index(arr, (i-1) as Natural, indexes) - 1) + indexes#(i)
//			if i <= 1? indexes#(1) else arr.dimensions#(i) * (index(arr, i-1, indexes) - 1) + indexes#(i)
		}
		
		return : Anything[0..1] =
			if n == 0 or (1..n)->exists {in i; indexes#(i) > arr.dimensions#(i)}? null
			else arr.elements#(index(arr, n, indexes));
		// No @Lean: Array's rank/dimensions/elements fields have no Lean4SFS counterpart to
		// build a real lambda against, and there's no Mathlib/Lean primitive for row-major
		// N-dimensional array flattening. Best-effort lambda below, NOT backed by any real
		// Mathlib definition, mirroring the recursive index() helper's own row-major
		// linear-offset formula (dims/indexes both taken as plain 0-indexed Lists here,
		// since neither Array itself nor 1-indexed access are modeled):
		@Lean{l="fun dims elements indexes =>"+
			" let n := dims.length"+
			" if n == 0 || (List.range n).any (fun i => indexes.getD i 0 > dims.getD i 0) then none"+
			" else let linIdx := (List.range n).foldl (fun acc i =>"+
			"   if i == 0 then indexes.getD 0 0"+
			"   else dims.getD i 0 * (acc - 1) + indexes.getD i 0) 0"+
			" elements[linIdx - 1]?";}
	}
}
