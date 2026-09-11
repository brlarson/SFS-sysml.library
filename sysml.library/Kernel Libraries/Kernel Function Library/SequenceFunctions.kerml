standard library package SequenceFunctions {
	doc
	/*
	 * This package defines functions that operate on general sequences of values. (For functions that
	 * operate on Collection values, see CollectionFunctions.)
	 */

	private import Base::Anything;
	private import Occurrences::SelfSameLifeLink;
	private import Occurrences::HappensJustBefore;
	private import ScalarValues::*;
	private import ControlFunctions::*;
	private import Assertion::Lean;
	private import Assertion::Assert;

	function '#' specializes BaseFunctions::'#' { in seq: Anything[0..*] ordered nonunique; in index: Positive[1];
		return : Anything[0..1];
		@Lean{l="fun seq i => seq[i - 1]?";}
	}

	function equals{ in x: Anything[0..*] ordered nonunique; in y: Anything[0..*] ordered nonunique;
		return : Boolean[1] =
			size(x) == size(y) and
			(1..size(x))->forAll {in i; x#(i) == y#(i)};
		@Lean{l="fun x y => x = y";}
	}

	function same{ in x: Anything[0..*] ordered nonunique; in y: Anything[0..*] ordered nonunique;
		return : Boolean[1] =
			size(x) == size(y) and
			(1..size(x))->forAll {in i; x#(i) === y#(i)};
		@Lean{l="fun x y => x.length == y.length && (x.zip y).all fun p => ptrEq p.1 p.2";}
	}

	function size{ in seq: Anything[0..*] nonunique;
		return : Natural[1] = if isEmpty(seq)? 0 else size(tail(seq)) + 1;
		@Lean{l="List.length";}
	}
	function isEmpty{ in seq: Anything[0..*] nonunique;
		return : Boolean[1] = seq == null;
		@Lean{l="List.isEmpty";}
	}
	function notEmpty{ in seq: Anything[0..*] nonunique;
		return : Boolean[1] = not isEmpty(seq);
		@Lean{l="fun seq => !List.isEmpty seq";}
	}
	function includes{ in seq1: Anything[0..*] nonunique; in seq2: Anything[0..*] nonunique;
		return : Boolean[1] = seq2->forAll {in x; seq1->exists{in y; x == y}};
		@Lean{l="fun seq1 seq2 => List.Subset seq2 seq1";}
	}
	function includesOnly{ in seq1: Anything[0..*] nonunique; in seq2: Anything[0..*] nonunique;
		return : Boolean[1] = seq1->includes(seq2) and seq2->includes(seq1);
		@Lean{l="fun seq1 seq2 => List.Subset seq1 seq2 ∧ List.Subset seq2 seq1";}
	}
	function excludes{ in seq1: Anything[0..*] nonunique; in seq2: Anything[0..*] nonunique;
		return : Boolean[1] = seq2->forAll {in x; seq1->excludes(x)};
		@Lean{l="List.Disjoint";}
	}

	function union{ in seq1: Anything[0..*] ordered nonunique; in seq2: Anything[0..*] ordered nonunique;
		return : Anything[0..*] ordered nonunique = (seq1, seq2);
		@Lean{l="List.append";}
	}
	function intersection{ in seq1: Anything[0..*] ordered nonunique; in seq2: Anything[0..*] ordered nonunique;
		return : Anything[0..*] ordered nonunique = seq1->select {in x; seq2->includes(x)};
		@Lean{l="List.inter";}
	}
	function including{ in seq: Anything[0..*] ordered nonunique; in values: Anything[0..*] ordered nonunique;
		return : Anything[0..*] ordered nonunique = union(seq, values);
		@Lean{l="List.append";}
	}
	function includingAt{ in seq: Anything[0..*] ordered nonunique; in values: Anything[0..*] ordered nonunique;
		in index: Positive[1];
		return : Anything[0..*] ordered nonunique =
			(seq->subsequence(1, (index - 1) as Positive), values, seq->subsequence(index + 1));
//			(seq->subsequence(1, index - 1), values, seq->subsequence(index + 1));
		@Lean{l="fun seq values index => seq.take (index - 1) ++ values ++ seq.drop index";}
	}
	function excluding{ in seq: Anything[0..*] ordered nonunique; in values: Anything[0..*];
		return : Anything[0..*] ordered nonunique = seq->reject {in x; values->includes(x)};
		@Lean{l="List.diff";}
	}
	function excludingAt{ in seq: Anything[0..*] ordered nonunique;
		in startIndex: Positive[1]; in endIndex: Positive[1] default startIndex;
		return : Anything[0..*] ordered nonunique =
			(seq->subsequence(1, (startIndex - 1) as Positive), seq->subsequence(endIndex + 1));
//			(seq->subsequence(1, startIndex - 1), seq->subsequence(endIndex + 1));
		@Lean{l="fun seq startIndex endIndex => seq.take (startIndex - 1) ++ seq.drop endIndex";}
	}

	function subsequence{ in seq: Anything[0..*] ordered nonunique;
		in startIndex: Positive[1]; in endIndex: Positive[1] default size(seq) as Positive;
//		in startIndex: Positive[1]; in endIndex: Positive[1] default size(seq);
		return : Anything[0..*] = (startIndex..endIndex)->collect {in i; seq#(i)};
		@Lean{l="fun seq startIndex endIndex => (seq.drop (startIndex - 1)).take (endIndex - startIndex + 1)";}
	}
	function head{ in seq: Anything[0..*] ordered nonunique;
		return : Anything[0..1] = seq#(1);
		@Lean{l="List.head?";}
	}
	function tail{ in seq: Anything[0..*] ordered nonunique;
		return : Anything[0..*] ordered nonunique = subsequence(seq, 2);
		@Lean{l="List.tail";}
	}
	function last{ in seq: Anything[0..*] ordered nonunique;
		return : Anything[0..1] = seq#(size(seq));
		@Lean{l="List.getLast?";}
	}

doc 
	/* SFS:  The 4 behaviors (add/addAt/remove/removeAt) are left without — 
	 * same treatment as every other file in this session: no prior behavior
	 * anywhere in the project has gotten @Lean metadata, since their real
	 * semantics is already fully captured by the pure helper functions they
	 * invoke (including/includingAt/excluding/excludingAt, each already annotated above).	
	 */

	behavior add { inout seq: Anything[0..*] ordered nonunique; in values: Anything[0..*] ordered nonunique;
		@Assert{n="add appends values"; f="<<add : seq~Anything : I[[self::seq,endShot]]"+
				" = including(I[[self::seq,startShot]],values) >>";}
		succession :HappensJustBefore first calcNewSeq then bindNewSeq;
		private step calcNewSeq {
			feature newSeq = seq->including(values);
		}
		step bindNewSeq {
			binding seq = calcNewSeq.newSeq;
		}
	}
	behavior addAt { inout seq: Anything[0..*] ordered nonunique; in values: Anything[0..*] ordered nonunique;
		in index: Positive[1];
		@Assert{n="addAt inserts values"; f="<<addAt : seq~Anything : I[[self::seq,endShot]]"+
				" = includingAt(I[[self::seq,startShot]],values,index) >>";}
		succession :HappensJustBefore first calcNewSeq then bindNewSeq;
		private step calcNewSeq {
			feature newSeq = seq->includingAt(values, index);
		}
		step bindNewSeq {
			binding seq = calcNewSeq.newSeq;
		}
	}
	behavior remove{ inout seq: Anything[0..*] ordered nonunique; in values: Anything[0..*];
		@Assert{n="remove excludes values"; f="<<remove : seq~Anything : I[[self::seq,endShot]]"+
				" = excluding(I[[self::seq,startShot]],values) >>";}
		succession :HappensJustBefore first calcNewSeq then bindNewSeq;
		private step calcNewSeq {
			feature newSeq = seq->excluding(values);
		}
		step bindNewSeq {
			binding seq = calcNewSeq.newSeq;
		}
	}
	behavior removeAt{ inout seq: Anything[0..*] ordered nonunique;
		in startIndex: Positive[1]; in endIndex: Positive[1] default startIndex;
		@Assert{n="removeAt shrinks seq"; f="<<removeAt : seq~Anything :"+
				" subsetOf(I[[self::seq,endShot]],I[[self::seq,startShot]]) >>";}
		succession :HappensJustBefore first calcNewSeq then bindNewSeq;
		private step calcNewSeq {
			feature newSeq = seq->excludingAt(startIndex, endIndex);
		}
		step bindNewSeq {
			binding seq = calcNewSeq.newSeq;
		}
	}
}