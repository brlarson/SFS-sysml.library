library package Mereology {
    doc
    /*
     * SFS:  Merology is the metaphysics of parthood.
     * Predicates are Performances::BooleanEvaluation in KerML, 
     * but metaphysical predicates aren't meant to be executed.
     * Need something to define values rather than operations.
     */

    private import Performances::BooleanEvaluation;
    private import Occurrences::Occurrence;
	private import Assertion::Assert;

    abstract predicate PartOf specializes BooleanEvaluation {
        doc /* SFS: PartOf is the proper part relation xPy (x is a proper part of y)*/
        @Assert{n="PartOf"; f="<< PartOf : x~Occurrence, y~Occurrence : xPy >>";}
        in x : Occurrence;
        in y : Occurrence;
    }

    // SFS:  Define part antireflexivity.
    @Assert{n="PAR"; f="<< PAR : : forall x~Occurrence are not PartOf(x,x) >>"; t="par";}
    // SFS:  Define part transitivity.
    @Assert{n="PTR"; f="<< PTR : : forall x,y,z~Occurrence are ( (PartOf(x,y) and PartOf(y,z)) implies PartOf(x,z) ) >>"; t="ptr";}

    abstract predicate PartOverlap specializes BooleanEvaluation {
        doc /* SFS: PartOverlap is the overlap relation xOy */
        @Assert{n="PartOverlap"; f="<< PartOverlap : x~Occurrence, y~Occurrence : "+
                "exists z~Occurrence that ( PartOf(z,x) and PartOf(z,y) ) >>"; t="PartOverlap";}
        in x : Occurrence;
        in y : Occurrence;
    }

    abstract predicate PartUnderlap specializes BooleanEvaluation {
        doc /* SFS: PartUnderlap is the underlap relation xUy */
        @Assert{n="PartUnderlap"; f="<< PartUnderlap : x~Occurrence, y~Occurrence : "+
                "exists z~Occurrence that ( PartOf(x,z) and PartOf(y,z) ) >>"; t="PartUnderlap";}
        in x : Occurrence;
        in y : Occurrence;
    }

    abstract predicate ImproperPart specializes BooleanEvaluation {
        doc /* SFS: ImproperPart is the improper part relation xIPy */
        @Assert{n="ImproperPart"; f="<< ImproperPart : x~Occurrence, y~Occurrence : PartOf(x,y) or x=y >>"; t="ImproperPart";}
        in x : Occurrence;
        in y : Occurrence;
    }

    abstract predicate PartDisjoint specializes BooleanEvaluation {
        doc /* SFS: PartDisjoint is the part disjointness relation xDy */
        @Assert{n="PartDisjoint"; f="<< PartDisjoint : x~Occurrence, y~Occurrence : not PartOverlap(x,y) >>";
                t="PartDisjoint";}
        in x : Occurrence;
        in y : Occurrence;
    }

    // SFS:  Define part containment hierarchy.
    @Assert{n="PCH"; f="<< PCH : : forall x,y~Occurrence are "+
        "( (x=y or PartOf(x,y) or PartOf(y,x) or PartDisjoint(x,y))"+
        "and not (PartOf(x,y) and PartOf(y,x)) ) >>"; t="pch";}


    abstract predicate AtomicPart specializes BooleanEvaluation {
        doc /* SFS: AtomicPart is the part atomicity Ax */
        @Assert{n="AtomicPart";f="<< AtomicPart : x~Occurrence : not exists z~Occurrence that PartOf(z,x) >>";
                t="AtomicPart";}
        in x : Occurrence;
    }

}