library package Mereology {
    doc
    /*
     * SFS:  Merology is the metaphysics of parthood.
     * Predicates are Performances::BooleanEvaluation in KerML, 
     * but metaphysical predicates aren't meant to be executed.
     * Need something to define values rather than operations.
     */

    private import Performances::BooleanEvaluation;
    private import KerML::Kernel::Class;
	private import Assertion::Assert;

    abstract predicate PartOf specializes BooleanEvaluation {
        doc /* SFS: PartOf is the proper part relation xPy (x is a proper part of y)*/
        @Assert{n="PartOf"; f="<< PartOf : x~Class, y~Class : xPy >>";}
        in x : Class;
        in y : Class;
    }

    // SFS:  Define part antireflexivity.
    @Assert{n="PAR"; f="<< PAR : : forall x~Class are not PartOf(x,x) >>"; t="df-par";}
    // SFS:  Define part transitivity.
    @Assert{n="PTR"; f="<< PTR : : forall x,y,z~Class are ( (PartOf(x,y) and PartOf(y,z)) implies PartOf(x,z) ) >>"; t="df-ptr";}
     
    abstract predicate PartOverlap specializes BooleanEvaluation {
        doc /* SFS: PartOverlap is the overlap relation xOy */
        @Assert{n="PartOverlap"; f="<< PartOverlap : x~Class, y~Class : "+
                "exists z~Class that ( PartOf(z,x) and PartOf(z,y) ) >>"; t="df-pov";}
        in x : Class;
        in y : Class;
    }
    
    abstract predicate PartUnderlap specializes BooleanEvaluation {
        doc /* SFS: PartUnderlap is the underlap relation xUy */
        @Assert{n="PartUnderlap"; f="<< PartUnderlap : x~Class, y~Class : "+
                "exists z~Class that ( PartOf(x,z) and PartOf(y,z) ) >>"; t="df-pun";}
        in x : Class;
        in y : Class;
    }

    abstract predicate ImproperPart specializes BooleanEvaluation {
        doc /* SFS: ImproperPart is the improper part relation xIPy */
        @Assert{n="ImproperPart"; f="<< ImproperPart : x~Class, y~Class : PartOf(x,y) or x=y >>";}
        in x : Class;
        in y : Class;
    }

    abstract predicate PartDisjoint specializes BooleanEvaluation {
        doc /* SFS: PartDisjoint is the part disjointness relation xDy */
        @Assert{n="PartDisjoint"; f="<< PartDisjoint : x~Class, y~Class : not PartOverlap(x,y) >>";
                t="df-pdj";}
        in x : Class;
        in y : Class;
    }

    // SFS:  Define part containment hierarchy.
    @Assert{n="PCH"; f="<< PCH : : forall x,y~Class are "+
        "( (x=y or PartOf(x,y) or PartOf(y,x) or PartDisjoint(x,y))"+
        "and not (PartOf(x,y) and PartOf(y,x)) ) >>"; t="df-pch";}


    abstract predicate AtomicPart specializes BooleanEvaluation {
        doc /* SFS: AtomicPart is the part atomicity Ax */
        @Assert{n="AtomicPart";f="<< AtomicPart : x~Class : not exists z~Class that PartOf(z,x) >>";
                t="df-pat";}
        in x : Class;
    }

}