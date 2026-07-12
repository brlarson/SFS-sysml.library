//Allen.kerml


library package Allen {
  doc /* SFS:  Allen's Intervals 
    * "death" from df-bl.death; "birth" from df-bl.birth
    */
  
  private import Assertion::Assert;
  private import Occurrences::Occurrence;
  
  
  predicate precedes {
    @Assert{n="precedes"; f="<<precedes : x~Occurrence, y~Occurrence : death(x) < birth(y)>>";}
    in x : Occurrence;
    in y : Occurrence;
    x.endShot < y.startShot
  }
  
  predicate meets {
    @Assert{f="<< meets(X,Y) := (death(X) = birth(Y)) >>";}
    doc /* x must not be open-right, and y must not be open-left */
    in x : Occurrence;
    in y : Occurrence;
    x.endShot == y.startShot and not x.openRight and not y.openLeft
  }

  predicate overlaps {
    @Assert{f="<< overlaps(X,Y) :=  birth(Y) < death(X) >>";}
    in x : Occurrence;
    in y : Occurrence;
    y.startShot < x.endShot 
  }

  predicate starts {
    @Assert{f="<< starts(X,Y) :=  (birth(X) = birth(Y)) and (death(Y) < death(X)) >>";}
    doc /* both should be the same for open-left */
    in x : Occurrence;
    in y : Occurrence;
    (x.startShot == y.startShot) and (y.endShot < x.endShot)
      and x.openLeft == y.openLeft
  }

  predicate during {
    @Assert{f="<< during(X,Y) :=  (birth(Y) <= birth(X)) and (death(X) <= death(Y)) >>";}
    in x : Occurrence;
    in y : Occurrence;
    (y.startShot <= x.startShot) and (x.endShot <= y.endShot)
  }

  predicate finishes {
    @Assert{f="<< finishes(X,Y) :=  (birth(Y) < birth(X)) and (death(X) = death(Y)) >>";}
    in x : Occurrence;
    in y : Occurrence;
    y.startShot < x.startShot and x.endShot == y.endShot
      and x.openRight==y.openRight
  }

  predicate coincident {
    @Assert{f="<< coincident(X,Y) :=  (birth(Y) = birth(X)) and (death(X) = death(Y)) >>";}
    in x : Occurrence;
    in y : Occurrence;
    y.startShot == x.startShot and x.endShot == y.endShot
      and x.openLeft == y.openLeft and x.openRight==y.openRight
  }

  predicate nonoverlaps {
    @Assert{f="<< nonoverlaps(X,Y) :=  (birth(Y) > death(X)) or (birth(X) > death(Y)) >>";}
    in x : Occurrence;
    in y : Occurrence;
    (y.startShot > x.endShot) and (x.startShot > y.endShot)
  }
  
  abstract predicate nearlyMeets {
    @Assert{f="<< nearlyMeets(X,Y) := (death(X) = birth(Y)) and (X.openRight or Y.openLeft) >>";}
    doc /*  don't meet, but no instants between 
     * the end-shot of x and the start-shot of y
     * "abstract" because this can't be executed
     * x is open-right; y is open-left, or both
     */
    in x : Occurrence;
    in y : Occurrence;
    x.endShot==y.startShot and ( x.openRight or y.openLeft)
  }


}
