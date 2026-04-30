//Allen.kerml


library package Allen {
  doc /* SFS:  Allen's Intervals */
  
  private import Assertion::Assert;
  private import Occurrences::Occurrence;
  
  
  predicate precedes {
    language "Domain" /*  precedes(X,Y) := death(X) < birth(Y) */
    in x : Occurrence;
    in y : Occurrence;
    x.endShot < y.startShot
  }
  
  predicate meets {
    language "Domain" /*  meets(X,Y) := (death(X) = birth(Y)) */
    doc /* x must not be open-right, and y must not be open-left */
    in x : Occurrence;
    in y : Occurrence;
    x.endShot == y.startShot and not x.openRight and not y.openLeft
  }

  predicate overlaps {
    language "Domain" /*  overlaps(X,Y) :=  birth(Y) < death(X) */
    in x : Occurrence;
    in y : Occurrence;
    y.startShot < x.endShot 
  }

  predicate starts {
    language "Domain" /*  starts(X,Y) :=  (birth(X) = birth(Y)) and (death(Y) < death(X)) */
    doc /* both should be the same for open-left */
    in x : Occurrence;
    in y : Occurrence;
    (x.startShot == y.startShot) and (y.endShot < x.endShot)
      and x.openLeft == y.openLeft
  }

  predicate during {
    language "Domain" /*  during(X,Y) :=  (birth(Y) <= birth(X)) and (death(X) <= death(Y)) */
    in x : Occurrence;
    in y : Occurrence;
    (y.startShot <= x.startShot) and (x.endShot <= y.endShot)
  }

  predicate finishes {
    language "Domain" /*  finishes(X,Y) :=  (birth(Y) < birth(X)) and (death(X) = death(Y)) */
    in x : Occurrence;
    in y : Occurrence;
    y.startShot < x.startShot and x.endShot == y.endShot
      and x.openRight==y.openRight
  }

  predicate coincident {
    language "Domain" /*  coincident(X,Y) :=  (birth(Y) = birth(X)) and (death(X) = death(Y)) */
    in x : Occurrence;
    in y : Occurrence;
    y.startShot == x.startShot and x.endShot == y.endShot
      and x.openLeft == y.openLeft and x.openRight==y.openRight
  }

  predicate nonoverlaps {
    language "Domain" /*  nonoverlaps(X,Y) :=  (birth(Y) > death(X)) or (birth(X) > death(Y)) */
    in x : Occurrence;
    in y : Occurrence;
    (y.startShot > x.endShot) and (x.startShot > y.endShot)
  }
  
  abstract predicate nearlyMeets {
    language "Domain" /* nearlyMeets(X,Y) := (death(X) = birth(Y)) and (X.openRight or Y.openLeft) */
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
