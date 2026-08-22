//Allen.kerml


library package Allen {
  doc /* SFS:  Allen's Intervals
    * "death" defined by df-bl.death; "birth" defined by df-bl.birth
    */
  
  private import Assertion::Assert;
  private import Occurrences::Occurrence;
  private import Domain::next;
  
  
  predicate precedes {
    @Assert{n="precedes"; f="<<precedes : x~Occurrence, y~Occurrence :"+
      " death(x) < birth(y) >>"; t="precedes";}
    in x : Occurrence;
    in y : Occurrence;
    x.endShot < y.startShot
  }
  
  predicate meets {
    @Assert{n="meets"; f="<<meets : x~Occurrence, y~Occurrence :"+
      " death(x) = birth(y) >>"; t="meets";}
    doc /* x must not be open-right, and y must not be open-left */
    in x : Occurrence;
    in y : Occurrence;
    x.endShot == y.startShot and not x.openRight and not y.openLeft
  }

  predicate overlaps {
    @Assert{n="overlaps"; f="<<overlaps : x~Occurrence, y~Occurrence :"+
      " birth(y) <  death(x)>>"; t="overlaps";}
    in x : Occurrence;
    in y : Occurrence;
    y.startShot < x.endShot 
  }

  predicate starts {
    @Assert{n="starts"; f="<<starts : x~Occurrence, y~Occurrence :"+
      " birth(x) = birth(y) and death(y) < death(x)"+
      " and x.openLeft = y.openLeft >>"; t="starts";}
    doc /* both should be the same for open-left */
    in x : Occurrence;
    in y : Occurrence;
    (x.startShot == y.startShot) and (y.endShot < x.endShot)
      and x.openLeft == y.openLeft
  }

  predicate during {
    @Assert{n="during"; f="<<during : x~Occurrence, y~Occurrence :"+
      " birth(y) <= birth(x) and death(x) <= death(y)>>"; t="during";}
    in x : Occurrence;
    in y : Occurrence;
    (y.startShot <= x.startShot) and (x.endShot <= y.endShot)
  }

  predicate finishes {
    @Assert{n="finishes"; f="<<finishes : x~Occurrence, y~Occurrence :"+
      " birth(y) < birth(x) and death(x) = death(y)"+
      " and x.openRight = y.openRight >>"; t="finishes";}
    doc /* both should be the same for open-right */
    in x : Occurrence;
    in y : Occurrence;
    y.startShot < x.startShot and x.endShot == y.endShot
      and x.openRight==y.openRight
  }

  predicate coincident {
    @Assert{n="coincident"; f="<<coincident : x~Occurrence, y~Occurrence :"+
      " birth(y) = birth(x) and death(x) = death(y)"+
      " and x.openLeft = y.openLeft and x.openRight = y.openRight >>"; t="coincident";}
    doc /* both should be the same for open-left and open-right */
    in x : Occurrence;
    in y : Occurrence;
    y.startShot == x.startShot and x.endShot == y.endShot
      and x.openLeft == y.openLeft and x.openRight==y.openRight
  }

  predicate nonoverlaps {
    @Assert{n="nonoverlaps"; f="<<nonoverlaps : x~Occurrence, y~Occurrence :"+
      " birth(y) > death(x) or birth(x) > death(y)>>"; t="nonoverlaps";}
    in x : Occurrence;
    in y : Occurrence;
    (y.startShot > x.endShot) or (x.startShot > y.endShot)
  }
  
  predicate nearlyMeets {
    @Assert{n="nearlyMeets"; f="<<nearlyMeets : x~Occurrence, y~Occurrence :"+
      " (birth(y) = death(x) and (x.openRight or y.openLeft)) or next(death(x), birth(y))>>";}
    doc /*  don't meet, but no instants between the end-shot of x and the start-shot of y */
    in x : Occurrence;
    in y : Occurrence;
    ( x.endShot==y.startShot and ( x.openRight or y.openLeft) ) or next(x.endShot, y.startShot)
  }


}
