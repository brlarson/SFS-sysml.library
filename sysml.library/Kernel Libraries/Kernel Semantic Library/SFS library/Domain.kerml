library package Domain {
  private import ScalarValues::Real;
  private import ScalarValues::Boolean;
  private import Base::DataValue;
  private import Assertion::Assert;
 	private import Occurrences::Occurrence;
	private import SI::s;
	private import Performances::BooleanEvaluation;
	private import Base::Anything;
  private import ISQSpaceTime::TimeValue;

//  datatype Time specializes Real;
  
  type Instant specializes TimeValue {
    doc /* an instant of time */
  }
  
  classifier Interval  
  {
    doc /* an interval is a duration between two instants */
    feature lowerBound : Instant;
    feature upperBound : Instant;
    feature openLeft : Boolean;
    feature openRight : Boolean; 
    inv {lowerBound <= upperBound}   
  }

	feature now : Instant {
		doc /* the current instant of time */
	}	

	feature start : Instant = 0.0 [s] {
		doc /* the beginning of system operation, start=0 */
	}

	predicate next {
		doc /* tau1 precedes tau2 and there are no instants in between */
		@Assert{n="next"; f="<<next : tau1~Instant, tau2~Instant : (tau1 < tau2 and "+
			" not exists tau~Instant that (tau1 < tau and tau < tau2) )  >>"; 
				t="next";}
		in feature tau1 : Instant;
		in feature tau2 : Instant;
	}

	function Get { // replaces FeatureReferencingPerformances::FeatureReadEvaluation
		doc /* Get(d,f,tau) returns the value of the feature d::f at time tau. */
		@Assert{n="Get"; f="<<Get : d~Occurrence, f~Anything, tau~Instant := I[[d::f,tau]] >>";
				t="Get";}
		in feature d : Occurrence[1] {  //onOccurrence
		  feature f : Anything[1];  //accessedFeature
		}
		in feature tau : Instant[1];   //startingAt    
		return result : Anything[0..1];
	}

	function GetNow {
		doc /* GetNow(d,f) returns the value of the feature d::f at the current time, now. */
		@Assert{n="GetNow"; f="<<GetNow : d~Occurrence, f~Anything := I[[d::f,now]] >>"; 
				t=("Get","now");}
		in feature d : Occurrence[1] {  //onOccurrence
		  feature f : Anything[1];  //accessedFeature
		}
		return result : Anything[0..1] = Get(d, now);
	}

	behavior SetNow {  // replaces FeatureReferencingPerformances::FeatureWritePerformance
		doc /* SetNow(d,f,v) sets the value of the feature d::f to v at the current time, now. */
		@Assert{n="SetNow"; f="<<SetNow : d~Occurrence, f~Anything : I[[d::f,now]] = v >>";
				t="SetNow";}
		in feature d : Occurrence[1] {  //onOccurrence
		  feature f : Anything[1];  //accessedFeature
		}
		in feature v : Anything[1];  //replacementValues
	}

  behavior GetChange {
		doc /* GetChange(d,f) waits for value of the feature d::f to change
		     * from its value at time tau. */
		@Assert{n="GetChange"; f="<<GetChange : d~Occurrence, f~Anything, tau~Instant : "+
				"(I[[d::f,tau]] <> I[[d::f,now]] and forall t~Instant in tau ., now are I[[d::f,t]] = I[[d::f,tau]])"+
				" implies v = I[[d::f,now]] >>";
				t="GetChange";}
		in feature d : Occurrence[1] {  //onOccurrence
		  feature f : Anything[1];  //accessedFeature
		}
		in feature tau : Instant[1];   //startingAt    
		out feature v : Anything[0..1];  //values
	}

	behavior GetBooleanChange :> GetChange {
		doc /* GetBooleanChange, like GetChange, waits for d::e to toggle */
		@Assert{n="GetBooleanChange"; f="<<GetBooleanChange : d~Occurrence, e~BooleanEvaluation, tau~Instant : "+
				"(I[[d::e,tau]] <> I[[d::e,now]] and forall t~Instant in tau ., now are I[[d::e,t]] = I[[d::e,tau]])"+
				" implies b = I[[d::e,now]] >>";
				t="GetBooleanChange";}
		in feature :>> d {
			feature e : BooleanEvaluation[1] :>> f;
		}
		in feature tau : Instant[1];   //startingAt    
		out feature b : Boolean[1] :>> v;
	}

	behavior GetChangeToTrue :> GetBooleanChange{
		doc /* GetChangeToTrue does not wait if d::e is already true */
		@Assert{n="GetChangeToTrue"; f="<<GetChangeToTrue : d~Occurrence, e~BooleanEvaluation, tau~Instant : "+
				"(I[[d::e,now]] and forall t~Instant in tau ., now are not I[[d::e,t]] )"+
				" implies b = true >>";
				t="GetChangeToTrue";}
	}

	behavior GetChangeToFalse :> GetBooleanChange{
		doc /* GetChangeToFalse does not wait if d::e is already false */
		@Assert{n="GetChangeToFalse"; f="<<GetChangeToFalse : d~Occurrence, e~BooleanEvaluation, tau~Instant : "+
				"(not I[[d::e,now]] and forall t~Instant in tau ., now are I[[d::e,t]] )"+
				" implies b = false >>";
				t="GetChangeToFalse";}
	}

}