library package Domain {
  private import ScalarValues::Real;
  private import ScalarValues::Boolean;
  private import Base::DataValue;
  private import Assertion::Assert;
 	private import Occurrences::Occurrence;
	private import SI::s;
	private import Performances::BooleanEvaluation;
	private import Base::Anything;

  datatype Time specializes Real;
  
  type Instant specializes Time {
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

	function Get { // replaces FeatureReferencingPerformances::FeatureReadEvaluation
		doc /* Get(d,f,tau) returns the value of the feature d::f at time tau. */
		in feature d : Occurrence[1] {  //onOccurrence
		  feature f : Anything[1];  //accessedFeature
		}
		in feature tau : Instant[1];   //startingAt    
		return result : Anything[0..1];
		language "Domain" /* Get(d,f,tau) := I[[d::f,tau]]*/
	}

	function GetNow {
		doc /* GetNow(d,f) returns the value of the feature d::f at the current time, now. */
		in feature d : Occurrence[1] {  //onOccurrence
		  feature f : Anything[1];  //accessedFeature
		}
		return result : Anything[0..1] = Get(d, now);
		language "Domain" /* GetNow(d,f) := I[[d::f,now]]*/
	}

	behavior SetNow {  // replaces FeatureReferencingPerformances::FeatureWritePerformance
		doc /* SetNow(d,f,v) sets the value of the feature d::f to v at the current time, now. */
		in feature d : Occurrence[1] {  //onOccurrence
		  feature f : Anything[1];  //accessedFeature
		}
		in feature v : Anything[1];  //replacementValues
		language "Domain" /* I[[d::f,now]] = v */
	}

  behavior GetChange {
		doc /* GetChange(d,f) returns the change in value of the feature d::f 
		     * from its value at d::startShot. */
		in feature d : Occurrence[1] {  //onOccurrence
		  feature f : Anything[1];  //accessedFeature
		}
		out feature v : Anything[0..1];  //values
		language "Domain" /* ( I[[d::f,d::startShot]] <> I[[d::f,now]]
		  * and forall t~Instant in d::startShot ., now are I[[d::f,t]] = I[[d::f,d::startShot]]) 
			* implies v = I[[d::f,now]] */
	}

	behavior GetBooleanChange :> GetChange {
		in feature :>> d {
			feature e : BooleanEvaluation[1] :>> f;
		}
		out feature b : Boolean[1] :>> v;
		language "Domain" /* ( I[[d::e::result,d::startShot]] <> I[[d::e::result,now]]
		  * and forall t~Instant in d::startShot ., now are I[[d::e::result,t]] = I[[d::e::result,d::startShot]] )
			* implies b = I[[d::e::result,now]] */
	}

	behavior GetChangeToTrue :> GetBooleanChange{
		language "Domain" /* ( forall t~Instant in d::startShot ., now are I[[d::e::result,t]] = false  )
			* and I[[d::e::result,now]] = true */
	}

	behavior GetChangeToFalse :> GetBooleanChange{
		language "Domain" /* ( forall t~Instant in d::startShot ., now are I[[d::e::result,t]] = true  )
			* and I[[d::e::result,now]] = false */
	}

}