/* standard */ library package RunTimeServices {
  doc 
  /*
   * RunTimeServices defines classes to perform operations
   * as similar to AADL Run-Time Services (RTS) as possible.
  */

  private import Collections::List;
  private import ScalarValues::Natural;
  private import Base::Anything;
  private import ScalarValues::Boolean;
  private import SequenceFunctions::*;
	private import Assertion::Assert;

  struct Buffer {
    doc /* FIFO buffer */
    private var feature elements[0..*] : Anything := ();

    function isEmpty {
      return : Boolean[1] = elements == null;
    }

    @Assert{ doc /* any get returns was put previously */
      n="GetWhatsPut"; f="<< GetWhatsPut : : forall t1~Instant are get(v)@t1 <> null "+
        " implies exists t2~Instant in t2<t1 that put(v)@t2 >>"; }

    @Assert{ doc /* buffer is first-in first-out*/
      n="FIFO"; f="<< FIFO : : forall t1,t2~Instant in t1<t2 are "+
        " (get(v1)@t1 and get(v2)@t2) implies "+
        " exists t3~Instant in t3<t1 that exists t4~Instant in t4<t2 that "+
        " (t3<t4 and put(v1)@t3 and put(v2)@t4) >>";}

    step put {
      in value : Anything[1];
      step : add {
        inout seq = elements;
        in values = value;
      } 
    } 

    step get {
      out var value : Anything[0..1] default if isEmpty()?  null else head(elements);
      step : remove {
        inout seq = elements;
        in values = value;
      }
      doc /* when get returns a value, that value was put previously */
    } 

  }


}