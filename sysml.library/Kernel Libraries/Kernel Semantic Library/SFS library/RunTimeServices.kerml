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

  struct Buffer {
    doc /* FIFO buffer */
    private var feature elements[0..*] : Anything := ();

    function isEmpty {
      return : Boolean[1] = elements == null;
    }

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
      language "Domain" /* get(v)@t1 <> null implies exists t2 in t2<t1 that put(v)@t2 */ 
    } 

    language "Domain" 
      /* (get(v1)@t1 and get(v2)@t2 and t1<t2) implies
      * exists t3 in t3<t1 that exists t4 in t4<t2 that
      * (t3<t4 and put(v1)@t3 and put(v2)@t4) */
  }


}