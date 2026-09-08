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
  private import ControlFunctions::select;
	private import Assertion::Assert;

  struct Buffer {
    doc /* FIFO buffer */
    private var feature elements[0..*] : Anything := ();

    bool isEmpty {
      return : Boolean[1] = elements == null;
    }

    @Assert{ doc /* any get returns was put previously */
      n="GetWhatsPut"; f="<< GetWhatsPut : : forall v~Anything, t1~Instant are get(v)@t1 <> null "+
        " implies exists t2~Instant in t2<t1 that put(v)@t2 >>"; }

    @Assert{ doc /* buffer is first-in first-out*/
      n="FIFO"; f="<< FIFO : : forall v1,v2~Anything, t1,t2~Instant in t1<t2 are "+
        " (v1 <> null and v2 <> null and get(v1)@t1 and get(v2)@t2) implies "+
        " exists t3~Instant in t3<t1 that exists t4~Instant in t4<t2 that "+
        " (t3<t4 and put(v1)@t3 and put(v2)@t4) >>";}

    @Assert{ doc /* anything evicted was put previously */
      n="EvictWhatsPut"; f="<< EvictWhatsPut : : forall v~Anything, t1~Instant are (v <> null and evict(v)@t1) "+
        " implies exists t2~Instant in t2<t1 that put(v)@t2 >>"; }

    @Assert{ doc /* anything returned by matching was put previously */
      n="MatchingWhatsPut"; f="<< MatchingWhatsPut : : forall v~Anything, sample~Anything, t1~Instant are "+
        " (v in matching(sample)@t1) implies exists t2~Instant in t2<t1 that put(v)@t2 >>"; }

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

    step evict {
      doc /* removes a specific, previously-identified value from the buffer, if any */
      in value : Anything[0..1];
      step : remove {
        inout seq = elements;
        in values = value;
      }
    }

    step matching {
      doc /* the first element currently in the buffer that conforms to the type of sample, if any */
      in sample : Anything[1];
      out matched : Anything[0..1] default head(elements->select{in x : Anything; x istype sample});
    }

  }

  struct OutBuffer {
    doc /* an outgoing buffer never needs to hold more than one pending value -- unlike Buffer (a
     * destructive FIFO, sized for a queue of pending incoming transfers), OutBuffer holds at most
     * one element, and get() does not remove it. That makes get() idempotent and safe for multiple
     * independent readers: a single put fans the same value out to every flow that reads it, until
     * the next put overwrites it. This is what lets one outgoing port feed several connected flows
     * (multicast) from a single send.
     *
     * Duplicating a value to more than one reader this way is only meaningful for Virtual payloads
     * (see Tangibility::Virtual) -- a Physical occurrence cannot actually be in two places at once,
     * so a Physical payload's outgoingBuffer must not be read by more than one flow even though
     * this struct's own get() would technically allow it.
     */
    private var feature element[0..1] : Anything := ();

    bool isEmpty {
      return : Boolean[1] = element == null;
    }

    @Assert{ doc /* any get returns was put previously */
      n="OutGetWhatsPut"; f="<< OutGetWhatsPut : : forall v~Anything, t1~Instant are get(v)@t1 <> null "+
        " implies exists t2~Instant in t2<=t1 that put(v)@t2 >>"; }

    @Assert{ doc /* get is non-destructive: repeated gets with no intervening put return the same value */
      n="OutGetIdempotent"; f="<< OutGetIdempotent : : forall v1,v2~Anything, t1,t2~Instant in t1<t2 are "+
        " (get(v1)@t1 and get(v2)@t2 and not exists t3~Instant in (t1<t3 and t3<=t2) that put(v3~Anything)@t3) "+
        " implies v1=v2 >>"; }

    step put {
      doc /* replaces whatever is currently held, rather than queueing alongside it */
      in value : Anything[1];
      step clearOld : remove {
        inout seq = element;
        in values = element;
      }
      step addNew : add {
        inout seq = element;
        in values = value;
      }
      succession clearOld then addNew;
    }

    step get {
      doc /* non-destructive: does not remove the element, so every connected reader sees it */
      out value : Anything[0..1] default if isEmpty()? null else head(element);
    }

  }

}