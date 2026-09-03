library package Tangibility {
  doc /* Whether something is virtual or physical, and if physical, solid, liquid, or etherial */
  
  private import Regions::Region;
  private import ISQ::VolumeValue;
  private import SI::L;
  private import Occurrences::Occurrence;

  abstract classifier Virtual :> Occurrence {
    doc /* something without physical existence itself, and can only exist if allocated to something physical */

    var feature allocatedTo[0..1] : Physical {
      doc /* physical thing which hosts or performs this virtual thing allowing it to exist */
    }

    var feature delegatedTo[0..1] : Virtual {
      doc /* may be delegated to another virtual thing, but must everntually be allocated to 
       * something physical to exist */
    }

    var feature delegations[0..*] : Virtual {
      doc /* other virtual things which delegate their existence to this virtual thing */
    }
  }

  abstract classifier Physical :> Occurrence disjoint from Virtual {
    doc /* something which occupies a 3D region in some frame-of-reference*/

    var feature location[1] : Region {
      doc /* where this thing exists */
    }

    var feature allocations[0..*] : Virtual {
      doc /* the virtual things this physical thing hosts or performs */
    }
  }

  abstract classifier Solid :> Physical {
    doc /* something that might bend or deform, but not flow */
  }

  abstract classifier Fluid :> Physical disjoint from Solid {
    doc /* something that flows; liquid or gas*/

    feature amount : VolumeValue[1] default 0 [L] {
      doc /* volume of fluid held in its location */
    }
  }

  abstract classifier Etherial :> Physical disjoint from Solid, Fluid {
    doc /* medium for the transmission of radiation:  light, radio, heat, cosmic rays */
  }

  assoc Allocation {
    doc /* association of a virutal thing to the physical thing to which it's allocated */
    end feature virtualThing : Virtual crosses physicalThing.allocations;
    end feature physicalThing : Physical crosses virtualThing.allocatedTo;
  }

  assoc Delegation {
    doc /* delegation of existance from one virtual thing to another virtual thing */
    end feature delegator : Virtual crosses delegatee.delegations;
    end feature delegatee : Virtual crosses delegator.delegatedTo;
  }

  function Location :> Regions::Location {
    doc /* */
    // in o : Occurrence :>> o;
    // return result : Region :>> result;
    if (o istype Physical) ? (o as Physical).location else
      if o istype Virtual ?
        if not (o as Virtual).allocatedTo.isEmpty ? Location((o as Virtual).allocatedTo)
          else if not (o as Virtual).delegatedTo.isEmpty ? Location((o as Virtual).delegatedTo)
          else Regions::nowhere;
  }

}

