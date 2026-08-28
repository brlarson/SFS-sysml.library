//Tangibility.KerML

library package Tangibility {
  doc /* Whether something is virtual or physical, and if physical, solid, liquid, or etherial */
  
  private import Regions::Region;
  private import ISQ::VolumeValue;
  private import SI::L;

  abstract classifier Virtual {
    doc /* something without physical existence itself, and can only exist if allocated to something physical */

    feature allocatedTo : Physical[1] {
      doc /* may be allocated to another virtual thing, but must everntually be allocated to 
       * something physical to exist */
    }

  }

  abstract classifier Physical disjoint from Virtual {
    doc /* something which occupies a 3D region in some frame-of-reference*/

    feature location : Region[1];
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

}

