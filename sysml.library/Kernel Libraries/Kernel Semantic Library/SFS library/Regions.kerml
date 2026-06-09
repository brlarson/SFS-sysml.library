library package Regions {
    doc
    /*
    *  SFS:  Metaphysical
    * A region is a contiguous, three-dimensional volume at a particular place in a particular frame-of-reference.
    * The location of a thing is the region it occupies (within a frame-of-reference, at a particular moment of time).
    * The surface of a region is its boundary.
    */
    private import SpatialFrames::SpatialFrame;
    private import Occurrences::Occurrence;
	private import Assertion::Assert;
    private import Performances::BooleanEvaluation;
    private import Clocks::Clock;
    private import Clocks::universalClock;

    type FrameOfReference specializes Base::Anything {
        doc
        /*
        * SFS:  A frame of reference serves as the reference for the location of an occurrence.
        * All inertial frames-of-reference are completely equivalent for the formulation of the 
        * Laws of Physics. (relativity)
        * A frame of reference has an existence independent of objects and processes occurring
        * within it. (substantialism)
        * Within a frame of reference, time progresses uniformly, and simultenaity is
        * well-defined. (Newtonian spacetime)
        */
        feature clock : Clock default universalClock;
    }

    feature universalFrameOfReference : FrameOfReference {
        doc
        /*
        * SFS: universalFrameOfReference is a fixed frame of reference used as a
        * universal default.
        */
        feature :>> clock = universalClock;
    }

    type Region specializes Base::Anything {
        doc
        /*
        * SFS:  A region is a contiguous, three-dimensional volume at a particular
        * place in a particular frame-of-reference. [9]
        * Regions do not have parts.
        * A region may overlap or contain other regions.
        */
        feature frameOfReference : FrameOfReference default universalFrameOfReference;
    }

    type Point specializes Base::Anything {
        doc
        /*
        *  SFS:  Point is a metaphysical 0-dimensional entity.
        */
        feature frameOfReference : FrameOfReference default universalFrameOfReference;
    }

    type Surface specializes Base::Anything {
        doc
        /*
        *  SFS:  Surface is the set of points at the boundary of a Region.
        */
        feature frameOfReference : FrameOfReference default universalFrameOfReference;
    }
 
    /**
     * Represents a spatial location or position within a system.
     * This function can be used to define or reference points, areas, or regions
     * in a model where specific coordinates or spatial context is needed.
     */
    function Location {
        doc
        /*
        * SFS:  The location function relates spatial occurrences to their region.
        * This is the "L" exact location primitive. 
        * Uses o.frameOfReference as the frame-of-reference for the region.
        */
        @Assert{t="Location"; f="<< Location : o~Occurrence := result~Region | o L region";
            comment /* Location is a function, but "L" is a binary operator, so "|" (such that)  notation is used */ }
        in o : Occurrence;
        return result : Region;
        inv { o.isClosed and o.innerSpaceDimension == 3 and o.outerSpaceDimension == 3
            and o.frameOfReference == (result as Region).frameOfReference 
            }
    }

     // SFS:  Two things having the same location are the same thing (df-lfu)
    @Assert{n="locational functionality"; 
        f="<< LFU : : forall x~Occurrence forall r1,r2~Region are"+
          " ( (L(x)=r1 and L(x)=r2) implies r1=r2 ) >>"; t="df-lfu";}

    // SFS:  No two things share an exact location.
    @Assert{n="injectivity of location"; 
        f="<< LIN : : forall x,y~Occurrence forall r~Region are"+
          " ( (L(x)=r and L(y)=r) implies x=y ) >>"; t="df-lin";}


    predicate PointInRegion {
        doc /* SFS: Point is contained in Region; "in" is a set mebership relation */
        @Assert{n="PointInRegion"; f="<< PointInRegion : point~Point, region~Region : "+
                " point in region >>";}
        in point : Point;
        in region : Region;
        inv { point.frameOfReference == region.frameOfReference }
    }

    predicate PointOnSurface {
        doc /* SFS: Point is on a Surface */
        @Assert{n="PointOnSurface"; f="<< PointOnSurface : point~Point, surface~Surface : "+
                " point in surface >>";}
        in point : Point;
        in surface : Surface;
        inv { point.frameOfReference == surface.frameOfReference }
    }

    predicate RegionOverlap {
        doc /* SFS:  Two regions containing the same point overlap. 
            * This is the "O" relation (df-rov).
            * Regions are disjoint if they don't overlap */
        @Assert{n="RegionOverlap"; f="<< RegionOverlap : r1~Region, r2~Region :"+
                "exists p~Point that (PointInRegion(p,r1) and PointInRegion(p,r2)) >>"; t="df-rov";}
        in r1 : Region;
        in r2 : Region;
        inv { r1.frameOfReference == r2.frameOfReference }
    }


    predicate RegionContainment {
        doc /* SFS:  A region contains another, when it contains all of its points.
            *  true when r1 contains r2 
            * This is the "C" relation (df-rco). */
        @Assert{n="RegionContainment"; f="<< RegionContainment : r1~Region, r2~Region :"+
                "exists p~Point that (PointInRegion(p,r2) implies PointInRegion(p,r1)) >>"; t="df-rco";}
        in r1 : Region;
        in r2 : Region;
        inv { r1.frameOfReference == r2.frameOfReference }
    }

    doc /* SFS: Regions overlap only if one contains the other. This property is called no interpenetration. */
    @Assert{n="NOINTP"; f="<< NOINTP : : forall r1,r1~Region are"+ 
            "RegionOverlap(r1,r2) implies (RegionContainment(r1,r2) or RegionContainment(r2,r1)) >>"; t="df-rni";}

    doc /* SFS: Parthood implies regional containment. This property is called expansivity. */
    @Assert{n="EXPNS"; f="<< EXPNS : : forall x,y~Classifier forall r1,r1~Region are "+
           "( (Location(x)=r1 and Location(y)=r2 and PartOf(x,y)) implies RegionContainment(r2,r1) ) >>"; t="";}

    predicate AtomicRegion {
        doc /* SFS:  A region is atomic, Ar , when it contains no other regions (in the location relation).
         * This is the "A" operator (df-rat). */
        @Assert{n="AtomicRegion"; f="<< AtomicRegion : r~Region : "+
                "forall r1~Region are ( RegionContainment(r,r1) implies r = r1 ) >>"; t="df-rat";}
        in r : Region;
        language "Domain" /* A : r~Region : forall r1~Region are ( RegionContainment(r,r1) implies r = r1 ) */
    } 

    // Atomic regions are disjoint (df-rdi)
    @Assert{n="AtomicRegionDisjoint"; f="<< AtomicRegionDisjoint : :"+ 
        "forall r1~Region r2~Region are "+
        "   ( (AtomicRegion(r1) and AtomicRegion(r2)) implies "+
        "     (not RegionOverlap(r1,r2) or r1=r2) ) >>"; t="df-rdi";}  

    // Atomic parts have atomic regions
    @Assert{n="APAR"; f="<< APAR : : forall x~Occurrence forall r~Region :"+
            "(Location(x)=r and AtomicPart(x)) implies AtomicRegion(r) >>"; t="df-apar";}
 
    // Adjacent points are infinitessimly close, the set of adjacent points to p
    // is Adj(p) defined by df-adjp

    function RegionSurface {
        doc /* SFS: The surface of a region is all the points on its boundary */
        @Assert{n="RegionSurface"; f="<< RegionSurface : r~Region := result~Surface | "+
                "forall p~Point are (PointOnSurface(p,result) and PointInRegion(p,r) implies "+
                "  exists p2~Point that ( p2 in Adj(p) and not PointInRegion(p2,r) ) ) >>"; t="df-rsurf";}
        in r : Region;
        return result : Surface;
        inv { r.frameOfReference == (result as Surface).frameOfReference}
    }
  
    function RegionInterior {
        doc /* SFS:  The interior of a region includes all the points in a region 
          * not on its surface */
        @Assert{n="RegionInterior"; f="<< RegionInterior : r~Region := result~Region | "+
            "forall p~Point are (PointInRegion(p,result) implies "+
            "  (PointInRegion(p,r) and not PointOnSurface(p,RegionSurface(r))) ) >>"; t="df-rint";}
        in r : Region;
        return result : Region;
        inv { r.frameOfReference == (result as Region).frameOfReference}
    }

    function RegionFilm {
        doc /* SFS: The film of a region is a surface of which it's the interior */
        @Assert{n="RegionFilm"; f="<< RegionFilm : r~Region := result~Surface | "+
            " forall p~Point are ( PointOnSurface(p,result) implies "+
            " (not PointInRegion(p,r) and exists p2~Point that "+
            "    (PointOnSurface(p2,RegionSurface(r)) and p2 in Adj(p)))) >>"; t="df-rfilm";}
        in r : Region;
        return result : Surface;
        inv { r.frameOfReference == (result as Surface).frameOfReference}
    }

    predicate ExternallyConnected {
        doc /* SFS:  This is the externally connected (EC) relation  of Region Connection Calculus
          * some point on the film of r1 is on the surface of r2 */
        @Assert{n="ExternallyConnected"; f="<< ExternallyConnected : r1~Region, r2~Region : "+
            " exists p~Point that ( PointOnSurface(p,RegionFilm(r1)) and PointOnSurface(p,RegionSurface(r2)) ) >>"; t="df-rec";}
        in r1 : Region;
        in r2 : Region;
        inv { r1.frameOfReference == r2.frameOfReference }
        language "Domain" /* EC : r1~Region, r2~Region : 
          * exists p~Point that ( On(p,RegionSurface(r1)) and On(p,RegionSurface(r2)) ) */
    }

    //  predicate FilmConnected {
    //     doc /* SFS:  This is neeeded for Occurences::JustOutsideOf. */
    //     in r1 : Region;
    //     in r2 : Region;
    //     inv { r1.frameOfReference == r2.frameOfReference }
    //     language "Domain" /* FilmConnected : r1~Region, r2~Region : 
    //       * exists p~Point that ( On(p,RegionFilm(r1)) and On(p,RegionFilm(r2)) ) */
    // }
   
}