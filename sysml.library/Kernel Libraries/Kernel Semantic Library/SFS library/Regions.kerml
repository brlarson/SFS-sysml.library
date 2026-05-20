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
        * well-defined. (absolute time)
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
        *  SFS:  Region is a metaphysical three-dimensional volume.
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
        * This is the "L" exact location primitive. (df-lfu)
        * Uses o.frameOfReference as the frame-of-reference for the region.
        */
        language "Domain" /* L : o : Occurrence := result */
        in o : Occurrence;
        return result : Region;
        inv { o.isClosed and o.innerSpaceDimension == 3 and o.outerSpaceDimension == 3
            and o.frameOfReference == (result as Region).frameOfReference 
            }
   }

    // SFS:  Two things having the same location are the same thing (df-lfu)
    language "Domain" /* forall x~Occurrence forall r1,r2~Region are
      *  ( (L(x)=r1 and L(x)=r2) implies r1=r2 ) */


    predicate PointInRegion {
        doc /* SFS: Point is contained in Region */
        in point : Point;
        in region : Region;
        inv { point.frameOfReference == region.frameOfReference
            and point.frameOfReference == region.frameOfReference 
        }
        language "Domain" /* In : point~Point, region~Region : point in region */
    }

    predicate PointOnSurface {
        doc /* SFS: Point is on a Surface */
        in point : Point;
        in surface : Surface;
        inv { point.frameOfReference == surface.frameOfReference }
        language "Domain" /* On : point~Point, surface~Surface : point on surface" */
    }

    predicate RegionOverlap {
        doc /* SFS:  Two regions containing the same point overlap. 
            * This is the "O" relation (df-rov).
            * Regions are disjoint if they don't overlap */
        in r1 : Region;
        in r2 : Region;
        inv { r1.frameOfReference == r2.frameOfReference }
        language "Domain" /* O : r1~Region, r2~Region : exists p~Point that (In(p,r1) and In(p,r2)) */
    }

        doc /* SFS: Regions overlap only if one contains the other. This property is called no interpenetration. */
        language "Domain" /* forall r1,r1~Region are 
          O(r1,r2) implies (RegionContainment(r1,r2) or RegionContainment(r2,r1)) */

    predicate RegionContainment {
        doc /* SFS:  A region contains another, when it contains all of its points. 
            * This is the "C" relation (df-rco). */
        in r1 : Region;
        in r2 : Region;
        inv { r1.frameOfReference == r2.frameOfReference }
        language "Domain" /* RegionContainment : r1~Region, r2~Region : forall p~Point are (In(p,r2) implies In(p,r1)) */
    }

        doc /* SFS: Parthood implies regional containment. This property is called expansivity. */
        language "Domain" /* forall x,y~Classifier forall r1,r1~Region are 
          ( (L(x)=r1 and L(y)=r2 and PartOf(x,y)) implies RegionContainment(r1,r2) */

    predicate AtomicRegion {
        doc /* SFS:  A region is atomic, Ar , when it contains no other regions (in the location relation).
         * This is the "A" operator (df-rat). */
        in r : Region;
        language "Domain" /* A : r~Region : forall r1~Region are ( RegionContainment(r,r1) implies r = r1 ) */
    } 

    // Atomic regions are disjoint (df-rdi)  
    language "Domain" /* AtomicRegionDisjoint : : 
        * forall r1~Region r2~Region are 
        *   ( (AtomicRegion(r1) and AtomicRegion(r2)) implies
        *   (not RegionOverlap(r1,r2) or r1=r2) ) */ 
    
    function RegionInterior {
        doc /* SFS:  The interior of a region includes all the points in a region 
          * not on its surface */
        in r : Region;
        return result : Region;
        inv { r.frameOfReference == (result as Region).frameOfReference}
        language "Domain" /* RegionInterior : r~Region := result~Region | 
          * exists s~Surface that forall p~Point are ( In(p,result) implies 
          * (In(p,r) and not On(p,RegionSurface(r))) ) */
    }

    function RegionSurface {
        doc /* SFS: The surface of a region is all the points on its boundary */
        in r : Region;
        return result : Surface;
        inv { r.frameOfReference == (result as Region).frameOfReference}
        language "Domain" /* RegionSurface : r~Region := result~Surface | 
          * exists r1~Region that forall p~Point are ( On(p,result) implies 
          *   (In(p,r) and not In(p,RegionInterior(r))) ) */
    }

    function RegionFilm {
        doc /* SFS: The film of a region is a surface of which it's the interior */
        in r : Region;
        return result : Surface;
        inv { r.frameOfReference == (result as Region).frameOfReference}
        language "Domain" /* RegionFilm : r~Region := result~Surface | 
          * exists r1~Region that forall p~Point are ( On(p,result) implies 
          *   (RegionInterior(r1)=r and RegionSurface(r1)=result) ) */
    }

    predicate ExternallyConnected {
        doc /* SFS:  This is the externally connected (EC) relation  of Region Connection Calculus */
        in r1 : Region;
        in r2 : Region;
        inv { r1.frameOfReference == r2.frameOfReference }
        language "Domain" /* EC : r1~Region, r2~Region : 
          * exists p~Point that ( On(p,RegionSurface(r1)) and On(p,RegionSurface(r2)) ) */
    }

     predicate FilmConnected {
        doc /* SFS:  This is neeeded for Occurences::JustOutsideOf. */
        in r1 : Region;
        in r2 : Region;
        inv { r1.frameOfReference == r2.frameOfReference }
        language "Domain" /* FilmConnected : r1~Region, r2~Region : 
          * exists p~Point that ( On(p,RegionFilm(r1)) and On(p,RegionFilm(r2)) ) */
    }
   
}