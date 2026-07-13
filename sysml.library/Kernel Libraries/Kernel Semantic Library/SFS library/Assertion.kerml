library package Assertion {

// use language "Domain" instead

private import Metaobjects::Metaobject;
private import ScalarValues::String;

metaclass Assert specializes Metaobject {
	doc
	/*
	 * Assert attaches temporal logic formulas to KerML elements
	 */
	feature n[0..1] : String;  //name
	feature f[1..*] : String;  //formula
	feature t[0..*] : String;  //theorem name which attests to this @Assert

}

}