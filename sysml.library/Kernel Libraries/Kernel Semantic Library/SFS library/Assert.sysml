//standard 
library package Assert {

private import ScalarValues::String;

metadata def Assert {
	attribute n[0..1] : String;  //name
  attribute f[1..*] : String;  //formula(s)
  attribute t[0..*] : String;  //theorem name(s) which attests to this @Assert
}

metadata def Invariant {
	attribute n[0..1] : String;  //name
  attribute inv[1] : String;   //invariant formula
  attribute t[0..*] : String;  //theorem name(s) which attests to this @Invariant
}

}