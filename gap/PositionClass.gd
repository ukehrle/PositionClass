#
# PositionClass: Provides functions that, given a set of representatives of an
#  equivalence class and an element, finds in which class an element is.
#
#! @Chapter Introduction
#!
#! PositionClass is a package which does some
#! interesting and cool things
#!
#! @Chapter Functionality
#!
#!
#! @Section Example Methods
#!
#! This section will describe the example
#! methods of PositionClass


#############################################################################
##
#! @Description
#! The info class for computations with InduceReduce
#!
DeclareInfoClass("InfoPositionClass");

DeclareAttribute( "PositionClassRecord", IsObject, "mutable" );

#############################################################################
#!
#! @Description
#! A record containing options used in PositionClass
#! TODO: Use gap option stack thingy instead
#!
DeclareGlobalVariable( "PosClassOptions" );


DeclareGlobalFunction( "PosClassInitTests" );

# TODO: fix description to account for all methods installed
#! @Description
#! given a PosClass record <r>, an element <g>, and <maxcost>, tries to determine
#! the class of <g> using only tests of cost at most <maxcost>.
#! Returns a list of possible class indices.
DeclareOperation ( "PositionClass", [ IsObject, IsObject, IsInt ]);
DeclareOperation ( "PositionClass", [ IsObject, IsObject ] );
