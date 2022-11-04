# record whose components are available default test functions
DeclareGlobalVariable( "PosClassConjugacyTestFunctions" );

# list of functions to be used by PositionClass by default
DeclareGlobalVariable( "PosClassConjugacyDefaultFunctions" );

DeclareOperation ( "PositionClass", [ IsGroup, IsMultiplicativeElementWithInverse ]);
DeclareOperation ( "PositionClass", [ IsGroup, IsMultiplicativeElementWithInverse, IsInt ]);
DeclareOperation ( "PositionClass", [ HasPositionClassRecord, IsMultiplicativeElementWithInverse, IsInt ]);
DeclareOperation ( "PositionClass", [ HasPositionClassRecord, IsMultiplicativeElementWithInverse]);

DeclareAttribute( "PowerMap", IsConjugacyClassGroupRep );
