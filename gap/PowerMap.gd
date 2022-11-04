DeclareAttribute( "PowerMap", IsConjugacyClassGroupRep );


DeclareProperty( "AllClassesHavePowerMaps", IsGroup );
DeclareProperty( "UnderlyingGroupHasClassPowerMaps", IsNearlyCharacterTable );

DeclareOperation( "PosClassComputeAllPowerMaps", [IsGroup]);
DeclareOperation( "PosClassExportPowerMaps", [IsGroup]);
DeclareOperation( "PowerMap",
    [ UnderlyingGroupHasClassPowerMaps and IsNearlyCharacterTable, IsInt, IsInt ]);
