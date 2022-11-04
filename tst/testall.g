#
# PositionClass: Provides functions that, given a set of representatives of an equivalence class and an element, finds in which class an element is.
#
# This file runs package tests. It is also referenced in the package
# metadata in PackageInfo.g.
#
LoadPackage( "PositionClass" );

TestDirectory(DirectoriesPackageLibrary( "PositionClass", "tst" ),
  rec(exitGAP := true));

FORCE_QUIT_GAP(1); # if we ever get here, there was an error
