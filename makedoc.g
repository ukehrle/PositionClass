#
# PositionClass: Provides functions that, given a set of representatives of an equivalence class and an element, finds in which class an element is.
#
# This file is a script which compiles the package manual.
#
if fail = LoadPackage("AutoDoc", "2018.02.14") then
    Error("AutoDoc version 2018.02.14 or newer is required.");
fi;

AutoDoc( rec( scaffold := true, autodoc := true ) );
