# Experimental special-unitary sharing

This directory contains an unfinished SU extension with 36 source modules.
It is excluded from `GS`, `GSChecked` and the supported verification scope.
The O/U library does not depend on it.

The construction imposes determinant one on every physical block and uses
matrix exponentials for updates. Compilation issues remain in the complex
exponential and tangent-direction modules; downstream geometric statements
must not be treated as established results.

The sources retain their `GS.SpecialUnitarySharing` namespaces. To develop
this extension, use the `GS/` directory here as an overlay on the main source
tree and include the required modules in the build. Verify the complete
dependency chain before using its results.

See [the mathematical guide](../../docs/SPECIAL_UNITARY_SHARING.md).
