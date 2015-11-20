# unumd
Unums (Universal Numbers) in D. See http://www.slideshare.net/insideHPC/unum-computing-an-energy-efficient-and-massively-parallel-approach-to-valid-numerics for an introduction.

This attempt at an implementation does not exactly implement Unums as described by John Gustafson, with their dynamic exponent and fraction components.
Instead it uses native floating point types as fixed storage, thereby putting an upper limit on the number of bits available to the exponent and fraction.

It does add the `Ubit` (which signals whether a Unum is exact or inexact) and tracks the number of significant bits (as opposed to regular floating point values which assume that all bits are significant).

The `Ubit` and `precision` fields are stored in the native floating point value, overwriting the least significant bits.
For inexact Unums this has the funny benefit of keeping their value within the Unum range they're representing: lower-bound ≤ float-value ≤ upper-bound. For exact Unums these utag bits will have to be cleared to retrieve the correct value.
