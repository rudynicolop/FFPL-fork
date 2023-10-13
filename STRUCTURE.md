# Structure of the Coq development

This document roughly maps the lecture notes and exercises to the Coq development.
The files matching the course content are included in the `theories/type_systems` folder.
All of the paths given below are to be understood relative to that folder.

## Chapter 1

### Section 1.0

The definition of terms, values, and substitution can be found at the top of `stlc/lang.v`.

The definition of closed terms is in `stlc/closed.v`.
For Coq engineering reasons this departs a bit from the on-paper definition, but it is equivalent.

The file `stlc/notation.v` contains some Coq declarations that lets us write lambda-calculus terms in Coq more conveniently.
In `stlc/lang.v` start around line 100 you can find an explanation of how these notations work.

### Section 1.1

Big-step, structural small-step, and contextual small-step semantics are all defined in `stlc/lang.v`.
Structural semantics are the easiest to define so they come first.
Big-step semantics requires reasoning about the conversion between values and expressions.

### Section 1.2

The examples for what you can do with the untyped lambda-calculus can be found in `stlc/untyped.v`.