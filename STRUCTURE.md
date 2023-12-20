# Structure of the Coq development

This document roughly maps the lecture notes and exercises to the Coq development.
The files matching the course content are included in the `theories/type_systems` folder.
All of the paths given below are to be understood relative to that folder.

## Chapter 1: Simply Typed Lambda Calculus

The definition of terms, values, and substitution can be found at the top of `stlc/lang.v`.

The definition of closed terms is in `stlc/closed.v`.
For Coq engineering reasons this departs a bit from the on-paper definition, but it is equivalent.

The file `stlc/notation.v` contains some Coq declarations that lets us write lambda-calculus terms in Coq more conveniently.
In `stlc/lang.v` start around line 100 you can find an explanation of how these notations work.

### Section 1.1: Operational Semantics

Big-step, structural small-step, and contextual small-step semantics are all defined in `stlc/lang.v`.
Structural semantics are the easiest to define so they come first.
Big-step semantics requires reasoning about the conversion between values and expressions.
`big_step_step` shows that big-step semantics implies small-step semantics.

Lemma 1 is `fill_contextual_step`, and Lemma 2 is `fill_comp`.

### Section 1.2: The Untyped Lambda-Calculus

The examples for what you can do with the untyped lambda-calculus can be found in `stlc/untyped.v`.
This is using the definitions and theory for closed terms in `stlc/closed.v`.
(We don't rigorously develop that theory in the lecture notes.)

### Section 1.3: Typing

The definition of types and curry-style typing is at the top of `stlc/types.v`.

### Section 1.4: Type Safety

All the lemmas, theorems, and corollaries from this section are in `stlc/types.v`.
The Coq file contains comments explaining with Lemma/... the proofs correspond to.

### Section 1.5: Termination

All the lemmas, theorems, and corollaries from this section are in `stlc/logrel.v`.
This is using the definitions and theory for parallel substitution in `stlc/parallel_subst.v`.
(We don't rigorously develop that theory in the lecture notes.)
The Coq file contains comments explaining with Lemma/... the proofs correspond to.

## Chapter 2: De Bruijn Representation

The files for this chapter are located in `stlc_de_bruijn`.
The contextual operational semantics is in `lang.v`, the type system and type safety proof in `types.v`, and the logical relation and termination proof in `logrel.v`.

## Chapter 3: System F: Polymorphism and Existential Types

### Section 3.1: System F

The language definition is in `systemf/lang.v`; the typing rules are at the top of `systemf/types.v`.

### Section 3.2: Encoding data types

This section has not been formalized in Coq.

### Section 3.3: Data abstraction with existential types

This section has not been formalized in Coq.

### Section 3.4: System F with De Bruijn representation

The definitions in Coq all use De Bruijn representation.

### Section: 3.5: Type Safety

The type safety proof can be found in `systemf/types.v`.

### Section 3.6: Termination

The logical relation for the termination proof can be found in `systemf/logrel.v`.

### Section 3.2: Type Casts Break Termination

This section has not been formalized in Coq.

### Section 3.8: Free Theorems

The proofs of the free theorems can be found in `systemf/free_theorems.v`.

### Section 3.9: Semantic Type Safety of Unsafe Code with Existential Types

The soundness proof of MyBit_unsafe can be found in `systemf/existential_invariants.v`.

## Chapter 4: Mutable State

The language definition is in `systemf_state/lang.v`.

### Section 4.1: Data Abstraction via Local State

This section has not been formalized in Coq.

### Section 4.2: Type Safety

The typing rules and type safety proof are in `systemf_state/types.v`.

### Section 4.3: Recursion via State

This section has not been formalized in Coq.

### Section 4.4: Termination

The big-step semantics are in `systemf_state/big_step.v`.
The logical relation and termination proof are in `systemf_state/logrel.v`.

### Section 4.5: Semantic Type Safety of Unsafe Code with Local State

The soundness proof of MyMutBit_unsafe is in `systemf_state/mutbit.v`.
