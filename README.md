hinitiality
===========

This repository contains developments related to homotopy-inductive types, i.e.,
inductive types where the computation rules are stated using propositional instead
of definitional equality.

The organization is as follows.

------------------------------------------------------------------------------

Folder "two-hinit"

Contains the characterization of the type Two as a homotopy-initial
algebra. More precisely, we give 3 different characterizations of Two and show that
they are all equivalent:

   - Two with dependent elimination and computation rules.
   - Two with simple elimination and computation rules,
     together with uniqueness and coherence rules.
   - Two as a homotopy-initial algebra.

The files are organized as follows:

   - File "two.v" contains the 3 characterizations of Two
   - File "two_alg.v" contains the definition of algebras, homomorphisms,
     h-initiality, and related concepts.
   - File "hom_paths.v" contains the characterization of the path space
     of homomorphisms as the space of 2-cells.
   - File "dep_imp_simp.v" shows that the dependent rules imply the simple ones.
   - File "simp_imp_dep.v" shows that the simple rules imply the dependent ones.
   - File "dep_eq_simp.v" shows that the dependent and simple rules are equivalent
     as types.
   - File ""simp_eq_hinit.v" shows that the simple rules and h-initiality are
     equivalent as types.

------------------------------------------------------------------------------

Folder "w-hinit"

Contains the characterization of the W-type of well-founded trees W A B as a
homotopy-initial algebra. More precisely, we give 3 different characterizations
of W A B and show that they are all equivalent:

   - W A B with dependent elimination and computation rules.
   - W A B with simple elimination and computation rules,
     together with uniqueness and coherence rules.
   - W A B as a homotopy-initial algebra.

The files are organized as follows:

   - File "w.v" contains the 3 characterizations of W A B
   - File "w_alg.v" contains the definition of algebras, homomorphisms,
     h-initiality, and related concepts.
   - File "hom_paths.v" contains the characterization of the path space
     of homomorphisms as the space of 2-cells.
   - File "dep_imp_simp.v" shows that the dependent rules imply the simple ones.
   - File "simp_imp_dep.v" shows that the simple rules imply the dependent ones.
   - File "dep_eq_simp.v" shows that the dependent and simple rules are equivalent
     as types.
   - File ""simp_eq_hinit.v" shows that the simple rules and h-initiality are
     equivalent as types.

------------------------------------------------------------------------------

Folder "nat-from_w"

Contains the encoding of natural numbers as a W-type.
The files are organized as follows:

   - File "types.v" contains the definitions of the inductive types Zero, One,
     Two, and W A B.
   - File "nat.v" contains the encoding of natural numbers as a W-type.





Repository last updated: April 19, 2013
Authors: Steve Awodey, Nicola Gambino, Kristina Sojakova
Contact : awodey@cmu.edu
          nicola.gambino@gmail.com
          kristinas@cmu.edu

