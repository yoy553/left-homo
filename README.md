This directory contains Coq scripsts (ver.8.6) discussed in the paper. 

Title : Generalized Equivalence of Leftward and Homomorphic Functions
Author: Yosuke Yamamot and Chris Dutchyn


FoldLib.v  : Ltac scripts (section 2.2): linU_inclusion_tac (for Property 3),
	     linU_slideout_tac (for Property 4),
             and linU_homomorphism_tac (for Meta-Proposition 1) 

MyLib.v    : Library for the project

cata.v     : List-catamorphisms  (section 2)

./ISort
ISort.v    : insertion sort (section 1)

./QSort    : quicksort (3.1)
AnaSortEq.v: Equivalence between quiksort and selection sort
QSort.v    : quicksort 
FindMinN.v : findmin function called by selectino sort defined in AnaSortEq.v
Replace.v  : replace function called by selectino sort defined in AnaSortEq.v

./Fact     : 
Fact.v     : factorial function (section 3.2)


