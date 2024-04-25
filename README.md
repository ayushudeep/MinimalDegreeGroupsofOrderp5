
This repository contains data and code related to the preprint:

Sunil Kumar Prajapati, and Ayush Udeep.
Minimal degrees for faithful permutation representations 
of groups of order $p^5$ where $p$ is an odd prime.

It is designed for use with Magma.

Each directory Table-J where J \in {1,...,3} encodes data recorded in 
the corresponding table of the paper. 

The other files are:
* BehraveshDelfanip5GroupsTest.m: Checks the number of non-isomorphic
  groups of order p^5, for an explicit prime p, that appear in the paper:
  
  H. Behravesh and M. Delfani, On faithful quasi-permutation representations
   of groups of order p^5, J. Algebra Appl., 17(7) (2018), 1850127 (12 pages).

* ThreeIsomorphicGroups.m: Establishes isomorphism for three groups listed in the paper.

* setup-permrep.m: Various functions needed to set up the 
associated representations for an explicit prime p. 

* Saunders-mindeg.m: An implementation in Magma of the 
algorithm of Elias et al. (2010) developed by Neil Saunders.


Here's an example of the use of the code.

% cd Table-2 
% magma Table2-Center-rank1.m
// For each prime p in range [5..11] the groups of order p^5 with center of rank 1 listed in Table 2 are setup and their minimal degree permutation representations are constructed. 

Prepared April 2024
