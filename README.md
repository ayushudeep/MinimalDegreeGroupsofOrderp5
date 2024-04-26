
This repository contains data and code related to the preprint:

Sunil Kumar Prajapati and Ayush Udeep.
Minimal degrees for faithful permutation representations 
of groups of order $p^5$ where $p$ is an odd prime.

It is designed for use with Magma.

Each directory Table-J where J \in {1,...,3} encodes data recorded in 
the corresponding table of the paper. 

The other files are:

* setup-permrep.m: various functions needed to set up the 
associated representations for an explicit prime p. 

* Saunders-mindeg.m: an implementation in Magma of the 
algorithm of Elias et al. (2010) developed by Neil Saunders.

* Example*.m: code to realise the examples described in the paper.

Here's an example of the use of the code.

% cd Table-2 

% magma Table2-Center-rank1.m

The file is Center-rank1.m. 

Prepared April 2024
