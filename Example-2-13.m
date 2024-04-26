// Example 2.13: construct minimal degree representation for phi_2(221)c

load "setup-permrep.m";


SetEchoInput (true);

p := 7;

F<a, a1, a2, ga> := FreeGroup (4);
Alpha := [a, a1, a2];
Beta := [ga];

// common relations, typically commutators
Comms := [
(a1, a) = a2, (a2, a)= 1, (a1, a2) = 1, a2^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j
 in [1..3]]: i in [1]]);

G := quo <F | Comms, a^(p^2) = 1, a1^p = 1, ga^(p) = a2>;

Q, phi := pQuotient(G, p, 6);

// subgroup R 
PR := sub<G | (G.1^p), G.2, G.4>;  
PR := phi (PR);
// kernel of non-linear irr char. from R
PN := sub<G | (G.1^p), G.2>;  
PN := phi (PN);

// group G 
PT := sub<G | G.1, G.2, G.3, G.4>; 
PT := phi (PT);
// kernel of non-linear irr char. from T
PL := sub<G | G.2, G.4>;
PL := phi (PL);

Int := Core(Q, PN) meet Core(Q, PL);
assert #Int eq 1;

phiN := CosetAction (Q, PN);
phiL := CosetAction (Q, PL);
pi := PermutationRepresentationSumH (Q, [phiN, phiL]);
J := Image (pi);
assert #J eq #Q;
assert IsIsomorphic (J, Q);
