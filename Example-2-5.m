// Example 2.5: construct minimal degree representation for phi_2(32)a_1

load "setup-permrep.m";

SetEchoInput (true);

p := 7;

F<a, a1, a2> := FreeGroup (3);
Alpha := [a, a1];
Beta := [a2];

// common relations, typically commutators
Comms := [
(a1, a) = a2, a2^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j
 in [1..2]]: i in [1]]);

G := quo <F | Comms, a^(p^2) = a2, a1^(p^2) = 1>;
Q, phi := pQuotient (G, p, 6);
H1 := sub<Q | [phi (G.1)]>;
H2 := sub<Q | [phi (G.2)]>;
Core (Q, H1) meet Core (Q, H2);
tau1 := CosetAction (Q, H1);
tau2 := CosetAction (Q, H2);
tau := PermutationRepresentationSumH (Q, [tau1, tau2]);
I := Image (tau);
#I;
IsIsomorphic (I, Q);
