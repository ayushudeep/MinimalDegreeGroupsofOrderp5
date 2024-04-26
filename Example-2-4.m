// Example 2.4: construct minimal degree perm rep for phi_2(311)a

load "setup-permrep.m";

SetEchoInput (true);

My2 := function(p)

F<a, a1, a2, ga> := FreeGroup (4);
Alpha := [a, a1, a2];
Beta := [ga];

// common relations, typically commutators
Comms := [
(a1, a) = a2, (a2, a)= 1, (a1, a2) = 1, a2^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j
 in [1..3]]: i in [1]]);

L := [];

// (311)a

G := quo <F | Comms, a^(p^2) = a2, a1^(p) = 1, ga^(p) = 1>;
Append (~L, G);

return L;
end function;

p := 7;

L := My2(p);

G:= L[1];
Q, phi := pQuotient (G, p, 6);

H := sub <G | [G.i: i in [1..3]]>;

ImH:=phi (H);

H1 := sub<ImH | [phi (G.i): i in [2]]>;
Core (ImH, H1);
tau1 := CosetAction (ImH, H1);
tau := PermutationRepresentationSumH (ImH, [tau1]);
I := Image (tau);
#I;
IsIsomorphic (I, ImH);

I, S := DetermineMinRep (G, Q, ImH, [H1], phi);

// check S 
&meet[Core (Q, s): s in S];

assert IsIsomorphic (I, Q);

// alternative to set it directly 
K:=sub< G | [G.i: i in [4]]>;   
K := phi (K);
phi1 := CosetAction (Q, sub< Q |  H1, K>);
phi2 := CosetAction (Q, ImH);
phi :=PermutationRepresentationSumH (Q, [phi1, phi2]);
J := Image (phi);

