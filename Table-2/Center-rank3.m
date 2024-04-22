load "../setup-permrep.m";

My2A := function(p)

F<a, a1, a2> := FreeGroup (3);
Alpha := [a, a1];
Beta := [a2];

// common relations, typically commutators
Comms := [
(a1, a) = a2, a2^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j
 in [1..2]]: i in [1]]);

L := [];

// (221)d

G := quo <F | Comms, a^(p^2) = 1, a1^(p^2) = 1>;
Append (~L, G);

return L;
end function;

Check2 := function (L, p)

count := 0;
H1 := [];
H2 := [];
H3:= [];
MinDeg := [];

// (221)d

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; 
Append (~H1, sub<F | Alpha[1], Alpha[3]>);
Append (~H2, sub<F | Alpha[2], Alpha[3]>);
Append (~H3, sub<F | Alpha[1], Alpha[2]^(p)>);
Append (~MinDeg, 3*p^2);

return H1, H2, H3, MinDeg;
end function;

MAX := 13^5;

for p in PrimesInInterval (5, 13) do 
   "\n process prime ", p;
   L := My2A(p);
   H1, H2, H3, MinDeg := Check2(L, p);

   for i in [1..#L] do
     G := L[i];
     Q, phi := pQuotient(G, p, 6);
     A := phi (H1[i]);
     B := phi (H2[i]);
     C := phi (H3[i]);
     m1 := Index(Q, A);
     m2 := Index(Q, B);
     m3 := Index(Q, C);
     m := m1 + m2 + m3;
     C1 := Core(Q, A);
     C2 := Core(Q, B);
     C3 := Core(Q, C);
     CI := C1 meet C2 meet C3;
     assert #CI eq 1;
     phiA := CosetAction (Q, A);
     phiB := CosetAction (Q, B);
     phiC := CosetAction (Q, C);
     pi := PermutationRepresentationSumH (Q, [phiA, phiB, phiC]);
     J := Image (pi);
     assert #J eq #Q;
     if #J le MAX then assert IsIsomorphic (J, Q); end if;
     assert Degree (J) eq m;
     assert Degree (J) eq MinDeg[i];
   end for;
end for;
