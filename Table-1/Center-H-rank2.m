load "../setup-permrep.m";

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

My2B := function(p)

K := GF(p);
w := PrimitiveRoot(p);
Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a, a1, a2, ga> := FreeGroup (4);
Alpha := [a, a1, a2];
Beta := [ga];

// common relations, typically commutators
Comms := [
(a1, a) = a2, (a2, a)= 1, (a1, a2) = 1, a2^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j
 in [1..3]]: i in [1]]);

L := [];

// (221)a

G := quo <F | Comms, a^p = a2, a1^(p^2) = 1, ga^(p) = 1>;
Append (~L, G);

// (2111)c

G := quo <F | Comms, a^(p^2) = 1, a1^p = 1, ga^(p) = 1>;
Append (~L, G);

return L;
end function;

CheckTable1Rank2 := function (L, p)

count := 0;
H := [];
T1 := [];
T2 := [];
MinDeg := [];
GMinDeg := [];

// phi_2(221)a

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4];
Append (~H, sub< F | Alpha[1], Alpha[2], Alpha[3]>);
Append (~T1, sub<F | Alpha[1]>);
Append (~T2, sub<F | Alpha[2]>);
Append (~MinDeg, 2*p^2);
Append (~GMinDeg, 2*p^2 + p);

// phi_2(2111)c

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4];
Append (~H, sub< F | Alpha[1], Alpha[2], Alpha[3]>);
Append (~T1, sub<F | Alpha[1]>);
Append (~T2, sub<F | Alpha[2], Alpha[3]>);
Append (~MinDeg, 2*p^2);
Append (~GMinDeg, 2*p^2 + p);

return H, T1, T2, MinDeg, GMinDeg;
end function;

MAX := 13^5;

for p in PrimesInInterval (5, 13) do 
   "\n process prime ", p;
   L := My2B(p);

   H, T1, T2, MinDeg, GMinDeg := CheckTable1Rank2(L, p);

   for i in [1..#L] do
     G := L[i];
     Q, phi := pQuotient(G, p, 6);

     // setup perm rep for non-abelian factor H 
     R := phi (H[i]);
     A := phi (T1[i]);
     B := phi (T2[i]);
     m1 := Index(R, A);
     m2 := Index(R, B);
     m := m1 + m2;
     C1 := Core(R, A);
     C2 := Core(R, B);
     C := C1 meet C2;
     assert #C eq 1;
     phiA := CosetAction (R, A);
     phiB := CosetAction (R, B);
     pi := PermutationRepresentationSumH (R, [phiA, phiB]);
     J := Image (pi);
     assert #J eq #R;
     if #J le MAX then assert IsIsomorphic (J, R); end if;
     assert Degree (J) eq m;
     assert Degree (J) eq MinDeg[i];

     // setup perm rep for G 
     I, IS := DetermineMinRep (G, Q, R, [A, B], phi);
     assert #&meet[Core (Q, s): s in IS] eq 1;
     assert #I eq #Q;
     if #Q le MAX then assert IsIsomorphic (I, Q); end if;
     assert Degree (I) eq GMinDeg[i];
   end for;
end for;
