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

// (311)a

G := quo <F | Comms, a^(p^2) = a2, a1^(p) = 1, ga^(p) = 1>;
Append (~L, G);

// (221)b

G := quo <F | Comms, a^p = a2, a1^(p) = 1, ga^(p^2) = 1>;
Append (~L, G);

// (2111)d

G := quo <F | Comms, a^(p) = 1, a1^p = 1, ga^(p^2) = 1>;
Append (~L, G);

return L;
end function;

My2C := function(p)

K := GF(p);
w := PrimitiveRoot(p);

Z := Integers ();
    nu := Z ! (NonQuadraticResidue (p)); // nu

F<a, a1, a2, b, ga> := FreeGroup (5);
Alpha := [a, a1, a2];
Beta := [b, ga];

// common relations, typically commutators
Comms := [
(a1, a) = a2, (a2, a)= 1, (a1, a2) = 1,
(b, ga) = 1, a2^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j
 in [1..3]]: i in [1..2]]);

L := [];

// (2111)a

G := quo <F | Comms, a^(p) = a2, a1^p = 1,
b^p = 1, ga^p = 1>;
Append (~L, G);

// (2111)b

G := quo <F | Comms, a^(p) = 1, a1^p = 1,
b^p = 1, ga^p = a2>;
Append (~L, G);

// (1^5)

G := quo <F | Comms, a^(p) = 1, a1^p = 1,
b^p = 1, ga^p = 1>;
Append (~L, G);

return L;
end function;

My3B := function(p)

K := GF(p);

w := PrimitiveRoot(p);

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

Z := Integers ();
    nu := Z ! (NonQuadraticResidue (p)); // nu

F<a, a1, a2, a3, ga> := FreeGroup (5);
Alpha := [a, a1, a2];
Beta := [a3, ga];

// common relations, typically commutators
Comms := [
(a1, a) = a2, (a2, a)= a3, (a1, a2) = 1, (a3, ga) = 1,
a2^p = 1, a3^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j
 in [1..3]]: i in [1..2]]);

L := [];

// (2111)a

G := quo <F | Comms, a^(p) = a3, a1^p = 1, ga^p = 1>;
Append (~L, G);

// (2111)b_r

for r in [1, nu] do
  G := quo <F | Comms, a^p = 1, a1^(p) = a3^r, ga^p = 1>;
  Append (~L, G);
end for;

// (1^5)

G := quo <F | Comms, a^p = 1, a1^(p) = 1, ga^p = 1>;
Append (~L, G);

return L;
end function;

Table1rank1 := function(p)
return My2B(p) cat My2C(p) cat My3B(p);
end function;

CheckTable1rank1 := function (L, p)

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

Z := Integers ();
    nu := Z ! (NonQuadraticResidue (p)); // nu

count := 0;
H := [];
S := [];
MinDeg := [];
GMinDeg := [];

// phi_2(311)a

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4];
Append (~H, sub< F | Alpha[1], Alpha[2], Alpha[3]>);
Append (~S, sub< F | Alpha[2]>);
Append (~MinDeg, p^3);
Append (~GMinDeg, p^3 + p);

// phi_2(221)b

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4];
Append (~H, sub< F | Alpha[1], Alpha[2], Alpha[3]>);
Append (~S, sub< F | Alpha[2]>);
Append (~MinDeg, p^2);
Append (~GMinDeg, 2*p^2);

// phi_2(2111)d

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4];
Append (~H, sub< F | Alpha[1], Alpha[2], Alpha[3]>);
Append (~S, sub< F | Alpha[2]>);
Append (~MinDeg, p^2);
Append (~GMinDeg, 2*p^2);

// phi_2(2111)a

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5];
Append (~H, sub< F | Alpha[1], Alpha[2], Alpha[3]>);
Append (~S, sub< F | Alpha[2]>);
Append (~MinDeg, p^2);
Append (~GMinDeg, p^2 + 2*p);

// phi_2(2111)b

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5];
Append (~H, sub< F | Alpha[1], Alpha[2], Alpha[3], Alpha[5]>);
Append (~S, sub< F | Alpha[2]>);
Append (~MinDeg, p^3);
Append (~GMinDeg, p^3 + p);

// phi_2(1^5)

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5];
Append (~H, sub< F | Alpha[1], Alpha[2], Alpha[3]>);
Append (~S, sub< F | Alpha[2]>);
Append (~MinDeg, p^2);
Append (~GMinDeg, p^2+ 2*p);

// phi_3(2111)a

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5];
Append (~H, sub< F | Alpha[1], Alpha[2], Alpha[3], Alpha[4]>);
Append (~S, sub< F | Alpha[2], Alpha[3]>);
Append (~MinDeg, p^2);
Append (~GMinDeg, p^2+ p);

// phi_3(2111)b_r

for r in [1, nu] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5];
Append (~H, sub< F | Alpha[1], Alpha[2], Alpha[3], Alpha[4]>);
Append (~S, sub< F | Alpha[3]>);
Append (~MinDeg, p^3);
Append (~GMinDeg, p^3+ p);
end for;

// phi_3(1^5)

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5];
Append (~H, sub< F | Alpha[1], Alpha[2], Alpha[3], Alpha[4]>);
Append (~S, sub< F | Alpha[2], Alpha[3]>);
Append (~MinDeg, p^2);
Append (~GMinDeg, p^2+ p);

return H, S, MinDeg, GMinDeg;
end function;

MAX := 13^5;

for p in PrimesInInterval (5, 13) do 
   "\n process prime ", p;
   L := Table1rank1(p);

   H, S, MinDeg, GMinDeg := CheckTable1rank1(L, p);

   for i in [1..#L] do
     G := L[i];
     Q, phi := pQuotient(G, p, 6);

     // setup perm rep for non-abelian factor H 
     R := phi (H[i]);
     A := phi (S[i]);
     m := Index(R, A);
     C := Core(R, A);
     assert #C eq 1;
     phiA := CosetAction (R, A);
     J := Image (phiA);
     assert #J eq #R;
     assert Degree (J) eq MinDeg[i];

     // setup perm rep for G 
     I, IS := DetermineMinRep (G, Q, R, [A], phi);
     assert #&meet[Core (Q, s): s in IS] eq 1;
     assert #I eq #Q;
     if #Q le MAX then assert IsIsomorphic (I, Q); end if;
     assert Degree (I) eq GMinDeg[i];
  end for;

end for;
