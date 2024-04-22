load "../setup-permrep.m";

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

My2B := function(p)

F<a, a1, a2, ga> := FreeGroup (4);
Alpha := [a, a1, a2];
Beta := [ga];

// common relations, typically commutators
Comms := [
(a1, a) = a2, (a2, a)= 1, (a1, a2) = 1, a2^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j
 in [1..3]]: i in [1]]);

L := [];

// (311)b

G := quo <F | Comms, a^(p) = 1, a1^p = 1, ga^(p^2) = a2>;
Append (~L, G);

return L;
end function;

My3A := function(p)

K := GF(p);
w := PrimitiveRoot(p);

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a, a1, a2, a3> := FreeGroup (4);
Alpha := [a, a1, a2];
Beta := [a3];

// common relations, typically commutators
Comms := [
(a1, a) = a2, (a2, a)= a3, (a1, a2) = 1,
a2^p = 1, a3^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j
 in [1..3]]: i in [1]]);

L := [];

// (311)a

G := quo <F | Comms, a^(p^2) = a3, a1^p = 1>;
Append (~L, G);

// (311)b_r

for r in [1, nu] do
  G := quo <F | Comms, a^p = 1, a1^(p^2) = a3^r>;
  Append (~L, G);
end for;

return L;
end function;

My3B := function(p)

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

// (2111)c

G := quo <F | Comms, a^p = 1, a1^(p) = 1, ga^p = a3>;
Append (~L, G);

return L;
end function;

My5 := function(p)

K := GF(p);
w := PrimitiveRoot(p);

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, b> := FreeGroup (5);
Alpha := [a1, a2, a3, a4];
Beta := [b];

// common relations, typically commutators
Comms := [
(a1, a2) = b, (a3, a1)= 1, (a1, a4) = 1,
(a2, a3) = 1, (a2, a4) = 1, (a3, a4) = b,
a2^p = 1, a3^p = 1, a4^p = 1, b^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j
 in [1..4]]: i in [1]]);

L := [];

// (2111)

G := quo <F | Comms, a1^(p) = b >;
Append (~L, G);

// (1^5)

G := quo <F | Comms, a1^(p) = 1 >;
Append (~L, G);

return L;
end function;

My7 := function(p)

K := GF(p);
w := PrimitiveRoot(p);

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a, a1, a2, a3, b> := FreeGroup (5);
Alpha := [a, a1, a2, b];
Beta := [a3];

// common relations, typically commutators
Comms := [
(a1, a) = a2, (a2, a) = a3, (b, a) = 1,
(a1, a2) = 1, (a1, b)= a3, (a2, b) = 1, 
a2^p = 1, a3^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j
 in [1..4]]: i in [1]]);

L := [];

// (2111)a

G := quo <F | Comms, a^p = a3, a1^p = 1, b^p = 1>;
Append (~L, G);

// (2111)b_r

for r in [1, nu] do
  G := quo <F | Comms, a^p = 1, b^p = 1, a1^p = a3^r>;
  Append (~L, G);
end for;

// (2111)c

G := quo <F | Comms, a^p = 1, a1^p = 1, b^p = a3>;
Append (~L, G);

// (1^5)

G := quo <F | Comms, a^p = 1, a1^p = 1, b^p = 1>;
Append (~L, G);

return L;
end function;


My8 := function(p)

F<a1, a2, b> := FreeGroup (3);
Alpha := [a1, a2]; Beta := [b];

// common relations, typically commutators
Comms := [
(a1, a2) = b, (b, a2) = b^p, b^(p^2) = 1];

L := [];

// (321)a

G := quo <F | Comms, a1^p = b, a2^(p^2) = 1>;
Append (~L, G);

return L;
end function;


My9 := function(p)

K := GF(p);
w := PrimitiveRoot(p);

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a, a1, a2, a3, a4> := FreeGroup (5);
Alpha := [a, a1, a2, a3];
Beta := [a4];

// common relations, typically commutators
Comms := [
(a1, a) = a2, (a2, a) = a3, (a3, a) = a4,
(a1, a2) = 1, (a1, a3)= 1, (a2, a3) = 1, 
a2^p = 1, a3^p = 1, a4^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j
 in [1..4]]: i in [1]]);

L := [];


// (2111)a

G := quo <F | Comms, a^p = a4, a1^p = 1>;
Append (~L, G);

// (2111)b_r

el3 := GCD(p-1, 3) - 1;
for r in [0..el3] do
  G := quo <F | Comms, a^p = 1, a1^p = a4^(w^r mod p)>;
  Append (~L, G);
end for;

// (1^5)

G := quo <F | Comms, a^p = 1, a1^p = 1>;
Append (~L, G);

return L;
end function;


My10 := function(p)

K := GF(p);
w := PrimitiveRoot(p);

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a, a1, a2, a3, a4> := FreeGroup (5);
Alpha := [a, a1, a2, a3];
Beta := [a4];

// common relations, typically commutators
Comms := [
(a1, a) = a2, (a2, a) = a3, (a3, a) = a4,
(a1, a2) = a4, (a1, a3)= 1, (a2, a3) = 1, 
a2^p = 1, a3^p = 1, a4^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j
 in [1..4]]: i in [1]]);

L := [];

// (2111)a_r

el4 := GCD(p-1, 4) - 1;
for r in [0..el4] do
  G := quo <F | Comms, a^p = a4^(w^r mod p), a1^p = 1>;
  Append (~L, G);
end for;

// (2111)b_r

el3 := GCD(p-1, 3) - 1;
for r in [0..el3] do
  G := quo <F | Comms, a^p = 1, a1^p = a4^(w^r mod p)>;
  Append (~L, G);
end for;


// (1^5)

G := quo <F | Comms, a^p = 1, a1^p = 1>;
Append (~L, G);

return L;
end function;

Table2Rank1 := function(p)
return My2B(p) cat My3A(p) cat My3B(p) cat My5(p) cat 
 My7(p) cat My8(p) cat My9(p) cat My10(p);
end function;


Check2 := function(L, p)

Z := Integers ();

count := 0;
H1 := [];
MinDeg1 := [];

// (311)b

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4];
Append (~H1, sub< F | Alpha[2]>);
Append (~MinDeg1, p^4);

return H1, MinDeg1;
end function;

Check3 := function(L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 1;
H2 := [];
MinDeg2 := [];

// (311)a

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4];
Append (~H2, sub< F | Alpha[2], Alpha[3]>);
Append (~MinDeg2, p^3);

// (311)b_r

for r in [1, nu] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4];
Append (~H2, sub< F | Alpha[3]>);
Append (~MinDeg2, p^4);
end for;

// (2111)c

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5];
Append (~H2, sub< F | Alpha[2], Alpha[3]>);
Append (~MinDeg2, p^3);

return H2, MinDeg2;
end function;

Check5 := function(L, p)

count := 5;
H3 := [];
MinDeg3 := [];

// (2111)

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5];
Append (~H3, sub< F | Alpha[2], Alpha[3]>);
Append (~MinDeg3, p^3);

// (1^5)

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5];
Append (~H3, sub< F | Alpha[2], Alpha[3]>);
Append (~MinDeg3, p^3);

return H3, MinDeg3;
end function;

Check7 := function(L, p)

K := GF(p);
w := PrimitiveRoot(p);

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 7;
H4 := [];
MinDeg4 := [];

// (2111)a

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5];
Append (~H4, sub< F | Alpha[2], Alpha[3]>);
Append (~MinDeg4, p^3);

// (2111)b_r

for r in [1, nu] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5];
Append (~H4, sub< F | Alpha[1], Alpha[5]>);
Append (~MinDeg4, p^3);
end for;

// (2111)c

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5];
Append (~H4, sub< F | Alpha[2], Alpha[3]>);
Append (~MinDeg4, p^3);

// (1^5)

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5];
Append (~H4, sub< F | Alpha[2], Alpha[3]>);
Append (~MinDeg4, p^3);

return H4, MinDeg4;
end function;

Check8 := function(L, p)

K := GF(p);
w := PrimitiveRoot(p);

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 12;
H5 := [];
MinDeg5 := [];

// (2111)a

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3];
Append (~H5, sub< F | Alpha[2]>);
Append (~MinDeg5, p^3);

return H5, MinDeg5;
end function;

Check9 := function(L, p)

K := GF(p);
w := PrimitiveRoot(p);

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 13;
H6 := [];
MinDeg6 := [];

// (2111)a

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5];
Append (~H6, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg6, p^2);

// (2111)b_r

el3 := GCD(p-1, 3) - 1;
for r in [0..el3] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5];
Append (~H6, sub< F | Alpha[3], Alpha[4]>);
Append (~MinDeg6, p^3);
end for;

// (1^5)

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5];
Append (~H6, sub< F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg6, p^2);

return H6, MinDeg6;
end function;

Check10 := function(L, p)

K := GF(p);
w := PrimitiveRoot(p);

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

el3 := GCD(p-1, 3);
count := 15 + el3;
H7 := [];
MinDeg7 := [];

// (2111)a_r

el4 := GCD(p-1, 4) - 1;
for r in [0..el4] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5];
Append (~H7, sub< F | Alpha[3], Alpha[4]>);
Append (~MinDeg7, p^3);
end for;

// (2111)b_r

el3 := GCD(p-1, 3) - 1;
for r in [0..el3] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5];
Append (~H7, sub< F | Alpha[3], Alpha[4]>);
Append (~MinDeg7, p^3);
end for;

// (1^5)

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5];
Append (~H7, sub< F | Alpha[3], Alpha[4]>);
Append (~MinDeg7, p^3);

return H7, MinDeg7;
end function;

for p in PrimesInInterval (5, 13) do 
   "\n process prime ", p;
   L := Table2Rank1(p);
   H1, MinDeg1 := Check2(L, p);
   H2, MinDeg2 := Check3(L, p);
   H3, MinDeg3 := Check5(L, p);
   H4, MinDeg4 := Check7(L, p);
   H5, MinDeg5 := Check8(L, p);
   H6, MinDeg6 := Check9(L, p);
   H7, MinDeg7 := Check10(L, p);
   H := H1 cat H2 cat H3 cat H4 cat H5 cat H6 cat H7;
   MinDeg := MinDeg1 cat MinDeg2 cat MinDeg3
         cat MinDeg4 cat MinDeg5 cat MinDeg6 cat MinDeg7;

   for i in [1..#L] do
      G := L[i];
      Q, phi := pQuotient(G, p, 6);
      A := phi (H[i]);
      m := Index(Q, A);
      assert m eq MinDeg[i];
      C := Core(Q, A);
      assert #C eq 1;
      phiA := CosetAction (Q, A);
      J := Image (phiA);
      // assert IsIsomorphic (J, PF);
      assert #J eq #Q;
      assert Degree (J) eq m;
   end for;
end for;
