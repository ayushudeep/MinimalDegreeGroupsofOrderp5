load "../setup-permrep.m";

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

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

// (32)a_1

G := quo <F | Comms, a^(p^2) = a2, a1^(p^2) = 1>;
Append (~L, G);

// (32)a_2

G := quo <F | Comms, a^(p^3) = 1, a1^p = a2>;
Append (~L, G);

// (311)c

G := quo <F | Comms, a^(p^3) = 1, a1^p = 1>;
Append (~L, G);

return L;
end function;

My2 := function(p)
return My2A(p);
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

// (221)a

G := quo <F | Comms, a^p = a3, a1^(p^2) = 1>;
Append (~L, G);

// (2111)d

G := quo <F | Comms, a^(p^2) = 1, a1^p = 1>;
Append (~L, G);

// (2111)e

G := quo <F | Comms, a^p = 1, a1^(p^2) = 1>;
Append (~L, G);

return L;
end function;

My3 := function(p)
return My3A(p);
end function;

My4 := function(p)

K := GF(p);
w := PrimitiveRoot(p);

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

PairPhi4 := function(r, p)
  for x in GF(p) do

      if 4*x eq (w^(2*r + 1) - 1) mod p and x ne 0 then
        return Z!x;
      end if;
    
  end for;
end function;

F<a, a1, a2, b1, b2> := FreeGroup (5);
Alpha := [a, a1, a2];
Beta := [b1, b2];

// common relations, typically commutators
Comms := [
(a1, a) = b1, (a2, a)= b2, (a1, a2) = 1, (b1, b2) = 1,
b1^p = 1, b2^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j
 in [1..3]]: i in [1..2]]);

L := [];


// (221)a

G := quo <F | Comms, a^p = b2, a1^p = b1,
 a2^p = 1>;
Append (~L, G);

// (221)c

G := quo <F | Comms, a^p = 1, a1^p = b1,
 a2^p = b2>;
Append (~L, G);

// (221)d_r

for r in [1..(p-1) div 2] do
  G := quo <F | Comms, a^p = 1, a1^p = b1^(w^r mod p),
  a2^p = b2>;
  Append (~L, G);
end for;

// (2111)a

G := quo <F | Comms, a^p = b2, a1^p = 1,
 a2^p = 1>;
Append (~L, G);

// (2111)b

G := quo <F | Comms, a^p = 1, a1^p = b1,
 a2^p = 1>;
Append (~L, G);

// (1^5)

G := quo <F | Comms, a^p = 1, a1^p = 1,
 a2^p = 1>;
Append (~L, G);

return L;
end function;

My6 := function(p)

K := GF(p);
w := PrimitiveRoot(p);

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

PairPhi6 := function(r, p)
  for x in GF(p) do

      if 4*x eq (w^(2*r + 1) - 1) mod p and x ne 0 then
        return Z!x;
      end if;
    
  end for;
end function;

F<a1, a2, b, b1, b2> := FreeGroup (5);
Alpha := [a1, a2, b];
Beta := [b1, b2];

// common relations, typically commutators
Comms := [
(a1, a2) = b, (b, a1)= b1, (b, a2) = b2, (b1, b2) = 1,
b^p = 1, b1^p = 1, b2^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j
 in [1..3]]: i in [1..2]]);

L := [];

// (221)a

G := quo <F | Comms, a1^p = b1, a2^p = b2>;
Append (~L, G);

// (221)b_r

for r in [1..(p-1) div 2] do
  G := quo <F | Comms, a1^p = b1^(w^r mod p), a2^p = b2>;
  Append (~L, G);
end for;

// (2111)a

G := quo <F | Comms, a1^p = b1, a2^p = 1>;
Append (~L, G);

// (1^5)

G := quo <F | Comms, a1^p = 1, a2^p = 1>;
Append (~L, G);

return L;
end function;


Table2rank2 := function(p)
return My2(p) cat My3(p) cat My4(p) cat My6(p);
end function;


Check2 := function (L, p)

count := 0;
H11 := [];
H12 := [];
MinDeg1 := [];

// (32)a_1

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; 
Append (~H11, sub<F | Alpha[1]>);
Append (~H12, sub<F | Alpha[2]>);
Append (~MinDeg1, p^3 + p^2);

// (32)a_2

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; 
Append (~H11, sub<F | Alpha[1]>);
Append (~H12, sub<F | Alpha[2]>);
Append (~MinDeg1, p^3 + p^2);

// (311)c

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; 
Append (~H11, sub<F | Alpha[1]>);
Append (~H12, sub<F | Alpha[2], Alpha[3]>);
Append (~MinDeg1, p^3 + p^2);

return H11, H12, MinDeg1;
end function;

Check3 := function (L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 3;
H21 := [];
H22 := [];
MinDeg2 := [];

// (221)a

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4]; 
Append (~H21, sub<F | Alpha[1], Alpha[3]>);
Append (~H22, sub<F | Alpha[2], Alpha[3]>);
Append (~MinDeg2, 2*p^2);

// (2111)d

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4]; 
Append (~H21, sub<F | Alpha[1]^(p), Alpha[2], Alpha[3]>);
Append (~H22, sub<F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg2, 2*p^2);

// (2111)e

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4]; 
Append (~H21, sub<F | Alpha[1], Alpha[3], Alpha[4]>);
Append (~H22, sub<F | Alpha[2], Alpha[3]>);
Append (~MinDeg2, 2*p^2);

return H21, H22, MinDeg2;
end function;

Check4 := function (L, p)

K := GF(p);
w := PrimitiveRoot(p);

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 6;
H31 := [];
H32 := [];
MinDeg3 := [];

// (221)a

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; 
Append (~H31, sub<F | Alpha[1], Alpha[3]>);
Append (~H32, sub<F | Alpha[2], Alpha[3]>);
Append (~MinDeg3, 2*p^2);

// (221)c

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; 
Append (~H31, sub<F | Alpha[1], Alpha[2]>);
Append (~H32, sub<F | Alpha[1], Alpha[3]>);
Append (~MinDeg3, 2*p^2);

// (221)d_r

for r in [1..(p-1) div 2] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; 
Append (~H31, sub<F | Alpha[1], Alpha[2]>);
Append (~H32, sub<F | Alpha[1], Alpha[3]>);
Append (~MinDeg3, 2*p^2);
end for;

// (2111)a

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; 
Append (~H31, sub<F | Alpha[1], Alpha[3]>);
Append (~H32, sub<F | Alpha[2], Alpha[3], Alpha[4]>);
Append (~MinDeg3, 2*p^2);

// (2111)b

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; 
Append (~H31, sub<F | Alpha[1], Alpha[2]>);
Append (~H32, sub<F | Alpha[1], Alpha[3], Alpha[5]>);
Append (~MinDeg3, 2*p^2);

// (1^5)

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; 
Append (~H31, sub<F | Alpha[1], Alpha[2], Alpha[4]>);
Append (~H32, sub<F | Alpha[1], Alpha[3], Alpha[5]>);
Append (~MinDeg3, 2*p^2);

return H31, H32, MinDeg3;
end function;

Check6 := function (L, p)

K := GF(p);
w := PrimitiveRoot(p);

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 11 + (p-1) div 2;
H41 := [];
H42 := [];
MinDeg4 := [];

// (221)a

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; 
Append (~H41, sub<F | Alpha[1], Alpha[3], Alpha[4]>);
Append (~H42, sub<F | Alpha[2], Alpha[3], Alpha[5]>);
Append (~MinDeg4, 2*p^2);

// (221)b_r

for r in [1..(p-1) div 2] do
   count := count+1;
   F := L[count];
   Alpha := [F.1, F.2, F.3, F.4, F.5]; 
   Append (~H41, sub<F | Alpha[1], Alpha[3], Alpha[4]>);
   Append (~H42, sub<F | Alpha[2], Alpha[3], Alpha[5]>);
   Append (~MinDeg4, 2*p^2);
end for;

// (2111)a

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; 
Append (~H41, sub<F | Alpha[1], Alpha[3]>);
Append (~H42, sub<F | Alpha[2], Alpha[3], Alpha[5]>);
Append (~MinDeg4, 2*p^2);

// (1^5)

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3, F.4, F.5]; 
Append (~H41, sub<F | Alpha[1], Alpha[3], Alpha[4]>);
Append (~H42, sub<F | Alpha[2], Alpha[3], Alpha[5]>);
Append (~MinDeg4, 2*p^2);

return H41, H42, MinDeg4;
end function;

MAX := 13^5;

for p in PrimesInInterval (5, 13) do 
   "\n process prime ", p;
   L := Table2rank2(p);
   H11, H12, MinDeg1 := Check2(L, p);
   H21, H22, MinDeg2 := Check3(L, p);
   H31, H32, MinDeg3 := Check4(L, p);
   H41, H42, MinDeg4 := Check6(L, p);
   H1 := H11 cat H21 cat H31 cat H41;
   H2 := H12 cat H22 cat H32 cat H42;
   MinDeg := MinDeg1 cat MinDeg2 cat MinDeg3 cat MinDeg4;

   for i in [1..#L] do
     G := L[i];
     Q, phi := pQuotient(G, p, 10);
     A := phi (H1[i]);
     B := phi (H2[i]);
     m1 := Index(Q, A);
     m2 := Index(Q, B);
     m := m1 + m2;
     C1 := Core(Q, A);
     C2 := Core(Q, B);
     C := C1 meet C2;
     assert #C eq 1;
     phiA := CosetAction (Q, A);
     phiB := CosetAction (Q, B);
     pi := PermutationRepresentationSumH (Q, [phiA, phiB]);
     J := Image (pi);
     assert #J eq #Q;
     if #J le MAX then assert IsIsomorphic (J, Q); end if;
     assert Degree (J) eq m;
     assert Degree (J) eq MinDeg[i];
   end for;
end for;

