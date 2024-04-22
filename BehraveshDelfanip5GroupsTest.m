NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

// List of groups of order p^5 in Behravesh and Delfani

BDlistA := function(p)

F<x, y, z> := FreeGroup (3);
Alpha := [x, z];
Beta := [y];

// common relations, typically commutators
Comms := [
 z^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j
 in [1..2]]: i in [1]]);

L := [];


// G1 Thm 3.5

G := quo <F | Comms, (x, z) = x^p, x^(p^2) = 1, y^(p^2) = 1>;
Append (~L, G);


// G2 Thm 3.5

G := quo <F | Comms, (x, z) = x^(p^2), x^(p^3) = 1, y^(p) = 1>;
Append (~L, G);

// G3 Thm 3.5

G := quo <F | Comms, (x, z) = y, x^(p^3) = 1, y^(p) = 1>;
Append (~L, G);

// G4 Thm 3.5

G := quo <F | Comms, (x, z) = y^p, x^(p^2) = 1, y^(p^2) = 1>;
Append (~L, G);

return L;
end function;


BDlistB := function(p)

F<x, y, z, k> := FreeGroup (4);
Alpha := [x, k];
Beta := [y, z];

// common relations, typically commutators
Comms := [
(y, z) = 1, y^p = 1, z^p = 1, k^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j
 in [1..2]]: i in [1..2]]);

L := [];


// G1 Thm 3.6

G := quo <F | Comms, (x, k) = x^p, x^(p^2) = 1>;
Append (~L, G);

// G2 Thm 3.6

G := quo <F | Comms, (x, k) = y, x^(p^2) = 1>;
Append (~L, G);

return L;
end function;

BDlistC := function(p)

F<x, y, z, k> := FreeGroup (4);
Alpha := [z, k];
Beta := [y, x];

// common relations, typically commutators
Comms := [
(y, x) = 1, y^p = 1, z^p = 1, k^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j
 in [1..2]]: i in [1..2]]);

L := [];


// G3 Thm 3.6

G := quo <F | Comms, (z, k) = x^p, x^(p^2) = 1>;
Append (~L, G);

// G4 Thm 3.6

G := quo <F | Comms, (z, k) = y, x^(p^2) = 1>;
Append (~L, G);

return L;
end function;

BDlistD := function(p)

K := GF(p);
w := PrimitiveRoot(p);

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<x, y, z> := FreeGroup (3);
Alpha := [z];
Beta := [y, x];

// common relations, typically commutators
Comms := [
(y, x) = 1, (x, z) = y, y^p = 1, z^p = 1];

L := [];

// G1 Thm 4.1

for r in [0,1] do
G := quo <F | Comms, (y, z) = x^(p^2 * nu^r), x^(p^3) = 1>;
Append (~L, G);
end for;

return L;
end function;

BDlistE := function(p)

F<x, y, z, k> := FreeGroup (4);
Alpha := [y, z, k];
Beta := [x];

// common relations, typically commutators
Comms := [
(y, k) = 1, y^p = 1, z^p = 1, k^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j
 in [1..3]]: i in [1]]);

L := [];

// G2 Thm 4.1

G := quo <F | Comms, (z, k) = y, (y, z) = x^p, x^(p^2) = 1>;
Append (~L, G);

return L;
end function;


BDlistF := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<x, y, z, k, t> := FreeGroup (5);
Alpha := [z, k, t];
Beta := [x, y];

// common relations, typically commutators
Comms := [
x^p = 1, y^p = 1, z^p = 1, k^p = 1, t^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j
 in [1..3]]: i in [1..2]]);

L := [];

// G1 Thm 4.2

G := quo <F | Comms, (z, t) = y, (k, t) = z, (z, k) = x>;
Append (~L, G);

// G2 Thm 4.2 is defined only for p = 3

// G3 Thm 4.2

G := quo <F | Comms, (z, t) = x, (k, t) = z, (z, k) = 1>;
Append (~L, G);

// G4 Thm 4.2

G := quo <F | Comms, (z, t) = x, (k, t) = y, (z, k) = 1>;
Append (~L, G);

return L;
end function;

BDlistG := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<x, y, z, k> := FreeGroup (4);
Alpha := [x, z, k];
Beta := [y];

// common relations, typically commutators
Comms := [
x^(p^2) = 1, y^p = 1, z^p = 1, k^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j
 in [1..3]]: i in [1]]);

L := [];

// G5 Thm 4.2

G := quo <F | Comms, (x, z) = 1, (x, k) = y, (z, k) = x^p>;
Append (~L, G);

// G6 Thm 4.2

G := quo <F | Comms, (x, z) = 1, (x, k) = x^p, (z, k) = y>;
Append (~L, G);

// G7 Thm 4.2

for r in [0,1] do
G := quo <F | Comms, (x, z) = 1, (x, k) = z, (z, k) = x^(p * nu^r)>;
Append (~L, G);
end for;

// G8 in Thm 4.2 is valid for p=3 only

// G9 Thm 4.2

G := quo <F | Comms, (x, z) = 1, (x, k) = z, (z, k) = y>;
Append (~L, G);

return L;
end function;

BDlistH := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

nonpair := function(p)
for a in GF (p) do
   for b in GF (p) do
      if not IsPower (a, 2) and not IsPower (b, 2) then return Z!a, Z!b; end if;
   end for;
end for;
end function;

F<x, y, z> := FreeGroup (3);
Alpha := [y, z];
Beta := [x];

// common relations, typically commutators
Comms := [
(x, y) = 1, x^(p^2) = 1, y^(p^2) = 1, z^p = 1];

L := [];

// G10 Thm 4.2

for r in [0,1] do
a, b := nonpair(p);
G := quo <F | Comms, (x, z) = y^p, (y, z) = x^(p * a^r)*y^(p *b)  >;
Append (~L, G);
end for;

// G11 Thm 4.2

G := quo <F | Comms, (x, z) = x^p, (y, z) = y^p  >;
Append (~L, G);

return L;
end function;

BDlistI := function(p)

Z := Integers ();

nu := Z ! (NonQuadraticResidue (p)); // nu

F<x, y, z, k, t> := FreeGroup (5);
Alpha := [y, z, k, t];
Beta := [x];

// common relations, typically commutators
Comms := [
(y, z) = 1, (y, k) = 1,  x^p = 1, y^p = 1, z^p = 1, k^p = 1, t^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j
 in [1..4]]: i in [1]]);

L := [];

// G1 Them 5.1

if p mod 3 eq 1 then add := [0..2];
else add := [0]; end if;
for r in add do
G := quo <F | Comms, (y, t) = x, (z, t) = y, (k, t) = z^(nu^r), (z, k) = x  >;
Append (~L, G);
end for;

// G2 Thm 5.1

G := quo <F | Comms, (y, t) = x, (z, t) = 1, (k, t) = y, (z, k) = x  >;
Append (~L, G);

// G3 Thm 5.1

G := quo <F | Comms, (y, t) = x, (z, t) = 1, (k, t) = z, (z, k) = x  >;
Append (~L, G);

// G4 Thm 5.1 is defined only for p = 3

return L;
end function;

BDlistJ := function(p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<x, y, z, k> := FreeGroup (4);
Alpha := [y, z, k];
Beta := [x];

// common relations, typically commutators
Comms := [
(y, z) = 1, (x, y) = 1, (x, z) = 1,  x^(p^2) = 1, y^p = 1, z^p = 1, k^p = 1] ;

L := [];

// G5 Them 5.1

if p mod 3 eq 1 then add := [1..2];
else add := [0]; end if;
for r in add do
G := quo <F | Comms, (x, k) = z, (z, k) = y, (y, k) = x^(p * nu^r) >;
Append (~L, G);
end for;

return L;
end function;

BDp5 := function(p)
return BDlistA(p) cat BDlistB(p) cat BDlistC(p) cat BDlistD(p) cat 
BDlistE(p) cat BDlistF(p) cat BDlistG(p) cat BDlistH(p) cat BDlistI(p) cat BDlistJ(p);
end function;

error "HERE";
// a:=7; b:= 97; a:=5;b:=97;p := 7; N:=[];

a := 5; b := 13;
for p in PrimesInInterval (a, b) do
   J := [];
   "\n p = ", p;
   L := BDp5(p);
   for i in [1..#L] do
      G := L[i];
      P := pQuotient (G, p, 6);
      assert #P eq p^5;
      Append (~J, P);
   end for;
   #J, NumberOfSmallGroups(p^5);

   SG := SmallGroups(p^5);

   for j in [1..#J] do
      T:= J[j];
      for i in [1..#SG] do
         H := SmallGroup(p^5, i);
         f := IsIsomorphic (T, H);
         if f then "found ", j, i; break i; end if;
      end for;
   end for;
end for;
