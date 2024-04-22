My4 := function(p)

K := GF(p);

w := PrimitiveRoot(p);

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

Z := Integers ();
    nu := Z ! (NonQuadraticResidue (p)); // nu

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

// (221)e

G := quo <F | Comms, a^p = 1, a1^(4*p) = b2^(-1),
 a2^p = b1*b2>;
Append (~L, G);

return L;
end function;


My6 := function(p)

K := GF(p);

w := PrimitiveRoot(p);

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

Z := Integers ();
    nu := Z ! (NonQuadraticResidue (p)); // nu

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

// (221)c_r

for r in [1, nu] do
  G := quo <F | Comms, a1^(4*p) = b2^(-r), a2^p = b1^r*b2^r>;
  Append (~L, G);
end for;

return L;
end function;

My4and6James := function(p)
   return My4(p) cat My6(p);
end function;

My4N := function(p)

w := PrimitiveRoot(p);

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

Z := Integers ();
    nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, b1, b2, b3> := FreeGroup (8);
Alpha := [a1, a2, a3, a4, a5];
Beta := [b1, b2, b3];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= 1, (a3, a4) = 1,
(a4, a5) = a2, (a3, a5) = a1, (a2, a5) = 1, a1 = b1,
a2 = b2] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..5]]: i in [1..3]])
cat &cat([[(Beta[i], Beta[j]) = Id(F) : j in [i + 1..3]]: i in [1..3]]);

M := [];

// G4, 24

G := quo <F | Comms, a5^p =  b1^p = b2^p = b3^p = 1, 
a3^p = b1, a4^p = b1*b2>;
G1:= sub<G | F.1, F.2, F.3, F.4, F.5, F.6, F.7>;

Append (~M, G1);

return M;
end function;

My6N := function(p)

w := PrimitiveRoot(p);

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

Z := Integers ();
    nu := Z ! (NonQuadraticResidue (p)); // nu

F<a1, a2, a3, a4, a5, b1, b2, b3> := FreeGroup (8);
Alpha := [a1, a2, a3, a4, a5];
Beta := [b1, b2, b3];

// common relations, typically commutators
Comms := [
(a2, a3) = 1, (a2, a4)= 1, (a3, a4) = a1,
(a4, a5) = a3, (a3, a5) = a2, (a2, a5) = 1, a1 = b1,
a2 = b2] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..5]]: i in [1..3]])
cat &cat([[(Beta[i], Beta[j]) = Id(F) : j in [i + 1..3]]: i in [1..3]]);

M := [];

// G6, 17r

for r in [1,nu] do
G := quo <F | Comms, a3^p =  b1^p = b2^p = b3^p = 1,
a4^p = b1, a5^p = (b1^r)*b2>;
G1:= sub<G | F.1, F.2, F.3, F.4, F.5, F.6, F.7>;
Append (~M, G1);
end for;

return M;
end function;

My4and6N := function(p)
   return My4N(p) cat My6N(p);
end function;


for p in PrimesInInterval (5, 40) do 
   "\nprocess p = ", p;
   L := My4and6James(p);
   M := My4and6N(p);

for i in [1..#L] do
F := L[i];
G := pQuotient(F, p, 6);
I := M[i];
H := pQuotient(I, p, 6);
i, IsIsomorphic(G, H);
end for;

end for;