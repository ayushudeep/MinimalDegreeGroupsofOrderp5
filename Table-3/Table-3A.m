load "../setup-permrep.m";

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

// (221)c

G := quo <F | Comms, a^(p^2) = 1, a1^p = 1, ga^(p) = a2>;
Append (~L, G);

return L;
end function;

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

My3A := function(p)
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

// (221)b_r

for r in [1, nu] do
  G := quo <F | Comms, a^(p^2) = 1, a1^p = a3^r>;
  Append (~L, G);
end for;

return L;
end function;

Table3A := function(p)
   return My2B(p) cat My3A(p);
end function;

Check2 := function(L, p)

count := 0;

PFlist1 := []; // lists the group G
PRlist1 := []; // lists the subgroup R
PNlist1 := []; // lists kernel of non-linear irr char.
PKlist1 := []; // lists kernel of linear char.
Mu1 := [];     // Mu(G) from Table 3

// (221)c

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta:= [F.4];
GPF, phi := pQuotient(F, p, 6);
Append(~PFlist1, GPF);
GPR := sub<GPF | phi(F.1^p), phi(F.2), phi(F.4)>;
GPN := sub<GPR | phi(F.1^p), phi(F.2)>;
GPK := sub<GPF | phi(F.2), phi(F.4)>;
Append(~PRlist1, GPR);
Append(~PNlist1, GPN);
Append(~PKlist1, GPK);
Append(~Mu1, p^3 + p^2);

return PFlist1, PRlist1, PNlist1, PKlist1, Mu1;
end function;

Check3 := function(L, p)

Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 1;

PFlist2 := []; // lists the group G
PRlist2 := []; // lists the subgroup R
PNlist2 := []; // lists kernel of non-linear irr char.
PKlist2 := []; // lists kernel of linear char.
Mu2 := [];     // Mu(G) from Table 3

// (221)b_r

for r in [1, nu] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta:= [F.4];
GPF, phi := pQuotient(F, p, 6);
Append(~PFlist2, GPF);
GPR := sub<GPF | phi(F.1^p), phi(F.2), phi(F.3)>;
GPN := sub<GPR | phi(F.1^p), phi(F.3)>;
GPK := sub<GPF | phi(F.2), phi(F.3)>;
Append(~PRlist2, GPR);
Append(~PNlist2, GPN);
Append(~PKlist2, GPK);
Append(~Mu2, p^3 + p^2);
end for;

return PFlist2, PRlist2, PNlist2, PKlist2, Mu2;
end function;

MAX := 13^5;

for p in PrimesInInterval (5, 13) do 
   "\nprocess p = ", p;
   L := Table3A(p);

   PFlist1, PRlist1, PNlist1, PKlist1, Mu1 := Check2(L, p);
   PFlist2, PRlist2, PNlist2, PKlist2, Mu2 := Check3(L, p);
   PFlist := PFlist1 cat PFlist2;
   PRlist := PRlist1 cat PRlist2;
   PNlist := PNlist1 cat PNlist2;
   PKlist := PKlist1 cat PKlist2;
   MinDeg := Mu1 cat Mu2;

   for i in [1..#L] do
      PF := PFlist[i];
      PR := PRlist[i];
      PN := PNlist[i];
      PK := PKlist[i];
      Mu_value := MinDeg[i];
      Int := Core(PF, PN) meet Core(PF, PK);
      assert #Int eq 1;

      phiN := CosetAction (PF, PN);
      phiK := CosetAction (PF, PK);
      pi := PermutationRepresentationSumH (PF, [phiN, phiK]);
      J := Image (pi);
      assert #J eq #PF;
      if #J le MAX then assert IsIsomorphic (J, PF); end if;
      assert Degree (J) eq Mu_value;

      // Irreducibility checks for X_G 
      QPRN, f := quo<PR | PN>;
      linQP := LinearCharacters(QPRN);
      for j in [1..#linQP] do
         if IsFaithful(linQP[j]) eq true then
            chi := linQP[j];
            break;
         end if;
      end for;
      chi_bar := LiftCharacter(chi, f, PR);
      psi := Induction(chi_bar, PF);
      assert IsIrreducible(psi);

      QPFK, h := quo<PF | PK>;
      linQPK := LinearCharacters (QPFK);
      for j in [1..#linQPK] do
         if IsFaithful(linQPK[j]) eq true then
            lambda := linQPK[j];
            break;
         end if;
      end for;
      eta := LiftCharacter(lambda, h, PF);
      assert IsIrreducible(eta);

   end for;
end for;
