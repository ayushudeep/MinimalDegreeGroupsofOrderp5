load "../setup-permrep.m";

NonQuadraticResidue := function (p)
  for x in GF (p) do
    if not IsPower (x, 2) then return x; end if;
  end for;
end function;

My4Girnat := function(p)

K := GF(p);
w := PrimitiveRoot(p);
Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a, b, c, d, e> := FreeGroup (5);
Alpha := [a, b, c];
Beta := [d, e];

// common relations, typically commutators
Comms := [
(b, a) = d*e, (c, a)= e, (b, c) = 1, (d, e) = 1,
d^p = 1, e^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..3]]: i in [1..2]]);

L := [];

// (221)e

G := quo <F | Comms, a^p = 1, b^p = d, c^p = e >;
Append (~L, G);

return L;
end function;

My6Girnat := function(p)

K := GF(p);
w := PrimitiveRoot(p);
Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

F<a, b, c, d, e> := FreeGroup (5);
Alpha := [a, b, c];
Beta := [d, e];

// common relations, typically commutators
Comms := [
(b, a) = c,  (c, b) = e, (d, e) = 1,
d^p = 1, e^p = 1] cat
&cat([[(Beta[i], Alpha[j]) = Id(F) : j in [1..3]]: i in [1..2]]);

L := [];

// (221)c_r

for r in [1, nu] do
G := quo <F | Comms, (c, a)= d*e^r, a^p = d, b^p = e, c^p = 1 >;
Append (~L, G);
end for;

return L;
end function;

Table3BGirnat := function(p)
   return My4Girnat(p) cat My6Girnat(p);
end function;

Check4Girnat := function(L, p)

count := 0;

PFlist3 := []; // lists the group G
PRlist3 := []; // lists the subgroup R
PNlist3 := []; // lists kernel of non-linear irr char from R
PSlist3 := []; // lists the subgroup S
PMlist3 := []; // lists kernel of non-linear irr char from S
Mu3 := [];     // Mu(G) from Table 3

// (221)b

count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta:= [F.4, F.5];
GPF, phi := pQuotient(F, p, 6);
Append(~PFlist3, GPF);
GPR := sub<GPF | phi(F.1), phi(F.2), phi(F.5)>;
GPN := sub<GPR | phi(F.1), phi(F.4*F.5)>;
GPS := sub<GPF | phi(F.1), phi(F.3), phi(F.4)>;
GPM := sub<GPS | phi(F.1), phi(F.3)>;
Append(~PRlist3, GPR);
Append(~PNlist3, GPN);
Append(~PSlist3, GPS);
Append(~PMlist3, GPM);
Append(~Mu3, p^3 + p^2);

return PFlist3, PRlist3, PNlist3, PSlist3, PMlist3, Mu3;
end function;

Check6Girnat := function(L, p)

K := GF(p);
w := PrimitiveRoot(p);
Z := Integers ();
nu := Z ! (NonQuadraticResidue (p)); // nu

count := 1;

PFlist4 := []; // lists the group G
PRlist4 := []; // lists the subgroup R
PNlist4 := []; // lists kernel of non-linear irr char from R
PSlist4 := []; // lists the subgroup S
PMlist4 := []; // lists kernel of non-linear irr char from S
Mu4 := [];     // Mu(G) from Table 3

// (221)c_r

for r in [1, nu] do
count := count+1;
F := L[count];
Alpha := [F.1, F.2, F.3]; Beta:= [F.4, F.5];
GPF, phi := pQuotient(F, p, 6);
Append(~PFlist4, GPF);
GPR := sub<GPF | phi(F.1), phi(F.3), phi(F.4), phi(F.5)>;
GPN := sub<GPR | phi(F.3), phi(F.4*F.5^r)>;
GPS := sub<GPF | phi(F.2), phi(F.3), phi(F.4)>;
GPM := sub<GPS | phi(F.2), phi(F.3)>;
Append(~PRlist4, GPR);
Append(~PNlist4, GPN);
Append(~PSlist4, GPS);
Append(~PMlist4, GPM);
Append(~Mu4, p^3 + p^2);
end for;

return PFlist4, PRlist4, PNlist4, PSlist4, PMlist4, Mu4;
end function;

MAX := 13^5;

for p in PrimesInInterval (5, 13) do 
   "\nprocess p = ", p;
   L := Table3BGirnat(p);

   PFlist3, PRlist3, PNlist3, PSlist3, PMlist3, Mu3 := Check4Girnat(L, p);
   PFlist4, PRlist4, PNlist4, PSlist4, PMlist4, Mu4 := Check6Girnat(L, p);
   PFlist := PFlist3 cat PFlist4;
   PRlist := PRlist3 cat PRlist4;
   PNlist := PNlist3 cat PNlist4;
   PSlist := PSlist3 cat PSlist4;
   PMlist := PMlist3 cat PMlist4;
   MinDeg := Mu3 cat Mu4;

   for i in [1..#L] do
      PF := PFlist[i];
      PR := PRlist[i];
      PN := PNlist[i];
      PS := PSlist[i];
      PM := PMlist[i];
      Mu_value := MinDeg[i];
      Int := Core(PF, PN) meet Core(PF, PM);
      // i, #Int;
      assert #Int eq 1;

      phiN := CosetAction (PF, PN);
      phiM := CosetAction (PF, PM);
      pi := PermutationRepresentationSumH (PF, [phiN, phiM]);
      J := Image (pi);
      assert #J eq #PF;
      //if #J le MAX then assert IsIsomorphic (J, PF); end if;
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

      QPSM, h := quo<PS | PM>;
      linQPM := LinearCharacters (QPSM);
      for j in [1..#linQPM] do
         if IsFaithful(linQPM[j]) eq true then
            lambda := linQPM[j];
            break;
         end if;
      end for;
      lambda_bar := LiftCharacter(lambda, h, PS);
      eta := Induction(lambda_bar, PF);
      assert IsIrreducible(eta);

   end for;
end for;
