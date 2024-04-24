// Magma library code to set up intransitive permutation representation

PermutationRepresentationSumH := function(G, reps)
/* reps should be a list of homomorphisms from group G to permutation
 * groups (subgroups of Sym(n_i)). The summed permutation representation
 * reps[1]+..resp[r] of degree n_1+n_2+..n_r is returned, together
 * with the image group.
 */
  local ng, nreps, degrees, phi, cdphi, g, ims, img, sumdeg, deg, cd, cdgens;
  nreps := #reps;
  degrees := [];
  sumdeg := 0;
  for j in [1..nreps] do
    phi:=reps[j];
    if Domain(phi) cmpne G then
      error
    "Domain of maps in reps must be G in PermutationRepresentationSum(G,reps)";
    end if;
    cdphi :=  Codomain(phi);
    if Category(cdphi) ne GrpPerm then
      error
  "Codomain of maps must be perm-gps in PermutationRepresentationSum(G,reps)";
    end if;
    degrees[j]:=Degree(cdphi);
    sumdeg +:= degrees[j];
  end for;
  deg:=sumdeg;

  ng := Type(G) eq GrpPC select NPCGenerators(G) else Ngens(G);

  // The codomain of the summed representation will be the direct product of the
  // codomains of the given maps.
  cdgens := [Sym(deg)|];
  sumdeg := 0;
  for j in [1..nreps] do
    for g in Generators(Codomain(reps[j])) do
      Append(~cdgens,[i:i in [1..sumdeg]] cat
            [i^g + sumdeg : i in [1..degrees[j]]] cat
            [i : i in [sumdeg+degrees[j]+1..deg]]);
    end for;
    sumdeg +:= degrees[j];
  end for;

  cd := sub<Sym(deg)|cdgens>;
  ims := [cd|];
  for i in [1..ng] do
    g := G.i;
    img:=[];
    sumdeg:=0;
    for j in [1..nreps]  do
      for k in [1..degrees[j]] do
        img[sumdeg+k] := sumdeg + k^reps[j](g);
      end for;
      sumdeg +:= degrees[j];
    end for;
    Append(~ims,img);
  end for;

  return hom<G -> cd | ims >, sub<cd|ims>;

end function;

// minimal degree permutation representation for abelian group 
MinimalDegreeRepresentationAbelianGroup := function (G)
    assert IsAbelian (G);
    bas := PrimaryAbelianBasis(G);
    subs := [ sub < G | [ x : x in bas | x ne b ]>  : b in bas];
    reps := [CosetAction(G, s): s in subs];
    phi, im :=  PermutationRepresentationSumH( G, reps);
    // ker := sub <G|>; assert ker eq Kernel(phi);
    return phi, im;
end function;

// G = H \times K 
// LH and LK determine min degree repn for H and K respectively
// write down repn for G 
MinRepDirectProduct := function (G, H, LH, K, LK)
   L := [sub<G | h, K>: h in LH] cat [sub<G | H, k>: k in LK]; 
   Phi := [CosetAction (G, l): l in L];
   pi := PermutationRepresentationSumH (G, Phi);
   J := Image (pi);
   return J, L;
end function;

// phi is map from G to Q, isomorphic copy;  
// H is non-abelian direct factor of Q, its perm rep determined by LH;
// determine abelian K such that Q = H \times K and its perm rep; 
// return perm rep for Q and corresponding list of subgroups of Q 

DetermineMinRep := function (G, Q, H, LH, phi)
   index := [i : i in [1..Ngens (G)] | not (phi (G.i) in H)];
   K := sub < G | [G.i: i in index]>;
   K := phi (K);
   assert IsNormal (Q, K);
   assert IsNormal (Q, H);
   assert #H * #K eq #Q;
   assert #(H meet K) eq 1;
   assert IsAbelian (K);
   bas := PrimaryAbelianBasis(K);
   LK := [sub <K | [x : x in bas | x ne b]> : b in bas];
   J, L := MinRepDirectProduct (Q, H, LH, K, LK);
   return J, L;
end function;
