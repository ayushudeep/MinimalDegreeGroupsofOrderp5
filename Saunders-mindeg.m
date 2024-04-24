// implementation by Neil Saunders of algorithm of:
// B. Elias, L. Silberman and R. Takloo-Bighash, 
// Minimal permutation representations of nilpotent groups, 
// Experiment. Math., {\bf 19} (1) (2010), 121–128.
//
// To call: 
// G := SmallGroup (64, 25); Mu(G);

function getMinFaithCollect(G)  // G is a permutation group

// Socle function only works for GPerm
// First finds the socle of G
// Then choose as K_1 the largest subgroups of G which does not contain K
// Then choose as K_2 the largest subgroups of G which does not contain K meet K1
// and so on until we get a faithful collection
 
   Inter:=Socle(G);
   subs:=Subgroups(G:IndexLimit:=Index(G,Socle(G)));
   F:=[]; //to become the faithful collection

   if #subs gt 10^6 then "Too many subgroups to process"; return []; end if;
   for j:=#subs to 1 by -1 do //going through the subgroups from largest to smallest
      sub:=subs[j]`subgroup;
      if ((Inter subset sub) eq false) then
        Append(~F,sub); //Add it to the collection
        Inter:=Inter meet sub; //maintain Inter
        if (IsTrivial(Inter)) then break; end if; //And stop if Inter=1
      end if;
   end for;
   return F;
end function;    

//--------------------------------------------------------------------------

function mu(F)

// This is the Cayley sum of a collection
// Returns the sum of 1/Order(x) for all x in F

   alph:=0;
   for i:=1 to #F do
      alph +:=1/Order(F[i]);
   end for;
   return alph;
end function;

//----------------------------------------------------------------------

function Mu(G)
   if IsAbelian (G) then 
       phi, I := MinimalDegreePermutationRepresentation (G);
       return Degree (I);
   end if;
   F:=getMinFaithCollect(G);
   if #F eq 0 then "Abandon this case"; return 0; end if;
   M:=Order(G)*mu(F);
   return M;
end function;
