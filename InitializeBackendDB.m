/*
	This is a first attempt at creating a file to initialize the database.
	Created May 18, 2026, by Robert Lemke Oliver.
*/

// Load the file where the records are created.

load "RecordTypes.m";

// Set database limits

MaxDegree := 12;
MaxOrder := 63;

// Create the permutation group database
// We'll seed with the value of Malle's a(G) and Bhargava's improvement to the Schmidt bound

NF_PermGrp_DB := [];

print "Initializing permutation group DB:";
IndentPush();

for n in [1..MaxDegree] do
	print "Working with degree",n;
	TGP:=TransitiveGroupProcess(n);
	id := 1;
	while not IsEmpty(TGP) do
		G:=Current(TGP);
		
		G_rec := rec< NFPermGroupRec | degree:=n, label:=id, order:=#G, nilpotent:=IsNilpotent(G), solvable:=IsSolvable(G)>;
		
		Cycs:=CyclicSubgroups(G);
		inds:=[n - #Orbits(c`subgroup) : c in Cycs | #(c`subgroup) gt 1];
		if n ge 2 then
			G_rec`malle_a := Minimum(inds);
			G_rec`upper_bound := (n-2)/4 + 1/G_rec`malle_a;
			
			conc_subgp := ncl< G | [c`subgroup : c in Cycs | n-#Orbits(c`subgroup) eq G_rec`malle_a]>;
			if conc_subgp eq G then
				G_rec`concentrated := false;
			else
				G_rec`concentrated := true;
				G_rec`concentrated_subgroup := conc_subgp;
			end if;
		end if;
		
		Append(~NF_PermGrp_DB,G_rec);
		
		Advance(~TGP);
		id:=id+1;
	end while;
end for;
IndentPop();

print "";


// Create the abstract group database
// We'll seed with Malle's a and a Galois upper bound from Min(Bhargava-Schmidt, 3.046/Sqrt(#G))

NF_AbstractGrp_DB := [];

print "Initializing abstract group DB:";
IndentPush();

for n in [1..MaxOrder] do
	print "Working with order",n;
	SGP := SmallGroupProcess(n);
	id := 1;
	while not IsEmpty(SGP) do
		G:=Current(SGP);
		
		G_rec := rec< NFAbstractGroupRec | order:=n, label:=id, nilpotent:=IsNilpotent(G), solvable:=IsSolvable(G)>;
		
		if n ge 2 then
			p := Divisors(n)[2];
			G_rec`galois_a:= (p-1) * (n div p);
			G_rec`radical_a:=1;
			
			galois_conc_subgp := ncl< G | [c[3] : c in ConjugacyClasses(G) | Order(c[3]) eq p]>;
			if galois_conc_subgp eq G then
				G_rec`galois_concentrated:=false;
			else
				G_rec`galois_concentrated:=true;
			end if;
			
			G_rec`galois_upper_bound := Min( (n-2)/4+1/G_rec`galois_a, 3.046 / Sqrt(n));
			
		end if;
		
		// Find the transitive representations in our DB
		core_free_subs := [ h`subgroup : h in Subgroups(G : IndexLimit := MaxDegree) | #Core(G,h`subgroup) eq 1];
		
		trans_reps := [];
		
		for H in core_free_subs do
			Append(~trans_reps,[Index(G,H), TransitiveGroupIdentification(CosetImage(G,H))]);
		end for;
		
		G_rec`transitive_reps := trans_reps;
		
		Append(~NF_AbstractGrp_DB,G_rec);
		
		Advance(~SGP);
		id:=id+1;
	end while;
end for;
IndentPop();
