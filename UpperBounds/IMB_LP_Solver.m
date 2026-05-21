/*
	Code to compute an upper bound for a given inertial height function using a list of available inertial multiplicity bounds.  This follows the linear programming strategy suggested in RJLO's notes.
	
	Initial version created May 20, 2026, by Robert Lemke Oliver.
*/


function InertialUB_from_IMBs( weight, bounds : rational:=false, approx:=10^(-10))
	/* 
		Input:
			The weight of the target inertial height function.  This should be indexed by the conjugacy classes of nontrivial cyclic subgroups of a group G.
			A known list of inertial multiplicity bounds.
			Optionally: a boolean (rational) that indicates whether you expect the output to be rational
		Output:
			An upper bound on the number of fields ordered by the provided inertial height function.
	*/
	
	N := #weight;
	
	// Simplex constraints first
	
	SimplexConstraints := [];
	for i in [1..N] do
		v := [0 : i in [1..N]];
		v[i] := 1;
		Append(~SimplexConstraints,v);
	end for;
	Append(~SimplexConstraints,weight);
	
	SimplexTargets:=[ 0 : i in [1..N]] cat [1];
	SimplexRelations:=[1 : i in [1..N]] cat [-1];
	
	// I don't know an easy way to force Magma to use an objective function that's given as a mininimum of linear forms, so I'm going to brute force things a little bit.
	
	Alphas := [];
	
	for obj in [1..#bounds] do
	
		// Assume bounds[obj] is the minimum, and use it as the objective function.
		// Add constraints that ensure it actually is the minimum.
	
		min_imb := bounds[obj];
		
		MinConstraints := [ [bounds[i][j]-min_imb[j] : j in [1..N]] : i in [1..#bounds] | i ne obj];
		MinTargets := [ 0 : i in [1..#bounds-1]];
		MinRelations := [ 1 : i in [1..#bounds-1]];
		
		ConstraintMat := Matrix(RealField(), SimplexConstraints cat MinConstraints);
		TargetMat := Transpose(Matrix(RealField(), [SimplexTargets cat MinTargets]));
		RelationMat := Transpose(Matrix(RealField(), [SimplexRelations cat MinRelations]));
		ObjectiveMat := Matrix(RealField(), [min_imb]);
		
		MaxPt := MaximalSolution(ConstraintMat,RelationMat,TargetMat,ObjectiveMat);
		
		Append(~Alphas,&+[MaxPt[1][i]*min_imb[i] : i in [1..N]]);
	end for;
	
	MaxAlpha:=Max(Alphas);
	
	if rational eq false then
		return MaxAlpha;
	end if;
	
	i:=1;
	CFV := ContinuedFractionValue(ContinuedFraction(MaxAlpha : Bound:=1));
	while Abs(MaxAlpha - CFV) gt approx do
		i:=i+1;
		CFV := ContinuedFractionValue(ContinuedFraction(MaxAlpha : Bound:=i));
	end while;
	
	return CFV;
	
end function;
