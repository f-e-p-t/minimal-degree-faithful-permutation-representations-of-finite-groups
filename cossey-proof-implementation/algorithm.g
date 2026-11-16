NaturalHomomorphismChain := [];

ComputeLAndD := function(G, N, deg)
    local orbits, L_gens, L, N_W, W, g, global_list, gens, i, j, g_global, Y, D, E_, y, y2, W2, yW2, l, OtherPoints, L_NoJunk,
    ImagesOfGens, HomGD;
    orbits := Orbits(N, [1..deg]);
    L_gens := [];
    Y := [];

    for W in orbits do
        AddSet(Y, Minimum(W));
        N_W := Image(ActionHomomorphism(N, W, OnPoints));
        gens := GeneratorsOfGroup(N_W);
        for g in gens do
            global_list := [1..deg];
            for j in [1..Length(W)] do
                global_list[W[j]] := W[j^g];
            od;

            g_global := PermList(global_list);
            if g_global <> fail then
                AddSet(L_gens, g_global);
            fi;
        od;
    od;

    L := Group(L_gens);
    E_ := ClosureGroup(G, L);
    D := Stabilizer(E_, Y, OnSets);

    ImagesOfGens := [];
    i := 1;
    for g in GeneratorsOfGroup(G) do
        for W in orbits do
            y := Y[i]; y2 := y^g;
            W2 := Orbit(N, y2, OnPoints);
            yW2 := Minimum(W2);
            OtherPoints := Difference([1..deg], W2);
            L_NoJunk := Stabilizer(L, OtherPoints, OnTuples);
            l := RepresentativeAction(L_NoJunk, y2, yW2, OnPoints);
            g := g * l;
            #Print(y, " in orbit ", W, " goes to ", y2, " in orbit ", W2, ". Sent back to ", yW2, " by ", l, "\n");
            i := i + 1;
        od;
        Add(ImagesOfGens, g);
        i := 1;
    od;
    Print("Images are ", ImagesOfGens, " which must fix ", Y, " setwise\n\n");
    HomGD := GroupHomomorphismByImages(G, D, GeneratorsOfGroup(G), ImagesOfGens);
    Add(NaturalHomomorphismChain, HomGD);

    return [L, D];
end;

MinimalNormalSubgroupContainedIn := function(G, H)
    local M, N, min_normals;

    if not IsSubgroup(G, H) then
        Print("Not a subgroup");
        return TrivialGroup;
    fi;

    min_normals := MinimalNormalSubgroups(G);

    for N in min_normals do
        if IsSubgroup(H, N) then
            return N;
        fi;
    od;

    Print("No minimal normal subgroup found\n");
    return TrivialGroup;
end;

CosseyProof := function(G)
    local FitG, deg, FitD, LFitD, SocleLFitD, FitGPrime, N, LAndD, SocleG, S, SD, step, DGens, InclusionDSD;

    deg := DegreeAction(G);

    FitG := FittingSubgroup(G);

    if IsAbelian(FitG) then
        Print("Fitting subgroup is abelian\n");
        LAndD := ComputeLAndD(G, FitG, deg);
        return LAndD[2];
    fi;

    FitGPrime := DerivedSubgroup(FitG);
    SocleG := Socle(G);
    N := MinimalNormalSubgroupContainedIn(G, FitGPrime);
    LAndD := ComputeLAndD(G, N, deg);
    FitD := FittingSubgroup(LAndD[2]);
    LFitD := ClosureGroup(LAndD[1], FitD);
    SocleLFitD := Socle(LFitD);
    S := Intersection(SocleLFitD, LAndD[1]);
    SD := ClosureGroup(S, LAndD[2]);

    DGens := GeneratorsOfGroup(LAndD[2]);
    InclusionDSD := GroupHomomorphismByImages(LAndD[2], SD, DGens, DGens);
    Add(NaturalHomomorphismChain, InclusionDSD);

    Print("Recursion step\n");
    step := CosseyProof(SD);
    return step;
end;

# ------------------------------------------------

#G := TransitiveGroup(24, 24642);
G := Group(
  (1, 6, 2)(3, 5, 7)(4, 9, 8)(10, 21, 13, 14, 11, 23, 16, 17)(12, 25, 18, 22, 
        15, 20, 24, 19)(26, 30, 29, 34, 31, 33, 28, 32)(35, 41, 39, 48, 36, 38, 
        42, 46)(37, 43, 44, 45, 40, 49, 47, 50),
    (1, 8, 2, 9, 6, 4)(3, 5, 7)(10, 41)(11, 38)(12, 43)(13, 46, 23, 35, 14, 
        39)(15, 49)(16, 48, 21, 36, 17, 42)(18, 50, 25, 40, 19, 47)(20, 37, 22, 
        44, 24, 45)(26, 29, 30, 27, 34, 28)(31, 33, 32),
    (1, 26, 2, 27)(3, 29, 9, 30)(4, 28, 5, 34)(6, 31)(7, 33, 8, 32)(10, 39, 24, 
        45, 23, 35, 22, 43, 11, 42, 18, 50, 21, 36, 19, 49)(12, 44, 13, 48, 25, 
        37, 14, 41, 15, 47, 16, 46, 20, 40, 17, 38),
    (2, 6)(3, 7)(4, 8)(10, 42, 24, 49, 11, 39, 18, 43)(12, 44, 13, 41, 15, 47, 
        16, 38)(14, 48, 22, 50, 17, 46, 19, 45)(20, 37, 23, 35, 25, 40, 21, 
        36)(26, 30, 32, 33, 29, 27)(28, 31, 34),
    (1, 28)(2, 26, 9, 31, 6, 33, 5, 34)(3, 32, 4, 29, 8, 30, 7, 27)(10, 35, 15, 
        37, 11, 36, 12, 40)(13, 42, 19, 43, 16, 39, 22, 49)(14, 41, 18, 44, 17, 
        38, 24, 47)(20, 45, 23, 46, 25, 50, 21, 48),
    (1, 26)(2, 29, 8, 27, 9, 33, 7, 34, 6, 32, 3, 31, 5, 28, 4, 30)(10, 36, 17, 
        42, 21, 41, 11, 35, 14, 39, 23, 38)(12, 37, 22, 44, 20, 43, 15, 40, 19, 
        47, 25, 49)(13, 48, 16, 46)(18, 45, 24, 50),
    (1, 8, 5, 6, 9, 7)(2, 4, 3)(10, 14, 13, 11, 17, 16)(12, 19, 18, 15, 22, 
        24)(20, 25)(21, 23)(28, 29)(30, 34)(32, 33)(38, 48, 39)(41, 46, 42)(43, 
        50, 44)(45, 47, 49) );

Print("\n\nGroup:\n", G, "\n\n");
Print("Order of group:\n", Order(G), "\n\n");
Print("Order of fitting subgroup:\n", Order(FittingSubgroup(G)), "\n\n");

G_hom := IsomorphismPermGroup(G);
G_perm := Image(G_hom);
Fit := FittingSubgroup(G_perm);

Representation := CosseyProof(G_perm);
Print("\nRepresentation of G/F(G):\n", Representation, "\n");

NaturalHom := NaturalHomomorphismChain[1];
i := 1;
for map in NaturalHomomorphismChain do
    if i = 1 then
        i := i + 1;
        continue;
    fi;
    NaturalHom := CompositionMapping(map, NaturalHom);
    i := i + 1;
od;

ImageNH := Image(NaturalHom);

if Representation = ImageNH then
    Print("\nNatural homomorphism from G to G/F(G):\n", NaturalHom, "\n\nwith image:\n", ImageNH);
fi;

Print("\n\nSize of representation:\n", Size(Representation));