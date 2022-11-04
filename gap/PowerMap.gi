InstallMethod( PowerMap,
               "Computes the power map of a conjugacy class",
               [ IsConjugacyClassGroupRep ],

function(cls)
  local  g,        # the group G
         rep,      # representative of cls
         ord,      # order of rep
         classes,  # conjugacy classes of G
         res,      # the result
         pd,       # prime divisors of the order
         k,        # loop variable
         kclass,
         i,
         j,
         infolevel,
         ug,       # the units of ℤ/ord ℤ
         act,      # action
         ost,      # orbit stabiliser record
         cosets,
         transrep, # transversal
         posi,     # position in classes
         x,        # loop variable for elements of stab
         clres,    # result for powermaps of powers
         clord,    # order for powers
         class;    #


    g := ActingDomain(cls);
    rep := Representative(cls);

    ord := Order(rep);

    Info(InfoPositionClass, 2, "PositionClass/PowerMap: Computing Power map for a conjugacy class of order ", ord);

    classes := ConjugacyClasses(g);

    res := [ Position(ConjugacyClasses(g), cls) ];
    res[ord] := 1;

    if ord <= 2 then
        return res;
    fi;


    if not IsPrime(ord) then
        pd := PrimeDivisors(ord);

        # copy the powers from already computed power maps
        for k in pd do
            Info(InfoPositionClass, 2, "CTUnger/PowerMap: using power map of ", k, "th power");

            res[k] := PositionClass(g, rep^k);
            kclass := classes[res[k]];

            # if HasPowerMap(kclass) then
                for i in [1..ord/k-1] do
                    Info(InfoPositionClass, 3, "CTUnger/PowerMap: filled in ", k*i, "th power using k=", k,".");
                    if not IsBound(res[k*i]) then
                        res[k*i] := PowerMap(kclass)[i];
                    fi;
                od;
            # fi;
        od;
    fi;

    # temporarily reduce info level to avoid unneccessary warnings
    infolevel := InfoLevel(InfoWarning);
    SetInfoLevel(InfoWarning, 0);

    ug := Units(ZmodnZ(ord)); # these are the missing powers

    act := function(alpha, x)
        return PositionClass(g, Representative(classes[alpha])^Int(x));
    end;

    ost := OrbitStabilizerTransversal(ug, Position(ConjugacyClasses(g), cls), act);

    cosets := RightCosets(ug, ost.stabilizer);

    for i in [1..Length(ost.orbit)] do
        transrep := ost.rep[i];
        posi := ost.orbit[i];
        for x in ost.stabilizer do
            res[Int(x*transrep)] := posi;
            Info(InfoPositionClass, 2, "Filling in entry ", Int(x*transrep), " with ", posi);
        od;
    od;

    #brute force missing
    for i in [1..ord] do
        if not IsBound(res[i]) then
            res[i] := PositionClass(g, rep^i);
        fi;
    od;

    # install power maps
    for i in [1..ord] do
        class := classes[res[i]];
        if not HasPowerMap(class) then
            clord := Order(Representative(class));
            clres := [];
            for j in [1..clord-1] do
                clres[j] := res[j*i mod ord];
                clres[clord] := 1;
            od;

            SetPowerMap(class, clres);
        fi;
    od;

    # reset to the original info level
    SetInfoLevel(InfoWarning, infolevel);

    return res;
end);


InstallMethod( PosClassComputeAllPowerMaps,
               "computes all power maps of conjugacy classes",
               [ IsGroup ],
function(G)
    local C;

    List(ConjugacyClasses(G), PowerMap);
    SetAllClassesHavePowerMaps(G, true);
    C := CharacterTable(G);
    SetUnderlyingGroupHasClassPowerMaps(C, true);

end);

InstallMethod( PosClassExportPowerMaps,
               "writes the power maps of the classes into the character table",
               [ IsGroup ],
function(G)
    local tbl, orders, allpowmaps, i, n, ex;

    tbl := CharacterTable(G);
    orders := List(ConjugacyClasses(G), x -> Order(Representative(x)));

    allpowmaps := [];

    for n in [1..Maximum(orders)] do
        allpowmaps[n] := [];
        for i in [1..Length(orders)] do
            ex := n mod orders[i];
            if ex = 0 then
                ex := orders[i];
            fi;
            allpowmaps[n][i] := PowerMap(ConjugacyClasses(G)[i])[ex];
        od;
    od;

    SetComputedPowerMaps(tbl, allpowmaps);
end);

InstallMethod( PowerMap,
               "for a character table, and two integers",
               [ UnderlyingGroupHasClassPowerMaps and IsNearlyCharacterTable, IsInt, IsInt ],
function( tbl, n, class )
    local G, cls, ex;

    G := UnderlyingGroup(tbl);
    cls := ConjugacyClasses(G)[class];
    ex := n mod Order(Representative(cls));
    if ex = 0 then
        return 1;
    fi;
    return PowerMap(cls)[ex];
end);
