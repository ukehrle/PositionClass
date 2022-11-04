            PointsRepOrb:=function ( arg )
                local  G, orbs, orb, max, g, gs, new, gen, Ggen, p, pnt, fst, img;
                G:=arg[1];

                max := LargestMovedPoint(G);

                Ggen:= GeneratorsOfGroup(G);
                new := BlistList( [ 1 .. max ], [ 1 .. max ] );
                orbs := [  ];
                gs:=[];
                fst := 1;
                while fst <> fail  do
                    orb := [ fst ];
                    g:=[()];
                    new[fst] := false;
                    p:=1;
                    while p<=Length(orb)  do
                        for gen  in Ggen  do
                            img := orb[p] ^ gen;
                            if new[img]  then
                                Add( orb, img );
                                Add(g, gen^(-1)*g[p]);
                                new[img] := false;
                            fi;
                        od;
                        p:=p+1;
                    od;
                    Add( orbs, orb );
                    Add( gs, g );
                    fst := Position( new, true, fst );
                od;
                return [orbs,gs];
            end;
InstallValue( PosClassConjugacyTestFunctions,
rec (
    CacheTest := rec (
        name := "CacheTest",
        cost := x -> 1,
        filters := [ ],
        type := "simple",
        fun := function(rep, x, r)
            local val;
            if not IsBound(rep.cache) then
                rep.cache := NewDictionary(x, true);
                return fail;
            fi;

            val := LookupDictionary(rep.cache, x);
            if val <> fail then
                Info(InfoPositionClass, 1, "PositionClass: Cache hit!");
                return val;
            fi;
            return fail;
        end
    ),

    StoreCache := rec (
        name := "StoreCache",
        cost := x -> 1,
        filters := [ ],
        type := "postHook",
        fun := function(rep, x, r)
            if Length(r) > 1 then
                return;
            fi;

            if not IsBound(rep.cache) then
                rep.cache := NewDictionary(x, true);
                return;
            fi;

            if Size(rep.cache) >= 10000 then
                rep.cache := NewDictionary(x, true);
            fi;

            AddDictionary(rep.cache, x, r[1]);
        end
    ),

    TrivialTest := rec(
        name := "TrivialTest",
        cost := x -> 1,
        filters := [ ],
        type := "simple",
        fun := function(rep, x, r)
            local k;

            if not IsBound(rep.sortedclreps) then
                rep.sortedclreps := ShallowCopy(rep.clreps);
                rep.indices := [1..Length(rep.clreps)];
                SortParallel(rep.sortedclreps, rep.indices);
            fi;

            k := PositionSortedEq(rep.sortedclreps, x);
            if k = fail then
                return fail;
            else
                return rep.indices[k];
            fi;
        end
    ),

    RandomTest := rec(
        name := "RandomTestPerm",
        cost :=
            # this test only makes sense if at least one of the nontrivial classes is somewhat
            # moderately sized.
            function(rep)
                if ForAll(rep.clreps, x -> Size(x^rep.g) >= 1000000 or x = x^0) then
                    return 1000000000;
                else
                    return 500;
                fi;
            end,
        description := Concatenation(
          "Tries to identify the classes by permuting <x> with random elements. ",
          "Success probability with class sizes at most k, l stored elements, n tries is  ",
          "1 - (1-l/k)^n. for example with l = 1 million, k = 1000, n = 1000: ~2/3 "
         ),
        filters := [ IsPermGroup ],
        type := "simple",
        fun := function(rep, x, r)
            local  i, y, j;
            if not IsBound(rep.base) then
                rep.base := BaseOfGroup(rep.g);
            fi;
            if not IsBound(rep.randomDict) then
                rep.randomDict := NewDictionary([ 1,2,3] , true);
                for i in [1..Length(rep.clreps)] do
                    if Size(ConjugacyClass(rep.g, rep.clreps[i])) < 1000 then
                        for y in ConjugacyClass(rep.g, rep.clreps[i]) do
                            AddDictionary(rep.randomDict,
                                          OnTuples(rep.base, y), i);
                        od;
                    else
                        for j in [1..1000] do
                            y := PseudoRandom(rep.g);
                            AddDictionary(rep.randomDict,
                                          OnTuples(rep.base, rep.clreps[i]^y), i);
                        od;
                    fi;
                od;
            fi;

            # only run test if at least one of the classes yet to distinguish is "small"
            if ForAll(r, i -> Size(rep.clreps[i]^rep.g) >= 1000000) then
              return fail;
            fi;

            for i in [1..1000] do
                x := x^PseudoRandom(rep.g);
                y :=  LookupDictionary(rep.randomDict, OnTuples(rep.base, x));
                if y <> fail then
                    return y;
                fi;
            od;

            return fail;
        end
    ),

    NiceMonomorphismHook := rec(
        name := "NiceMonomorphismHook",
        description := Concatenation(
          "checks whether rep.g has a NiceMonomorphism. ",
          "In this case it is installed as an additional",
          "representation and the test tree is rebuilt."),
        cost := x -> 0,
        filters := [ IsMatrixGroup ],
        type := "custom",
        fun := function(PR, rep, x, r, curr)
            local f, g;
            if HasNiceMonomorphism(rep.g) then
                f := NiceMonomorphism(rep.g);
                # the nice monomorphism representation might already be present.
                # Let's check.
                if ForAll(PR.representations, r -> r.hom <> f) then
                    # this code only works for the first representation
                    # Could be adjusted by using the composition of the homs,
                    # but this is probably never useful?
                    if rep.hom = IdentityMapping(rep.g) then
                        Info(InfoPositionClass, 1,
                             "Installing representation handled by nice monomorphism");
                        Add(PR.representations,
                            rec (
                            g := NiceObject(rep.g),
                            hom := NiceMonomorphism(rep.g),
                            name := Concatenation("NiceMonomorphism-", rep.name),
                            inv := rec (),
                            separates := true,
                            clreps := List(rep.clreps, a -> a^f)
                        ));
                        # remove this hook from the tests as it won't yield anything useful anymore.
                        PosClassInitTests(PR);
                        Info(InfoPositionClass, 1, "Removing nice monomorphism hook");
                        PR.tests := Filtered(PR.tests, x -> x.name <> Concatenation("NiceMonomorphismHook-", rep.name));
                        return PR.tree;
                    fi;
                fi;
                # remove this hook anyway.
                Info(InfoPositionClass, 1, "Removing nice monomorphism hook");
                PR.tests := Filtered(PR.tests, x -> x.name <> Concatenation("NiceMonomorphismHook-", rep.name));
            fi;
            return rec (classes := curr.classes, testNr := curr.testNr + 1);
        end
    ),

    CycleStructureTest := rec(
        name := "CycleStructureTest",
        cost := x -> 20,
        type := "invariant",
        filters := [ IsPermGroup ],
        fun := function(rep, x)
            local cysl,cys,mark,i,j,len,p,orb,perm;

            if not IsBound(rep.orbits) then
                rep.orbits := Orbits(rep.g);
            fi;

            perm := x;
            orb := rep.orbits;

            # this is taken from gap3/CHEVIE, written by Frank Lübeck, GPL2+
            if perm = ()  then return [];fi;
            mark := BlistList([],[]); cysl := [  ];
            for j in orb do
                cys:=[];
                for i  in j  do
                if not IsBound(mark[i]) then
                    len:=0; mark[i]:=true; p:=i^perm;
                    while not IsBound(mark[p]) do len:=len+1;mark[p]:=true;p:=p^perm;od;
                    if 0 < len  then
                        if IsBound( cys[len] )  then cys[len] := cys[len] + 1;
                        else cys[len] := 1;
                        fi;
                    fi;
                fi;
                od;
                Add(cysl,cys);
            od;
            return cysl;
        end
        ),

    # does not work for unknown reasons.

    # PcTest := rec (
    #     name := "PcTest",
    #     cost := x -> -1,
    #     type := "invariant",
    #     filters := [ IsPcGroup ],
    #     init := function(rep)
    #         rep.dat := rec ( group := rep.g );
    #         MultiClassIdsPc(rep.dat, rep.clreps);
    #     end,
    #     fun := function(rep, x)
    #         return MultiClassIdsPc(rep.dat, [x])[1];
    #     end
    # ),

    FingerPrintPermTest := rec (
        name := "FingerPrintPerm",
        cost := x -> 10,
        type := "invariant",
        filters := [ IsPermGroup ],
        init := function(rep)
            local m, po, sp, a, S, orbs, k, tmp, j, p, i, b;

            m:=LargestMovedPoint(rep.g);

            # orbits of points and transversals:
            po:=PointsRepOrb(rep.g);
            po[1]:=Filtered(po[1],a->Length(a)>1);
            po[2]:=Filtered(po[2],a->Length(a)>1);

            # if there are too many moved points:
            if Sum(List(po[1],Length))> 200 then
                rep.fingerprintskip := true;
                return;
            fi;

            # elements mapping p to smallest point in orbit
            sp:=[];
            for a in [1..Length(po[1])] do
                for i in [1..Length(po[1][a])] do
                sp[po[1][a][i]]:=po[2][a][i];
                od;
            od;

            # determine different orbits of pairs of points:
            orbs:=[];
            k:=1;
            for a in [1..Length(po[1])] do
                p:=po[1][a][1];
                S:=Stabilizer(rep.g,p);
                tmp:=Orbits(S,[1..m]);
                orbs[p]:=[];
                for b in tmp do
                if IsBound(sp[b[1]]) then
                    for j in b do
                    orbs[p][j]:=k;
                    od;
                    k:=k+1;
                fi;
                od;
            od;

            # not usable if r.g is two times transitive on moved points:
            if k=2 then
                rep.fingerprintskip := true;
                return;
            fi;
            rep.fingerprintsp := sp;
            rep.fingerprintorbs := orbs;

            return;
        end,

        fun := function(rep, x)
            local k, y, cys, degree, mark, i, j, len, cyc;
            if IsBound(rep.fingerprintskip) then
                return 0;
            fi;

            if x=() then
                return [];
            fi;
            degree := LargestMovedPoint( x );
            mark := BlistList( [ 1 .. degree ], [  ] );
            cys := [  ];
            for i  in [ 1 .. degree ]  do
                if not mark[i]  then
                    cyc := Cycle( x, i );
                    len := Length( cyc ) - 1;
                    if 0 < len  then
                        y:=rep.fingerprintsp[i];
                        k:=rep.fingerprintorbs[i^y][(i^x)^y];
                        if IsBound( cys[len] )  then
                            Add(cys[len],k);
                        else
                            cys[len] := [k];
                        fi;
                    fi;
                    for j  in cyc  do
                        mark[j] := true;
                    od;
                fi;
            od;
            for i in [1..Length(cys)] do
            if IsBound(cys[i]) then
                cys[i]:=Collected(cys[i]);
            fi;
            od;
            return cys;
        end
        ),

    
    PrimaryInvariantTest := rec(
        name := "PrimaryInvariantTest",
        cost := x -> 10,
        type := "invariant",
        filters := [ IsMatrixGroup ],
        fun := function(rep, x) return InvariantFactorsMat(x); end
        ),

    ConjugateTest := rec (
        name := "ConjugateTest",
        cost := x -> 10000,
        type := "simple",
        filters := [ IsGroup ],
        fun := function(rep, x, r)
            local i, n;

            n := Length(r);
            i := 1;


            while i < n and not IsConjugate(rep.g, x, rep.clreps[r[i]]) do
                i := i+1;
                hardcnt := hardcnt +1;
            od;
            hardcnt := hardcnt +1;

            return r[i];
        end
        ),

    ConjugateTestPerm := rec (
        name := "ConjugateTestPerm",
        cost := x -> 1000,
        type := "simple",
        filters := [ IsPermGroup ],
        init := function(rep)
            local i;

            if not IsBound(rep.isconjdata) then
                rep.isconjdata := [];
                for i in [1..Length(rep.clreps)] do;
                    rep.isconjdata[i] := IsConjData(rep.g, rep.clreps[i]);
                od;
            fi;
        end,
        fun := function(rep, x, r)
            local data, i, n;

            if not IsBound(rep.isconjdata) then
                rep.isconjdata := [];
            fi;

            n := Length(r);
            i := 1;
            while i < n do
                if not IsBound (rep.isconjdata[r[i]]) then
                    rep.isconjdata[r[i]] := IsConjData(rep.g, rep.clreps[r[i]]);
                fi;

                if IsConjTest(rep.isconjdata[r[i]], x) then
                    break;
                fi;

                i := i+1;
            od;

            return r[i];
        end
    )
));


InstallValue( PosClassConjugacyDefaultFunctions,
    [ PosClassConjugacyTestFunctions.TrivialTest
    # , PosClassConjugacyTestFunctions.NiceMonomorphismHook
    # , PosClassConjugacyTestFunctions.CacheTest
    # , PosClassConjugacyTestFunctions.StoreCache
    # , PosClassConjugacyTestFunctions.RandomTest
    , PosClassConjugacyTestFunctions.CycleStructureTest
    , PosClassConjugacyTestFunctions.FingerPrintPermTest
    , PosClassConjugacyTestFunctions.PrimaryInvariantTest
    # , PosClassConjugacyTestFunctions.CentralizerOrderTest
    # , PosClassConjugacyTestFunctions.PowerMapTest
    , PosClassConjugacyTestFunctions.ConjugateTest
    , PosClassConjugacyTestFunctions.ConjugateTestPerm
    # , PosClassConjugacyTestFunctions.PcTest
    ]);


InstallMethod( PositionClassRecord,
               "Sets up PositionClass record for a group",
               [ IsGroup ],

function(G)
    return rec ( enabledTests := PosClassConjugacyDefaultFunctions,
                 cache := NewDictionary(Identity(G), true),
                 representations := [
                         rec (
                              g := G,
                              hom := IdentityMapping(G),
                              name := "default",
                              inv := rec (),
                              separates := true,
                              clreps := List(ConjugacyClasses(G), Representative),
                              )
                         ]
                 );
end);

