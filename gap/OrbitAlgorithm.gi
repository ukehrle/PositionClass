# these methods are copied from <gap>/lib/oprt.gi with minor changes

#############################################################################
##
#F  OrbitStabilizer( <arg> )  . . . . . . . . . . . . .  orbit and stabilizer
##


InstallMethod( OrbitStabilizerTransversal,
               "variant for expensive actions",
               true,
               [IsGroup,IsObject,IsObject],
               1,

function( G, d, act )
    local orb, stb, rep, p, q,img, sch, i, gens, dict;

    gens := GeneratorsOfGroup(G);

    Info(InfoPositionClass, 1, "enter osta!");

    dict:=NewDictionary(d,true);

    # `false' the index `ind' must be equal to the orbit size.
    orb := [ d ];
    AddDictionary(dict,d,1);
    rep := [ One( G ) ];

    Info(InfoPositionClass, 1, "starting the actual run!");

    stb := TrivialSubgroup(G); # stabilizer seed
    if not IsEmpty( gens )    then
        rep := [ One( gens[ 1 ] ) ];
        p := 1;
        while p <= Length( orb )    do
            for i in [ 1 .. Length( gens ) ]    do

                # !!
                if ForAny([1..Length(orb)], j -> rep[p]*gens[i]*Inverse(rep[j]) in stb ) then
                    continue;
                fi;


                Info(InfoPositionClass, 1, "evaluated an action!");
                img := act( orb[ p ], gens[ i ] );

                MakeImmutable(img);

                q := LookupDictionary(dict,img);

                if q = fail then
                    Add( orb, img );
                    AddDictionary(dict,img,Length(orb));
                    Add( rep, rep[ p ] * gens[ i ] );
                else
                    sch := rep[ p ] * gens[ i ] / rep[ q ];
                    # NC is safe
                    stb := ClosureSubgroupNC(stb, sch);
                fi;
            od;
            p := p + 1;
        od;

    fi;

    return rec( orbit := orb, stabilizer := stb, rep := rep );
end);
