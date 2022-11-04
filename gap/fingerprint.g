#############################################################################
##
#F  FingerPrintFunction( <r>, <l> ) . . . . . . returns function which computes
#F  finger print of elements
##
##  If  <r>.g  moves   at  most MAXNUMBERPOINTSFINGERPRINT (default   200)
##  points, then a function f is  returned which computes the fingerprints
##  of cycles of fixed length of an element.
##
##  (Else a constant function is returned.)
##
##  This is a refinement of the *fingerprint* used in the programs for the
##  Dixon-Schneider algorithm:
##
##  Number the orbits   of <r>.g on the set   of pairs of moved  points of
##  <r>.g by 1..k. For a given element x  in <r>.g the fingerprint f(x) is
##  a list   whose  i-th  entry tells   for   each l in [1..k]    how many
##  (i+1)-cycles [p0, p1, .., pi] of x have the following property:
##
##    [p0,p1] is contained in orbit l of pairs of points
##
##  (Obviously l does not depend on the choice  of the pair [p0,p1] in the
##  cycle.)
##
##  This is clearly a class  invariant, since any y in  <r>.g maps a cycle
##  via conjugation onto
##
##    [p0, p1, .., pi]^y = [p0^y, p1^y, .., pi^y]
##
FingerPrintFunction:=function( r, l)
  local po, m, k, h, sp, p, a, b, i, j, S, orbs, tmp;

   MAXNUMBERPOINTSFINGERPRINT:=200;
  r := rec( g := G, help := []);

  m:=LargestMovedPoint(r.g);

  # orbits of points and transversals:
  po:=PointsRepOrb(r.g);
  po[1]:=Filtered(po[1],a->Length(a)>1);
  po[2]:=Filtered(po[2],a->Length(a)>1);

  # if there are too many moved points:
  if Sum(List(po[1],Length))>MAXNUMBERPOINTSFINGERPRINT then
    return x->0;
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
    S:=Stabilizer(r.g,p);
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
    return x->0;
  fi;

  h:=Length(r.help)+1;
  r.help[h]:=sp;
  r.help[h+1]:=orbs;

  # return a function which gives list of fingerprints
  # on cycles with fixed length:return
      function(x)
        local k, y, cys, degree, mark, i, j, len, cyc;
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
                    y:=sp[i];
                    k:=orbs[i^y][(i^x)^y];
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
      end;
end;
#############################################################################
##
#F  PointsRepOrb( <g> ) . . . . . orbits of points under permutation group <g>
#F  and transversal
##
##  <g>  must be  a  permutation  group.   'PointsRepOrb'  returns a  list
##  [orb,rep].   Here    orb is    a     list   of the    <g>-orbits    on
##  [1..LargestMovedPoint(<g>)]. rep[i][j]  is    an x in  <g>   such that
##  orb[i][j]^x=orb[i][1].
##
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
