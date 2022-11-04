##  isconj.g                          Frank Lübeck,  LfAZ 2022
##
##  Some experimental code for testing conjugacy of elements
##  in a permutation group.
##
##  A description is in (page 673):
##    Gregory Butler, Computing in Permutation and Matrix Groups II:
##    Backtrack Algorithm, Mathematics of Computation, Vol. 39,
##    No. 160 (Oct., 1982), pp. 671-680
##
##  Basic idea: conjugating maps cycles to cycles, a conjugating element must
##  map points to points in cycles of same length. When one point of a cycle is
##  mapped then the images of all other points in same cycle are also fixed.
##
##  For a fixed representative of a class we precompute a fixed stabilizer
##  chain where the base points are a concatenation of the cycles of pi.
##  Further optimization should be possible by better choices of the ordering of
##  the cycles.
##
##  Example:
##    g := AtlasGroup("Co2");
##    repeat x := Random(g); until Order(x) = 23;
##    dat := IsConjData(g, x);;
##    IsConjTest(dat, x^Random(g));
##    IsConjTest(dat, (x^5)^Random(g));

# args: pi permutation
#       max  integer >= largest moved point of pi
#
# returns information about cycles of pi, sorted by multiplcity
OrbLengths := function(pi, max)
  local cyc, lens, cl, ol, l, o, j, res;
  cyc := Cycles(pi, [1..max]);
  lens := [];
  cl := [];
  ol := [];
  for o in cyc do
    l := Length(o);
    AddSet(lens, Length(o));
    if not IsBound(cl[l]) then
      cl[l] := [o];
    else
      Add(cl[l], o);
    fi;
    for j in o do
      ol[j] := l;
    od;
  od;
  res := [lens, List(lens, l-> Concatenation(cl[l])), ol];
  SortParallel(res[2], res[1], {a,b}-> Length(a)<Length(b));
  return res;
end;

#### ol: points to cycle lengths
#### cl: lengths to points
#### lens: lengths

#    result: first component: lengths, second component points grouped by cycle length , third component, point to cycle length mapping.

# args: G: permutation group,
#       pi: permutation in Sym([1..max moved point of G])
# simple data structure for testing if elements are G-conjugate to pi
#  - the essential part is a stabilizer chain of G which starts
#    with cycles of pi (starting with those of least multiplicity)
IsConjData := function(G, pi)
  local o, res;
  o := OrbLengths(pi, LargestMovedPoint(G));
  #res := rec(p := pi, lens := o[1], lensets := o[2], lenp := o[3]);
  res := rec(p := pi, lenp := o[3]);
  res.stb := StabChain(G, Concatenation(o[2]));
  return res;
end;

# args: data: result of IsConjData(G, pi)
#       s: permutation (with same cycle structure as pi)
#       more...: only used in recursive calls (orbit lengths of s and
#                                              current cycle to be mapped)
#
# returns true if pi is  G-conjugate to s, false otherwise
IsConjTest := function(data, s, more...)
  local sol, cyc, o, pt, pos, a, scyc, only, t, ss, ssol, sdata,
        tst, len, j, orep;

  if Length(more) = 0 then
    sol := OrbLengths(s, Length(data.lenp))[3];
    cyc := false;
  else
    sol := more[1];
    cyc := more[2];
  fi;

  # current orbit and base point in stabilizer chain
  o := data.stb.orbit;
  pt := o[1];
  if cyc <> false then
    a := cyc[1];
    scyc := [a];
    repeat
      a := a^s;
      Add(scyc, a);
    until a = cyc[1];
    pos := Position(cyc, pt);
    if pos <> fail then
      # in this case the new base point is in a cycle of previous base
      # points; there is only one possibility where pt can be mapped by a
      # conjugating element (called 'only' below)
      if ForAny([1..pos-1], k-> cyc[k] <> scyc[k]) then
        return false;
      fi;
      only := scyc[pos];
      pos := Position(o, only);
      if pos = fail then
        return false;
      else
        t := InverseRepresentative(data.stb, only);
        ss := s^t;
        if not IsBound(data.stb.stabilizer) or
          IsEmpty(data.stb.stabilizer.generators) then
          return ss = data.p;
        fi;
        ssol := Permuted(sol, t);
        sdata := ShallowCopy(data);
        sdata.stb := data.stb.stabilizer;
        return IsConjTest(sdata, ss, ssol, cyc);
      fi;
    else
      # otherwise we check if the considered cycle is the same
      # for both elements; if yes reset 'cyc' and start over
      # with the cycle of 'pt' below
      if cyc <> scyc then
        return false;
      fi;
      cyc := false;
    fi;
  fi;
  if cyc = false then
    # in this case 'pt' is in a cycle not considered before; it can
    # only be mapped by a conjugating element to a point with same
    # cycle length in the other permutation
    cyc := [pt];
    a := pt;
    repeat
      a := a^data.p;
      Add(cyc, a);
    until a = pt;
    len := data.lenp[pt];
    if Length(more) = 0 then
      # on top level it suffices to check one point from each cycle in s
      # (if pi^x = s then also pi^(x*s^i) = s)
      orep := Set(List(Cycles(s,[1..Length(data.lenp)]), a-> a[1]));
      o := Filtered(o, i-> i in orep);
    fi;

# here is room for further improvements:
#   - find criteria such that fewer points in o must be considered
#   - choose ordering of cycles for base such that the proportion of
#     points in o which are good for finding a conjugating element
#     becomes larger
    for j in o do
      if sol[j] = len then # sol : point to cycle length mapping.
        t := InverseRepresentative(data.stb, j);
        ss := s^t;
        if not IsBound(data.stb.stabilizer) or
          IsEmpty(data.stb.stabilizer.generators) then
          return ss = data.p;
        fi;
        ssol := Permuted(sol, t);
        sdata := ShallowCopy(data);
        sdata.stb := data.stb.stabilizer;
        tst := IsConjTest(sdata, ss, ssol, cyc);
        if tst then
          return true;
        fi;
      fi;
    od;
    return false;
  fi;
end;
