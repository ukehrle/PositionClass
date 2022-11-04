# this function initializes the tests to be used  from PR.enabledTests
# It checks which tests are applicable, evaluates and sorts their costs and
# stores them and the representation they are run against in PR.tests
#
totalcnt := 0;
hardcnt := 0;
InstallGlobalFunction (PosClassInitTests,
function(PR)
    local  sepreps, rep, test, tests, postHooks, tmp, a, applicable, i;

    tests := [];
    postHooks := [];
    sepreps := [];

    # add all the "invariant" tests for non-separating representations.
    # we consider these as additional tests as they may produce different
    # results as the same test for the original rep.
    for rep in PR.representations do
        if not rep.separates then
            for test in Filtered(PR.enabledTests, x ->
                    x.type = "invariant" and
                    ForAll(test.filters, f -> f(rep.g))
                    ) do
                tmp := ShallowCopy(test);
                tmp.cost := tmp.cost(rep);
                tmp.rep := rep;
                tmp.name := Concatenation(tmp.name, "-", rep.name);
                tmp.stats := rec ( total := 0, success := 0 );
                Add(tests, tmp);
            od;
        else
            Add(sepreps, rep);
        fi;
    od;

    # for the separating reps, use the tests for the cheapest applicable rep
    for a in PR.enabledTests do
        test := ShallowCopy(a);

        applicable := Filtered(sepreps, x -> ForAll(test.filters, f -> f(x.g)));
        if IsEmpty(applicable) then
           continue;
        fi;

        SortBy(applicable, rep -> test.cost(rep) );
        test.cost := test.cost(applicable[1]);
        test.rep := applicable[1];
        test.name := Concatenation(test.name, "-", applicable[1].name);
        test.stats := rec ( total := 0, success := 0 );
        if IsBound(test.init) then
            test.init(rep);
        fi;
        if test.type = "postHook" then
            Add(postHooks, test);
        else
            Add(tests, test);
        fi;
    od;

    SortBy(tests, x -> x.cost);
    SortBy(postHooks, x -> x.cost);

    PR.tree := rec( classes := [1..Length(PR.representations[1].clreps)],
                    testNr := 1,
                    );

     PR.tests := tests;
     PR.postHooks := postHooks;
end
);
# PR has the following components:
# - tree: a decision tree
# - representations: a list of alternative representations that are records
#      with components:
#        g: an object that is somehow associated with this represenatiton.
#           this is what the filters of the tests are applied to.
#        hom: unbound or the homomorphism that maps elements from the first
#           representation to this one
#        clreps: representatives of the classes
#        separates: whether tests may assume that the representatives are
#           pairwise non-equivalent
#        invariants: invariants that have been computed for that representation
# - enabledTests: a list of tests that can be used, as passed in construction
# - tests: a list of tests to actually use;  each test has an additional
#          component "rep" that is the representation it is applied against
#
# each test is a record consisting of the following components
# - name: a name identifying the test
# - cost: a function that takes a representation and returns an integer
#      cost of the test.
# - filters: a list of filters that have to return true such that the test can
#       be applied against the representation
# - fun: a function, semantics are determined by the type:
# - type: one of the strings "simple", "invariant", "custom" or "postHook"
#     The first three are used to try to identify the class:
#
#    simple: fun(rep, x, r) returns either a result or fail.
#    invariant: fun(rep, x) returns an invariant.
#    custom: fun(PR, rep, x, r, curr) returns the loop variable curr (see code).
#
#    postHook: fun(rep, x, r) is run after the the main loop finished and can be
#               used for caching, additional cleanup, diagnostics etc.
#               The return value is discarded.
#
#   TODO: adjust signatures of all function types to fun(PR, rep, ElR, x, curr)
#   to make things less confusing?
#
InstallMethod ( PositionClass,
                [ IsObject, IsObject, IsInt ],

function(G, x, maxcost)
    local  PR, curr, r, i, k, t, tmp, xinv, new, val ;

    # counter := counter+1;
    totalcnt := totalcnt +1;

    PR := PositionClassRecord(G);

    if not ( IsBound(PR.tree) and
             IsBound(PR.tests) and
             IsBound(PR.postHooks)) then
        PosClassInitTests(PR);
    fi;

    curr := PR.tree;
    r := [1..Length(PR.representations[1].clreps)];

    while Length(r) > 1 do
        if not IsBound(PR.tests[curr.testNr]) then
            Info(InfoPositionClass, 1,
                 "No test with index ", curr.testNr, " exists. Giving up.");
            break;
        fi;

        t := PR.tests[curr.testNr];
        t.stats.total := t.stats.total + 1;


        Info(InfoPositionClass, 1,
             "PositionClass: Running test ", t.name);

        if t.type = "simple" then
            if not IsBound(curr.nextTest) then
                curr.nextTest := rec ( classes := r,
                                       testNr := curr.testNr + 1 );
            fi;

            tmp := t.fun(t.rep, x^(t.rep.hom), r);
            if tmp = fail then
                curr := curr.nextTest;
                continue;
            else
                t.stats.success := t.stats.success + 1;
                r := [tmp];
                break;
            fi;

        elif t.type = "invariant" then;
            # the test has never been run with this tree before.
            # rebuild the branches using the invariants stored in the
            # representation
            if not ( IsBound(curr.invSet) and IsBound(curr.branches) ) then
                curr.invSet := [];
                curr.branches := [];

                # compute missing invariants
                if not IsBound(t.rep.inv.(t.name)) then
                    t.rep.inv.(t.name) := [];
                fi;

                for i in r do
                    if not IsBound(t.rep.inv.(t.name)[i]) then
                        val := t.fun(t.rep, (t.rep.clreps[i]));
                        t.rep.inv.(t.name)[i] := val;
                    fi;
                od;

                for i in r do
                    tmp := t.rep.inv.(t.name)[i];
                    k := PositionSorted(curr.invSet, tmp);

                    if not IsBound(curr.invSet[k]) then
                        # append to both lists
                        Add(curr.invSet, tmp);
                        Add(curr.branches,
                            rec( classes := [i], testNr := curr.testNr + 1));

                    elif curr.invSet[k] <> tmp then
                        # insert into both lists
                        Add(curr.invSet, tmp, k);
                        Add(curr.branches,
                            rec( classes := [i], testNr := curr.testNr + 1),
                            k);
                    else
                        # insert i at the correct position into the
                        # sorted list of classes in that branch
                        Add(curr.branches[k].classes,
                            i,
                            PositionSorted(curr.branches[k].classes, i));
                    fi;
                od;

                if Length(curr.invSet) = 1 then
                    Info(InfoPositionClass, 1,
                         "PositionClass: Invariant ", t.name,
                         " does not distinguish any classes!");
                    Info(InfoPositionClass, 1,
                         "PositionClass: Removing ", t.name, " from tree.");
                    curr.testNr := curr.testNr + 1;
                    Unbind(curr.invSet);
                    Unbind(curr.branches);
                    continue;
                fi;
            fi;

            xinv := t.fun(t.rep, x^t.rep.hom);

            k := PositionSortedEq(curr.invSet, xinv);

            if k = fail then
                Error("No class has the same invariant ", t.name,
                      " as ", x, "!" );
            else
                r := curr.branches[k].classes;
                Info(InfoPositionClass, 1,
                     "PositionClass: Refined search space to ", r,
                     " using invariant ", t.name, ".");
                curr := curr.branches[k];
            fi;

        elif t.type = "custom" then
            curr := t.fun(PR, t.rep, x^t.rep.hom, r, curr);

        else
            Info(InfoPositionClass, 1,
                 "PositionClass: I have no idea how to handle tests of type ",
                 t.type);
            curr := t;
        fi;
    od;

    for t in PR.postHooks do
        Info(InfoPositionClass, 2, "PositionClass. Running postHook ", t.name );
        t.fun(t.rep, x, r);
    od;

    # if successful, return the result as an integer
    if Length(r) = 1 then
        return r[1];
    fi;

    return r;
end
);

InstallMethod ( PositionClass,
                "no maxcost",
                [ IsObject, IsObject],

function (G, x)
    return PositionClass(G, x, 9223372036854775807);
end);
