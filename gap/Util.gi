InstallGlobalFunction( "PositionSortedEq",
    function(hay, needle)
        local k;

        k := PositionSorted(hay, needle);

        # these two if clauses cannot be combined because gap
        # tries to access hay[k] anyway.
        if not IsBound(hay[k]) then
            return fail;
        elif hay[k] <> needle then
            return fail;
        else
            return k;
        fi;
    end
    );
