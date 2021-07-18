#########################################################################
##
#A  cusppairs.g                                                Jay Taylor
##
##  Distributed under GNU GPLv3.
##
##  This file contains the classification of d-cuspidal unipotent
##  characters for finite reductive groups. It can be used to determine
##  all d-cuspidal pairs. It requires the development version of CHEVIE
##  (compatible with version dated 30/10/2020).
##
##  The stored data consists of rational forms of Levi subgroups that
##  support a d-cuspidal unipotent character. This was computed with
##  CHEVIE using the commands SplitLevis and CuspidalUnipotentCharacters.
##  The stored data consists of a subset of simple roots and the twisting
##  element given as a word in the generators.
##
##  The main functions provided by this file are:
##      - SplitLeviCover
##      - CuspidalLevis
##      - CuspialPairs
##      - JordanCuspidalLevis
##      - JordanCuspidalPairs
##  Each of these functions takes as input a CoxeterCoset and optionally
##  an integer specifying which e-Harish-Chandra series one wants to
##  consider. If the integer is ommited then it is assumed that e=1.
##
##  Some additional functions are provided at the end for automatically
##  producing LaTeX tables of the output of these functions. We just give
##  a few examples of the use of the above functions:
##
##      gap> GF := CoxeterCoset(CoxeterGroup("E",8), ());;
##      gap> J := [1,2,3,4,5,6,8,119];;
##      gap> Hphi := CoxeterSubCoset(Group(GF), J, ());;
##      E6xA2<8,119>
##      gap> L := SplitLevis(Hphi,4);
##      [ E6xA2<8,119>, 2A3<2,4,3>xA2<8,119>.(q-1)(q^2+1),
##          A2<8,119>.(q-1)^2(q^2+1)^2 ]
##      gap> List(L, R -> SplitLeviCover(R,4));
##      [ E8, 2D6<2,3,4,21,8,97>.(q^2+1),
##          D4<7,61,8,97>.(q^2+1)^2 ]
##      gap> CuspidalLevis(Hphi,3);
##      [ E6.(q^2+q+1), 3D4<2,3,4,5>.(q^2+q+1)^2, (q^2+q+1)^4 ]
##
##      Cuspidal pairs returns a list of pairs. The first item in
##      the pair is the CoxeterCoset corresponding to a rational
##      Levi subgroup. The second item is a list giving the indices
##      of the cuspidal characters as obtained from UnipotentCharacters.
##
##      gap> CuspidalPairs(Hphi,3);
##      [ [ E6.(q^2+q+1), [ 19, 24, 25 ] ],
##          [ 3D4<2,3,4,5>.(q^2+q+1)^2, [ 8 ] ],
##          [ (q^2+q+1)^4, [ 1 ] ] ]
##
##      JordanCuspidalLevis and JordanCuspidalPairs behave in the same
##      way, except now the first entry is the smallest split Levi
##      subgroup of the parent of the input containing the Levi of the sub.
##
##      gap> H := ReflectionSubgroup(Group(GF), J);;
##      gap> w := LongestCoxeterElement(H)*LongestCoxeterElement(Group(GF));
##      gap> Hphi := CoxeterSubCoset(GF,J,w);
##      2E6x2A2<8,119>
##      gap> JordanCuspidalLevis(Hphi);
##      [ [ E8, 2E6x2A2<8,119> ],
##        [ E7<1,2,3,4,5,6,15>.(q-1), 2E6.(q-1)(q+1) ],
##        [ E7<8,1,34,3,4,5,6>.(q-1), 2A5<1,3,4,5,6>x2A2<8,119>.(q-1) ],
##        [ D6<1,42,3,4,5,6>.(q-1)^2, 2A5<1,3,4,5,6>.(q-1)^2(q+1) ],
##        [ D4<59,58,8,61>.(q-1)^4, 2A2<8,119>.(q-1)^4(q+1)^2 ],
##        [ A1<65>xA1<67>xA1<68>.(q-1)^5, (q-1)^5(q+1)^3 ] ]


##############################################################
##############################################################
##                                                          ##
##                          Data                            ##
##                                                          ##

# Some of the following functions are adapted from Jean Michel's CHEVIE
# library functions on unipotent characters.

CHEVIE.AddData("CuspidalLevis", "A", function(n, e)
    local a, rks;
    a := QuoInt(n+1, e);
    rks := Filtered([0..a], function(k)
        local B, p;
        for p in Partitions(n+1-k*e) do
            B := BetaSet(p);
            B := PositionProperty(B, k -> (k >= e) and (not k-e in B));
            if B = false then
                return true;
            fi;
        od;
        return false;
    end);
    return List(rks, k -> [[1..n-k*e],
            Filtered([n+1-k*e..n], i -> RemInt(n+1-i,e) <> 0)]);
end);

CHEVIE.AddData("CuspidalLevis", "2A", function(n, e)
    local d;

    if e mod 4 in [1,3] then
        d := 2*e;
    elif e mod 4 = 2 then
        d := e/2;
    else
        d := e;
    fi;

    return CHEVIE.A.CuspidalLevis(n, d);
end);

CHEVIE.AddData("CuspidalLevis", "B", function(n, e)
    local a, f, s, w, rks;

    if e mod 2 = 1 then
        f := e;
        s := ();
    else
        f := e/2;
        s := (1,2);
    fi;

    a := QuoInt(n, f);
    rks := Filtered([0..a], function(k)
        local S, d, r, p;
        r := n-k*f;
        for d in 1 + 2*[0..QuoInt((-1+RootInt((1+4*r), 2)), 2)] do
            for S in Symbols(r, d) do
                p := List([1,2], i -> PositionProperty(S[i],
                     k -> (k >= f) and (not k-f in S[i^s])));
                if (p[1] = false) and (p[2] = false) then
                    return true;
                fi;
            od;
        od;
        return false;
    end);

    w := function(a,b) return Concatenation(Reversed([2..a]), [1..b]); end;

    if e mod 2 = 1 then
        return List(rks, k -> [[1..n-k*f],
                Filtered([n+1-k*f..n], i -> RemInt(n+1-i,f) <> 0)]);
    else
        return List(rks, k -> [[1..n-k*f],
            Flat(List([0..k-1], i -> w(n+(i-k)*f+1, n+(i-k+1)*f)))]);
    fi;
end);

CHEVIE.AddData("CuspidalLevis", "D", function(n, e)
    local a, f, s, w, rks;

    if e mod 2 = 1 then
        f := e;
        s := ();
    else
        f := e/2;
        s := (1,2);
    fi;

    a := QuoInt(n, f);
    rks := Filtered([0..a], function(k)
        local S, d, r, p;
        r := n-k*f;
        # Special cases.
        if r = 0 then
            if e mod 2 = 0 and k mod 2 = 1 then
                return false;
            fi;
            return true;
        fi;
        if e mod 2 = 0 and k mod 2 = 1 then
            for d in 4*[0..QuoInt((RootInt(r)-1),2)]+2 do
                for S in Symbols(r, d) do
                    p := List([1,2], i -> PositionProperty(S[i],
                         k -> (k >= f) and (not k-f in S[i^s])));
                    if (p[1] = false) and (p[2] = false) then
                        return true;
                    fi;
                od;
            od;
        else
            for S in Symbols(r, 0) do
                if IsList(S[2]) then
                    p := List([1,2], i -> PositionProperty(S[i],
                         k -> (k >= f) and (not k-f in S[i^s])));
                else
                    p := [PositionProperty(S[1],
                         k -> (k >= f) and (not k-f in S[1])), false];
                fi;
                if (p[1] = false) and (p[2] = false) then
                    return true;
                fi;
            od;
            for d in 4*[1..RootInt(QuoInt(r,4), 2)] do
                for S in Symbols(r, d) do
                    p := List([1,2], i -> PositionProperty(S[i],
                         k -> (k >= f) and (not k-f in S[i^s])));
                    if (p[1] = false) and (p[2] = false) then
                        return true;
                    fi;
                od;
            od;
        fi;
        return false;
    end);

    w := function(a,b) return Concatenation(Reversed([1..a]), [3..b]); end;

    if e mod 2 = 1 then
        return List(rks, function(k)
            # Special treatment for A1 case. Element doesn't normalise.
            if n = k*f+1 then
                return [[], Filtered([2..n], i -> RemInt(n+1-i,f) <> 0)];
            else
                return [[1..n-k*f],
                    Filtered([n+1-k*f..n], i -> RemInt(n+1-i,f) <> 0)];
            fi;
        end);
    else
        return List(rks, function(k)
            if f = 1 and k = n then
                return [[], Concatenation([1],
                    Flat(List([0..k-1], i -> w(n+(i-k)+1, n+(i-k+1)))))];
            elif n = k*f+1 then
                return [[],
                    Flat(List([0..k-1], i -> w(n+(i-k)*f+1, n+(i-k+1)*f)))];
            else
                return [[1..n-k*f],
                    Flat(List([0..k-1], i -> w(n+(i-k)*f+1, n+(i-k+1)*f)))];
            fi;
        end);
    fi;
end);

CHEVIE.AddData("CuspidalLevis", "2D", function(n, e)
    local a, f, s, w, rks;

    if e mod 2 = 1 then
        f := e;
        s := ();
    else
        f := e/2;
        s := (1,2);
    fi;

    a := QuoInt(n, f);
    rks := Filtered([0..a], function(k)
        local S, d, r, p;
        r := n-k*f;
        if e mod 2 = 0 and k mod 2 = 1 then
            if r = 0 then
                # Special cases.
                if e mod 2 = 0 and k mod 2 = 0 then
                    return false;
                fi;
                return true;
            fi;
            for S in Symbols(r, 0) do
                if IsList(S[2]) then
                    p := List([1,2], i -> PositionProperty(S[i],
                         k -> (k >= f) and (not k-f in S[i^s])));
                else
                    p := [PositionProperty(S[1],
                         k -> (k >= f) and (not k-f in S[1])), false];
                fi;
                if (p[1] = false) and (p[2] = false) then
                    return true;
                fi;
            od;
            for d in 4*[1..RootInt(QuoInt(r,4), 2)] do
                for S in Symbols(r, d) do
                    p := List([1,2], i -> PositionProperty(S[i],
                         k -> (k >= f) and (not k-f in S[i^s])));
                    if (p[1] = false) and (p[2] = false) then
                        return true;
                    fi;
                od;
            od;
        else
            for d in 4*[0..QuoInt((RootInt(r)-1),2)]+2 do
                for S in Symbols(r, d) do
                    p := List([1,2], i -> PositionProperty(S[i],
                         k -> (k >= f) and (not k-f in S[i^s])));
                    if (p[1] = false) and (p[2] = false) then
                        return true;
                    fi;
                od;
            od;
        fi;
        return false;
    end);

    w := function(a,b) return Concatenation(Reversed([1..a]), [3..b]); end;

    if e mod 2 = 1 then
        return List(rks, function(k)
            # Special treatment for A1 case. Element doesn't normalise.
            if n = k*f+1 then
                return [[], Filtered([2..n], i -> RemInt(n+1-i,f) <> 0)];
            else
                return [[1..n-k*f],
                    Filtered([n+1-k*f..n], i -> RemInt(n+1-i,f) <> 0)];
            fi;
        end);
    else
        return List(rks, function(k)
            if f = 1 and k = n then
                return [[], Concatenation([1],
                    Flat(List([0..k-1], i -> w(n+(i-k)+1, n+(i-k+1)))))];
            elif n = k*f+1 then
                return [[],
                    Flat(List([0..k-1], i -> w(n+(i-k)*f+1, n+(i-k+1)*f)))];
            else
                return [[1..n-k*f],
                    Flat(List([0..k-1], i -> w(n+(i-k)*f+1, n+(i-k+1)*f)))];
            fi;
        end);
    fi;
end);

CHEVIE.AddData("tblcusplev", "G2", 
[   # e = 1
    [ [[1,2],[]], [[],[]] ],
    # e = 2
    [ [[1,2],[]], [[],[1,2,1,2,1,2]] ],
    # e = 3
    [ [[1,2],[]], [[],[1,2,1,2]] ],,,
    # e = 6
    [ [[1,2],[]], [[],[1,2]] ]
]);

CHEVIE.AddData("tblcusplev", "F4", 
[   # e = 1
    [   [[1,2,3,4],[]],
        [[2,3],[]],
        [[],[]]
    ],
    # e = 2 
    [   [[1,2,3,4],[]],
        [[3,2],[1,2,3,2,1,4,3,2,1,3,2,3,4,3,2,1,3,2,3,4]],
        [[],[1,2,1,3,2,1,3,2,3,4,3,2,1,3,2,3,4,3,2,1,3,2,3,4]]
    ],
    # e = 3
    [   [[1,2,3,4],[]],
        [[],[1,2,1,3,2,1,3,4,3,2,1,3,2,3,4,3]]
    ],
    # e = 4
    [   [[1,2,3,4],[]],
        [[3,2],[4,3,2,1,3,2,4,3,2,1]],
        [[],[1,2,1,3,2,1,3,4,3,2,3,4]]
    ],,
    # e = 6
    [   [[1,2,3,4],[]],
        [[],[1,2,1,3,2,3,4,3]]
    ],,
    # e = 8
    [   [[1,2,3,4],[]],
        [[],[1,2,3,2,4,3]]
    ],,,,
    # e = 12 
    [   [[1,2,3,4],[]],
        [[],[1,2,3,4]]
    ]
]);

CHEVIE.AddData("tblcusplev", "3D4", 
[   # e = 1
    [ [[1,2,3,4],[]], [[],[]] ],
    # e = 2
    [ [[1,2,3,4],[]], [[],[1,2,3,1,2,3]] ],
    # e = 3
    [ [[1,2,3,4],[]], [[],[1,2,3,1,2,4,3,2]] ],
    # e = 4
    [ [[1,2,3,4],[]] ],,
    # e = 6
    [ [[1,2,3,4],[]], [[],[1,2,3,2]] ]
]);

CHEVIE.AddData("tblcusplev", "E6", 
[   # e = 1
    [   [[1,2,3,4,5,6],[]], [[2,3,4,5],[]], [[],[]] ],
    # e = 2
    [   [[1,2,3,4,5,6],[]],
        [[6,5,4,3,1],[2,4,3,1,5,4,2,3,4,5,6,5,4,2,3,1,4,3,5,4,2]],
        [[],[2,3,4,2,3,4,5,4,2,3,4,5]]
    ],
    # e = 3
    [   [[1,2,3,4,5,6],[]],
        [[4,3,2,5],[6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1]],
        [[],[1,3,1,4,2,3,1,4,5,4,2,3,1,4,3,5,6,5,4,2,3,4,5,6]]
    ],
    # e = 4
    [   [[1,2,3,4,5,6],[]],
        [[4,3,2],[5,4,2,3,4,5,6]],
        [[],[3,4,2,3,4,5]]
    ],
    # e = 5
    [   [[1,2,3,4,5,6],[]],
        [[6],[1,4,2,3]]
    ],
    # e = 6
    [   [[1,2,3,4,5,6],[]],
        [[],[1,2,3,1,5,4,6,5,4,2,3,4]]
    ],,
    # e = 8
    [   [[1,2,3,4,5,6],[]],
        [[],[1,3,4,2,5]]
    ],
    # e = 9
    [   [[1,2,3,4,5,6],[]],
        [[],[1,3,4,2,3,4,5,6]]
    ],,,
    # e = 12
    [   [[1,2,3,4,5,6],[]],
        [[],[1,4,2,3,6,5]]
    ]
]);

CHEVIE.AddData("tblcusplev", "2E6", 
[   # e = 1
    [   [[1,2,3,4,5,6],[]],
        [[1,3,4,5,6],[]],
        [[],[]]
    ],
    # e = 2
    [   [[1,2,3,4,5,6],[]],
        [[4,3,2,5],[1,3,4,2,5,4,3,1,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1]],
        [[],[1,2,3,1,4,2,3,1,4,3,5,4,2,3,1,4,3,5,4,2,6,5,4,2,3,1,4,3,5,
            4,2,6,5,4,3,1]]
    ],
    # e = 3
    [   [[1,2,3,4,5,6],[]],
        [[],[4,2,5,4,2,3,4,5,6,5,4,2,3,4,5,6]]
    ],
    # e = 4
    [   [[1,2,3,4,5,6],[]],
        [[6,5,4],[1,3,4,2,5,4,3,1,6,5,4,2,3,4,5]],
        [[],[1,4,2,3,1,4,3,5,4,2,3,1,4,6,5,4,3,1]]
    ],
    # e = 5
    [ [[1,2,3,4,5,6],[]] ],
    # e = 6
    [   [[1,2,3,4,5,6],[]],
        [[2,3,4,5],[6,5,4,2,3,4,5,6]],
        [[],[1,2,4,3,1,5,4,3,6,5,4,3]]
    ],,
    # e = 8
    [ [[1,2,3,4,5,6],[]], [[],[2,5,4]] ],
    # e = 9
    [ [[1,2,3,4,5,6],[]] ],,,
    # e = 12
    [ [[1,2,3,4,5,6],[]], [[],[1,2,3,1,4,3]] ]
]);

CHEVIE.AddData("tblcusplev", "E7", 
[   # e = 1
    [   [[1,2,3,4,5,6,7],[]],
        [[1,2,3,4,5,6],[]],
        [[2,3,4,5],[]],
        [[],[]]
    ],
    # e = 2
    [   [[1,2,3,4,5,6,7],[]],
        [[2,4,3,5,1,6],[7,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,7,6,5,4,2,3,
            4,5,6,7]],
        [[4,5,2,3],[1,3,4,2,5,4,3,1,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,7,
            6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,7,6,5,4,2,3,4,5,6,7]],
        [[],[1,2,3,1,4,2,3,1,4,3,5,4,2,3,1,4,3,5,4,2,6,5,4,2,3,1,4,3,5,
            4,2,6,5,4,3,1,7,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,7,6,5,4,2,
            3,4,5,6,7]]
    ],
    # e = 3
    [   [[1,2,3,4,5,6,7],[]],
        [[7,4,6,5,2],[1,3,4,2,5,4,3,1,6,5,4,2,3,4,5,6,7,6,5,4,2,3,1,4,3,
            5,4,2,6,5,4,3]],
        [[4,3,2,5],[7,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,7]],
        [[],[4,3,5,4,2,3,4,5,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1]]
    ],
    # e = 4
    [   [[1,2,3,4,5,6,7],[]],
        [[2,5,7],[1,4,2,5,4,3,6,5,4,2,3,4,5,6,7,6,5,4,2,3,1,4,3,5,4,2,6,
            5,4,3]]
    ],
    # e = 5
    [   [[1,2,3,4,5,6,7],[]],
        [[6,7],[2,4,3,1]]
    ],
    # e = 6
    [   [[1,2,3,4,5,6,7],[]],
        [[4,6,5,2,7],[3,4,2,5,4,3,6,5,4,2,7,6,5,4,3,1]],
        [[4,3,2,5],[1,3,4,2,5,4,3,1,7,6,5,4,2,3,4,5,6]],
        [[],[5,4,3,6,5,4,2,3,4,7,6,5,4,2,3,1,4,3,5,4,2]]
    ],
    # e = 7
    [   [[1,2,3,4,5,6,7],[]],
        [[],[7,6,5,4,3,1]]
    ],
    # e = 8
    [   [[1,2,3,4,5,6,7],[]],
        [[7,5,2],[3,4,2,3,4,5,4,2,3,1,4,3,6,5,4,2,3,4,5,6,7,6,5,4,2,3,
            1,4,3,5,4,2,6,5,4,3,1]]
    ],
    # e = 9
    [   [[1,2,3,4,5,6,7],[]],
        [[],[4,2,6,5,4,2,3,1]]
    ],
    # e = 10
    [   [[1,2,3,4,5,6,7],[]],
        [[3,4],[2,4,3,1,5,4,2,3,4,5,6,7]]
    ],,
    # e = 12
    [   [[1,2,3,4,5,6,7],[]],
        [[2,5,7],[3,1,4,2,5,4,3,1,6,5,4,2,3,1,4,3,5,4,6,5,7,6,5,4,2,3,
            1,4,3,5,4,2,6,5,4,3,1,7,6,5,4,3]]
    ],,
    # e = 14
    [   [[1,2,3,4,5,6,7],[]],
        [[],[4,2,7,6,5,4,2,3,1]]
    ],,,,
    # e = 18
    [   [[1,2,3,4,5,6,7],[]],
        [[],[7,6,5,4,2,3,1]]
    ]
]);

CHEVIE.AddData("tblcusplev", "E8",
[   # e = 1
    [   [[1,2,3,4,5,6,7,8],[]],
        [[1,2,3,4,5,6,7],[]],
        [[1,2,3,4,5,6],[]],
        [[2,3,4,5],[]],
        [[],[]]
    ],
    # e = 2
    [   [[1,2,3,4,5,6,7,8],[]],
        [[7,5,4,3,1,6,2],[8,7,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,7,6,5,4,
            2,3,4,5,6,7,8,7,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,7,6,5,4,2,
            3,4,5,6,7,8]],
        [[3,4,2,6,1,5],[7,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,7,6,5,4,2,3,
            4,5,6,7,8,7,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,7,6,5,4,2,3,4,
            5,6,7,8,7,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,7,6,5,4,2,3,4,5,
            6,7,8]],
        [[3,4,2,5],[1,3,4,2,5,4,3,1,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,7,
            6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,7,6,5,4,2,3,4,5,6,7,8,7,6,
            5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,7,6,5,4,2,3,4,5,6,7,8,7,6,5,
            4,2,3,1,4,3,5,4,2,6,5,4,3,1,7,6,5,4,2,3,4,5,6,7,8]],
        [[],[1,2,3,1,4,2,3,1,4,3,5,4,2,3,1,4,3,5,4,2,6,5,4,2,3,1,4,3,
            5,4,2,6,5,4,3,1,7,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,7,6,5,4,
            2,3,4,5,6,7,8,7,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,7,6,5,4,2,
            3,4,5,6,7,8,7,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,7,6,5,4,2,3,
            4,5,6,7,8]]
    ],
    # e = 3
    [   [[1,2,3,4,5,6,7,8],[]],
        [[1,5,3,4,2,6],[8,7,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,7,6,5,4,2,
            3,4,5,6,7,8,7,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,7,6,5,4,2,3,
            4,5,6,7]],
        [[3,4,2,5],[6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,8,7,6,5,4,2,3,1,4,
            3,5,4,2,6,5,4,3,1,7,6,5,4,2,3,4,5,6,7,8,7,6,5,4,2,3,1,4,3,
            5,4,2,6,5,4,3,1,7,6,5,4,2,3,4,5,6,7]],
        [[],[1,2,3,1,4,2,3,1,4,5,4,2,3,1,4,3,5,6,5,4,2,3,1,4,3,5,4,2,
            6,7,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,7,8,7,6,5,4,2,3,1,4,3,
            5,4,2,6,5,4,3,1,7,6,5,4,2,3,4,5,6,7,8,7,6,5,4]]
    ],
    # e = 4
    [   [[1,2,3,4,5,6,7,8],[]],
        [[3,4,2,5],[1,3,4,2,5,4,3,1,6,5,4,2,3,4,5,6,7,6,5,4,2,3,1,4,3,
            5,4,2,6,5,4,3,1,7,6,5,4,2,3,4,5,6,8,7,6,5,4,2,3,4,5,6,7,8]],
        [[],[1,2,3,1,4,2,3,1,4,3,5,4,2,3,4,5,6,5,4,2,3,1,4,3,5,4,2,7,6,
            5,4,2,3,1,4,3,5,4,6,5,7,6,8,7,6,5,4,2,3,1,4,3,5,4,6,5,7,6,
            8,7]]
    ],
    # e = 5
    [   [[1,2,3,4,5,6,7,8],[]],
        [[1,3,4,2],[7,6,8,7,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,7,6,5,4,2,
            3,4,5,6,7,8,7,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,7,6,5,4,2,3,
            4,5,6,7]],
        [[],[1,2,3,1,4,2,3,1,4,5,4,2,3,1,4,5,6,5,4,2,3,1,4,5,6,7,6,5,4,
            2,3,1,4,5,6,7,8,7,6,5,4,2,3,4,5,6,7,8]]
    ],
    # e = 6
    [   [[1,2,3,4,5,6,7,8],[]],
        [[1,2,3,4,5,6],[7,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,7,6,5,4,2,3,
            4,5,6,7,8]],
        [[2,3,4,5],[1,3,4,2,5,4,3,1,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,7,
            6,5,4,2,3,4,5,6,7,8,7]],
        [[],[1,2,3,1,4,2,3,1,4,5,4,2,3,1,4,5,6,5,4,2,3,1,4,5,6,7,6,5,4,
            2,3,4,5,6,7,8,7,6,5,4]]
    ],
    # e = 7
    [   [[1,2,3,4,5,6,7,8],[]],
        [[1],[2,5,4,6,8,7]]
    ],
    # e = 8
    [   [[1,2,3,4,5,6,7,8],[]],
        [[4,2,3,5],[1,3,4,2,5,4,3,1,6,5,4,2,3,4,5,6,7,8,7,6,5,4,2,3,1,4,
            3,5,4,2,6,5,4,3,1,7,6,5,4,2,3,4,5,6,7,8,7]],
        [[],[1,2,3,1,4,2,3,1,4,5,4,2,3,1,4,5,6,5,4,2,3,4,5,6,7,6,5,8,7,6]]
    ],
    # e = 9
    [   [[1,2,3,4,5,6,7,8],[]],
        [[1,3],[2,4,3,1,6,5,4,2,3,4,5,7,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,
            1,7,6,5,4,2,3,4,5,6,7,8,7,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,
            7,6,5,4,2,3,4,5,6,7,8,7,6,5,4,2,3,1,4,3,5,4,2,6,5,7]]
    ],
    # e = 10
    [   [[1,2,3,4,5,6,7,8],[]],
        [[3,4,5,6],[2,4,3,5,4,2,6,5,4,3,1,7,6,5,4,2,3,4,5,6,7,8]],
        [[],[1,2,3,1,4,2,3,1,4,5,4,2,3,4,5,6,5,4,7,6,5,8,7,6]]
    ],,
    # e = 12
    [   [[1,2,3,4,5,6,7,8],[]],
        [[2,3,4,5],[1,3,4,2,5,4,3,1,6,5,4,2,3,4,5,6,7,8]],
        [[],[2,3,1,4,2,3,1,4,5,4,2,3,4,5,6,5,7,6,8,7]]
    ],,
    # e = 14
    [   [[1,2,3,4,5,6,7,8],[]],
        [[4],[3,4,2,5,4,3,1,6,5,4,2,3,4,5,6,7,8]]
    ],
    # e = 15
    [   [[1,2,3,4,5,6,7,8],[]],
        [[],[1,2,3,1,4,2,3,4,5,4,6,5,7,6,8,7]]
    ],,,
    # e = 18
    [   [[1,2,3,4,5,6,7,8],[]],
        [[3,4],[2,4,3,1,5,4,2,3,4,5,6,7,8]]
    ],,
    # e = 20
    [   [[1,2,3,4,5,6,7,8],[]],
        [[],[4,3,1,5,4,2,3,4,5,6,7,8]]
    ],,,,
    # e = 24
    [   [[1,2,3,4,5,6,7,8],[]],
        [[],[3,1,4,2,3,4,5,6,7,8]]
    ],,,,,,
    # e = 30
    [   [[1,2,3,4,5,6,7,8],[]],
        [[],[1,2,3,4,5,6,7,8]]
    ]
]);

CHEVIE.IndirectAddData2 := function(f, types, fun)
    local t;
    for t in types do
        CHEVIE.AddData(f, t[1], fun(t));
    od;
end;

CHEVIE.IndirectAddData2("CuspidalLevis", [["G2",2], ["F4",4], ["3D4",4],
    ["E6",6], ["E7",7], ["E8",8], ["2E6",6]],
    t -> function(e)
        local data;
        data := CHEVIE.R("tblcusplev", t[1]);
        if IsBound(data[e]) then
            return data[e];
        fi;
        return [[[1..t[2]], []]];
end);


##############################################################
##############################################################
##                                                          ##
##                     Main Functions                       ##
##                                                          ##

##########################################################################
##
#F SplitLeviCover( GF [, e] ) . . . . smallest e-split Levi containing GF.
##
##  Here GF is a CoxeterCoset and e > 0 is a positive integer. If e is
##  ommited then the default is that e = 1.
##
##  This returns the smallest e-split Levi subgroup of the parent of GF
##  that contains GF.
SplitLeviCover := function(arg)
    local L, LF, G, GF, d, J, pr, V, inds;

    LF := arg[1];
    if Length(arg) = 2 then
        d := arg[2];
    else
        d := 1;
    fi;

    L := Group(LF);
    GF := LF.parent;
    G := Group(GF);
    J := InclusionGens(L);

    # Matrix of phi acting on the roots.
    pr := EigenspaceProjector(LF, LF.phi, d);
    V := VectorSpace(List(G.roots{J}, r -> r*pr), Cyclotomics, 0*G.roots[1]);
    inds := Filtered([1..Length(G.roots)], i -> G.roots[i]*pr in V);

    return CoxeterSubCoset(GF, inds, LF.phi*GF.phi^-1);
end;

##########################################################################
##
#F CuspidalLevis( GF [, e] ) . . Levis of GF with an e-cuspidal unip char.
##
##  Here GF is a CoxeterCoset and e > 0 is a positive integer. If e is
##  ommited then the default is that e = 1.
##
##  This returns a list of all the Levis of GF, as instances of sub cosets,
##  that support a cuspidal unipotent character.
CuspidalLevis := function(arg)
    local phi, GF, t, e, inc, res;

    GF := arg[1];
    phi := GF.phi;
    if Length(arg) > 1 then
        e := arg[2];
    else
        e := 1;
    fi;

    inc := Group(GF).rootInclusion;
    res := List(ReflectionType(GF), function(t)
        local o, r, d, I, w0, m;
        o := t.orbit[1];
        r := Length(t.orbit);
        I := o.indices;
        d := QuoInt(e, GcdInt(r,e));
        if o.series = "A" and OrderPerm(t.twist) = 2 then
            w0 := LongestCoxeterElement(Group(GF), inc{I});
        else
            w0 := ();
        fi;
        return List(CHEVIE.Data("CuspidalLevis", t, d), function(T)
            local w, J;
            w := EltWord(Group(GF), inc{I{T[2]}})*w0;
            J := List([0..Length(t.orbit)-1], i -> phi^i);
            return [Concatenation(List(J, p -> List(inc{I{T[1]}}, x -> x^p))),
                w^(J[Length(t.orbit)])];
         end);
    end);

    return List(Cartesian(res), function(R)
        local I, w;
        if R = [] then
            I := [];
            w := ();
        else
            I := Concatenation(List(R, r -> r[1]));
            w := Product(List(R, r -> r[2]));
        fi;
        return CoxeterSubCoset(GF, I, w);
    end);
end;

##########################################################################
##
#F CuspidalPairs( GF [, e] ) . . . . . . . cuspidal unipotent pairs of GF.
##
##  Here GF is a CoxeterCoset and e > 0 is a positive integer. If e is
##  ommited then the default is that e = 1.
##
##  This returns a list of pairs. The first item in a pair gives a Levi of
##  GF as a sub coset. The second item in the pair is a list of indices of
##  e-cuspidal unipotent characters. The indices correspond to the list
##  obtained from calling UnipotentCharacters on the Levis.
CuspidalPairs := function(arg)
    local e, GF;
    GF := arg[1];
    if Length(arg) > 1 then
        e := arg[2];
    else
        e := 1;
    fi;
    return List(CuspidalLevis(GF,e),
        R -> [R, CuspidalUnipotentCharacters(R,e)]);
end;

##########################################################################
##
#F JordanCuspidalLevis( GF [, e] )
##
##  Here GF is a CoxeterCoset and e > 0 is a positive integer. If e is
##  ommited then the default is that e = 1.
##
##  This returns a list of pairs. The second item in the pair is an e-split
##  Levi subgorup of GF that supports an e-cuspidal unipotent character.
##  The first item in the pair is the smallest e-split Levi of the parent of
##  GF that contains GF.
JordanCuspidalLevis := function(arg)
    local e, GF;
    GF := arg[1];
    if Length(arg) > 1 then
        e := arg[2];
    else
        e := 1;
    fi;
    return List(CuspidalLevis(GF,e), R -> [SplitLeviCover(R,e), R]);
end;

# See CuspidalPairs and JordanCuspialLevis.
JordanCuspidalPairs := function(arg)
    local e, GF;
    GF := arg[1];
    if Length(arg) > 1 then
        e := arg[2];
    else
        e := 1;
    fi;
    return List(CuspidalLevis(GF,e),
        R -> [SplitLeviCover(R,e), R, CuspidalUnipotentCharacters(R,e)]);
end;

##############################################################
##############################################################
##                                                          ##
##                      For Printing                        ##
##                                                          ##

PPReflectionName := function(t)
    local res, l, r, i;
    res := "";
    if IsBound(t.orbit) then
        if OrderPerm(t.twist) <> 1 then
            Append(res, "{}^");
            Append(res, String(OrderPerm(t.twist)));
        fi;
        l := Length(t.orbit);
        r := t.orbit[1];
    else
        l := 1;
        r := t;
    fi;

    if IsBound(r.cartanType) then
        if r.cartanType = 1 then
            Append(res, "\\C");
        else
            Append(res, "\\B");
        fi;
    else
        Append(res, SPrint("\\", r.series));
    fi;
    Append(res, SPrint("_", Length(r.indices)));

    if l = 1 then
        Append(res, "(q)");
    else
        Append(res, SPrint("(q^", l, ")"));
    fi;
    return String(res);
end;

PPCoset := function(GF)
    local t, i, l, res;
    t := ReflectionType(GF); 
    res := Collected(List(t, R -> PPReflectionName(R)));
    res := List(res, function(r)
        if r[2] > 1 then
            return SPrint(r[1], "^", r[2]);
        else
            return r[1];
        fi; end);
    res := Join(res, ".");
    if IsSpets(GF) then
        if Group(GF).rank - Group(GF).semisimpleRank > 0 then
            if Length(res) > 0 then
                Append(res, ".");
            fi;
            l := CycPol(Concatenation([1,0],
                 List(Filtered(ReflectionDegrees(GF), function(x)
                          return x[1] = 1; end), function(x)
                        return AsRootOfUnity(x[2]);
                    end)));
            Append(res, String(FormatLaTeX(l)));
        fi;
    fi;
    return String(res);
end;

PrintTableCuspidalData := function(L, D)
    local c, e, i, file, J, R, T;

    file := "./Tables/tabdata.tex";
    AppendTo(file, "\\begin{longtable}{*{2}{>{$}c<{$}}*{4}{>{$}l<{$}}}\n");
    AppendTo(file, "\\toprule\n");
    AppendTo(file, Join(["\\multicolumn{1}{c}{No.}", "e\n",  
            "\\multicolumn{1}{c}{$C_{\\bG}^{\\circ}(s)^{nF}$}\n",
            "\\multicolumn{1}{c}{$\\bL^{nF}$}\n",
            "\\multicolumn{1}{c}{$C_{\\bL}^{\\circ}(s)^{nF}$}\n",
            "\\multicolumn{1}{c}{$\\lambda$}"], " & "));
    AppendTo(file, "\\\\\n\\midrule\n\\endhead\n\\bottomrule\n\\endfoot\n");

    for e in [1..Length(D)] do
        c := 1;
        for i in [1..Length(L)] do
            R := L[i];
            J := JordanCuspidalPairs(R, D[e]);
            AppendTo(file, Join([String(c), String(D[e]), PPCoset(R),
                PPCoset(J[1][1]), PPCoset(J[1][2]),
                String(Length(J[1][3]))], " & "));
            AppendTo(file, "\\\\\n");
            c := c+1;

            for T in J{[2..Length(J)]} do
                AppendTo(file, Join([String(c), String(D[e]), "",
                    PPCoset(T[1]), PPCoset(T[2]),
                    String(Length(T[3]))], " & "));
                AppendTo(file, "\\\\\n");
                c := c+1;
            od;
        od;
        if e < Length(D) then
            AppendTo(file, "\\midrule\n");
        fi;
    od;
    AppendTo(file, "\\end{longtable}\n");

    return true;

end;






