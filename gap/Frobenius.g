 ########################################################################
##
#A  frobenius3.g                                             Meinolf Geck
##
#Y  Copyright (C) 2019     Lehrstuhl fuer Algebra, Universitaet Stuttgart
##
##  This file  provides functions for computing  maximal vectors, minimal
##  polynomials,  and the  rational canonical form  (or  Frobenius normal
##  form)  of a matrix over any field that is available in  GAP.
##  The algorithms are based on, and a combination of:
##
##  K. Bongartz,  A direct approach to the rational normal form, preprint
##                                          available at arXiv:1410.1683.
##
##  M. Neunhoeffer and  C. E. Praeger,  Computing minimal polynomials  of
##                     matrices, LMS J. Comput. Math. 11 (2008), 252-279;
##
##  M. Geck,  On Jacob's construction  of  the  rational  canonical form,
##                        Electron. J. Linear Algebra 36 (2020), 177-182.
##
##########################################################################
##  The programs work both in GAP3 and GAP4, but need some fixes.
##########################################################################
if IsBound(VERSION)=false then
  VERSION:=['4'];
fi;
if VERSION[1]='4' then
  IsMat:=Ignore;
  x:=Indeterminate(Rationals,"x");
  myPolynomial:=UnivariatePolynomial;
  myCoeffsPol:=CoefficientsOfUnivariatePolynomial;
  LoadPackage("cvec");
else
  x:=X(Rationals);x.name:="x";
  myPolynomial:=Polynomial;
  myCoeffsPol:=function(f)
    local c,i;
    c:=(0*f.coefficients[1])*[1..f.valuation];
    Append(c,f.coefficients);
    return c;
  end;
  CMat:=function(f) return f;end;
fi;
if not IsBound(ImmutableVector) then
  ImmutableVector:=function(k,v) return v;end;
fi;
if not IsBound(ImmutableMatrix) then
  ImmutableMatrix:=function(k,v) return v;end;
fi;
if not IsBound(DefaultFieldOfMatrix) then
  DefaultFieldOfMatrix:=function(mat)
    local i,l;
    l:=Set(mat[1]);
    for i in [2..Length(mat)] do
      Append(l,mat[i]);
      l:=Set(l);
    od;
    return DefaultField(l);
  end;
fi;
if not IsBound(AddRowVector) then
  AddRowVector:=function(dst,src,mul)
    if mul<>0*mul then
      for i in [1..Length(dst)] do
        dst[i]:=dst[i]+mul*src[i];
      od;
    fi;
  end;
fi;
if not IsBound(IsDiagonalMat) then
  IsDiagonalMat:=function(M)
    local i,j;
    if Length(M)=0  then
      return true;
    fi;
    for i in [1..Length(M)] do
      for j in [1..Length(M[1])] do
        if i<>j and M[i][j]<>0*M[i][j] then
          return false;
        fi;
      od;
    od;
    return true;
  end;
fi;
if not IsBound(IsLowerTriangularMat) then
  IsLowerTriangularMat:=function(M)
    local i,j;
    if Length(M)=0  then
      return true;
    fi;
    for i in [1..Length(M)] do
      for j in [i+1..Length(M[1])] do
        if M[i][j]<>0*M[i][j] then
          return false;
        fi;
      od;
    od;
    return true;
  end;
fi;
RandomLowerTriangularMat:=function(m,n,R)
  local a,i,j;
  a:=RandomMat(m,n,R);
  for i in [1..m] do
    for j in [i+1..n] do
      a[i][j]:=0*a[i][j];
    od;
  od;
  return a;
end;

# we want that a gcd of polynomials is always monic
myGcd:=function(f,g)
  local d,c;
  d:=Gcd(f,g);
  c:=myCoeffsPol(d);
  if c[Length(c)]<>c[1]^0 then
    return c[Length(c)]^(-1)*d;
  else
    return d;
  fi;
end;

myLcm:=function(f,g)
  local d,c;
  d:=Lcm(f,g);
  c:=myCoeffsPol(d);
  if c[Length(c)]<>c[1]^0 then
    return c[Length(c)]^(-1)*d;
  else
    return d;
  fi;
end;

Print("###################################################################\n");
Print("##                                                               ##\n");
Print("##  MAXIMAL VECTORS AND THE  FROBENIUS NORMAL FORM OF MATRICES   ##\n");
Print("##  (Meinolf Geck,  University of Stuttgart,  9 February 2019)   ##\n");
Print("##                                                               ##\n");
Print("##  Main functions,  where  A  is a square matrix over a field   ##\n");
Print("##  (note that matrices act on the right on row vectors):        ##\n");
Print("##                                                               ##\n");
Print("##  * FrobeniusNormalForm(A);    compute Frobenius normal form   ##\n");
Print("##                                    and a base change matrix   ##\n");
Print("##  * InvariantFactorsMat(A);    compute the invariant factors   ##\n");
Print("##  * MaximalVectorMat(A);      compute a vector whose minimal   ##\n");
Print("##                                     polynomial is that of A   ##\n");
Print("##  * SpinMatVector(A,v);             spin up a vector under A   ##\n");
Print("##  * RatFormStep1J(A,v);              compute cyclic subspace   ##\n");
Print("##                                        and Jacob complement   ##\n");
Print("##  * RatFormCyclicChain(A);            compute complete chain   ##\n");
Print("##                                of relative cyclic subspaces   ##\n");
Print("##  * CharPolyMat(A);    compute the characteristic polynomial   ##\n");
Print("##  * GcdCoprimeSplit(f,g)    compute coprime factorisation of   ##\n");
Print("##                                      lcm of two polynomials   ##\n");
Print("##                                                               ##\n");
Print("##  Works in GAP3 and GAP4. For some tests, type 'FrobTest();'   ##\n");
Print("##  For some basic help, type 'FrobHelp(<function>);'            ##\n");
Print("##  Updates at pnp.mathematik.uni-stuttgart.de/iaz/iaz2/geckmf   ##\n");
Print("##                 All comments welcome!                         ##\n");
Print("##                                                               ##\n");
Print("###################################################################\n");

##########################################################################
##
#F  SpinMatVector( <A>, <v> ) . . . . . .  spin up a vector under a matrix
##
##  'SpinMatVector' computes  the  smallest subspace containing the vector
##  <v>  and invariant under the matrix  <A>.  The  output is a quadruple.
##  The first component contains a  basis in row echelon form,  the second
##  the  matrix  with  rows v, Av, A^2v, ..., A^(d-1)v, the third  one the
##  coefficients of the minimal polynomial of <v>  (of degree d),  and the
##  last one the positions of the pivots of the first component.
##
##  Examples:
##     gap>  A:=[[2,0,0],[0,-1,0],[0,0,1]];
##     gap>  v:=[1,1,0];
##     gap>  SpinMatVector(A,v);
##     [ [ [ 1, 0, 0 ], [ 0, 1, 0 ] ],
##       [ [ 1, 1, 0 ], [ 2, -1, 0 ] ],
##       [ -2, -1, 1 ], [ 1, 2 ] ]    So v has minimal polynomial x^2-x-2.
##     gap>  SpinMatVector(A,[1,1,1]);
##     [ [ [ 1, 0, 0 ], [ 0, 1, 0 ], [ 0, 0, 1 ] ],
##       [ [ 1, 1, 1 ], [ 2, -1, 1 ], [ 4, 1, 1 ] ],
##       [ 2, -1, -2, 1 ], [ 1, 2, 3 ] ]  minimal polynomial x^3-2x^2-x+2.
##
# this version does not compute the minimal polynomial, only the subspace
SpinMatVector1:=function(mat,vec)
  local A,v,k,d,one,zero,i,j,bahn,bahn1,nv,nv1,piv,koeff,weiter;
  k:=DefaultFieldOfMatrix(mat);
  v:=ImmutableVector(k,vec);
  A:=ImmutableMatrix(k,mat);
  one:=v[1]^0;
  zero:=0*v[1];
  i:=1;
  while i<=Length(v) and v[i]=zero do
    i:=i+1;
  od;
  if i>Length(v) then
    Error("# zero vector");
  fi;
  bahn:=[v];
  piv:=[i];
  bahn1:=[v[i]^(-1)*v];
  weiter:=true;
  d:=Length(bahn1);
  while weiter do
    nv1:=bahn[Length(bahn)]*A;
    nv:=ShallowCopy(nv1);
    for j in [1..d] do
      koeff:=nv[piv[j]];
      if koeff<>zero then
        AddRowVector(nv,bahn1[j],-koeff);
        #nv:=nv-koeff*bahn1[j];
      fi;
    od;
    if nv=0*nv then
      weiter:=false;
    else
      i:=1;
      while nv[i]=zero do
        i:=i+1;
      od;
      Add(piv,i);
      if nv[i]=one then
        Add(bahn1,nv);
      else
        Add(bahn1,nv[i]^(-1)*nv);
      fi;
      Add(bahn,nv1);
      d:=d+1;
    fi;
  od;
  #b1:=ShallowCopy(piv);
  #Sort(b1);
  #b1:=List(b1,i->Position(piv,i));
  #return [bahn1{b1},bahn,nv1,piv{b1}];
  return [bahn1,bahn,nv1,piv];
end;

# here, pivots are always updated
SpinMatVector1Old:=function(mat,vec)
  local A,v,k,d,one,zero,x,i,j,bahn,bahn1,b1,neuv,p,piv,r,minpol,koeff,weiter;
  k:=DefaultFieldOfMatrix(mat);
  v:=ImmutableVector(k,vec);
  A:=ImmutableMatrix(k,mat);
  one:=v[1]^0;
  zero:=0*v[1];
  i:=1;
  while i<=Length(v) and v[i]=zero do
    i:=i+1;
  od;
  if i>Length(v) then
    Error("# zero vector");
  fi;
  bahn:=[v];
  piv:=[i];
  b1:=[1];
  if v[i]<>one then
    bahn1:=[v[i]^(-1)*v];
  else
    bahn1:=[ShallowCopy(v)];
  fi;
  weiter:=true;
  d:=Length(bahn1);
  while weiter do
    neuv:=bahn[Length(bahn)]*A;
    Add(bahn,neuv);
    for j in [1..d] do
      koeff:=neuv[piv[b1[j]]];
      if koeff<>zero then
        neuv:=neuv-koeff*bahn1[b1[j]];
      fi;
    od;
    if neuv=0*neuv then
      weiter:=false;
    else
      p:=1;
      while neuv[p]=zero do
        p:=p+1;
      od;
      if neuv[p]=one then
        Add(bahn1,neuv);
      else
        Add(bahn1,neuv[p]^(-1)*neuv);
      fi;
      # update pivots
      r:=[];
      if p<piv[b1[1]] then
        r:=[d+1];
        Append(r,[1..d]);
      else
        j:=1;
        while j<=d and piv[b1[j]]<p do
          j:=j+1;
        od;
        if j<=d then
          r:=[1..j-1];
          Add(r,d+1);
          Append(r,[j..d]);
        else
          r:=[1..d+1];
        fi;
      fi;
      Add(piv,p);
      Add(b1,d+1);
      b1:=b1{r};
      d:=d+1;
    fi;
  od;
  #bahn:=ImmutableMatrix(k,bahn);
  #minpol:=SolutionMat(bahn{[1..d]},bahn[d+1]);
  #Add(minpol,-v[1]^0);
  #return [bahn1{b1},bahn{[1..d]},-minpol,piv{b1}];
  return [bahn1{b1},bahn{[1..d]},bahn[d+1],piv{b1}];
end;

SpinMatVector:=function(mat,vec)
  local sp,minpol;
  sp:=SpinMatVector1(mat,vec);
  minpol:=SolutionMat(sp[2],sp[3]);
  Add(minpol,-minpol[1]^0);
  return [sp[1],sp[2],-minpol,sp[4]];
end;

SpinMatVectorOld:=function(mat,vec)
  local sp,minpol,bahn,b,k;
  k:=DefaultFieldOfMatrix(mat);
  sp:=SpinMatVector1(mat,vec);
  bahn:=ImmutableMatrix(k,sp[2]);
  b:=ImmutableVector(k,sp[3]);
  minpol:=SolutionMat(bahn,b);
  Add(minpol,-b[1]^0);
  return [sp[1],sp[2],-minpol,sp[4]];
end;

##########################################################################
##
#F  GcdCoprimeSplit( <a>, <b> ) . . . . . . . coprime factorisation of lcm
##
##  'GcdCoprimeSplit' computes a divisor <a1> of the polynomial <a>  and a
##  divisor <b1> of the polynomial <b> such that <a1> and <b1> are coprime
##  and the lcm of <a>, <b> is <a1>*<b1>.  This is based on Lemma 5 in
##
##  K. Bongartz,  A direct approach to the rational normal form,  preprint
##  available at arXiv:1410.1683.
##
##  (Note that it does not use the prime factorisation of polynomials  but
##  only gcd computations.)
##
##  Example:
##    gap> a:=x^2*(x-1)^3*(x-2)*(x-3);
##    x^7-8*x^6+24*x^5-34*x^4+23*x^3-6*x^2
##    gap> b:=x^2*(x-1)^2*(x-2)^4*(x-4);
##    x^9-14*x^8+81*x^7-252*x^6+456*x^5-480*x^4+272*x^3-64*x^2
##    gap> GcdCoprimeSplit(a,b);
##    [ x^5-4*x^4+5*x^3-2*x^2,                    # the (monic) gcd
##      x^6-6*x^5+12*x^4-10*x^3+3*x^2,            # a1
##      x^5-12*x^4+56*x^3-128*x^2+144*x-64 ]      # b1
##
GcdCoprimeSplit:=function(a,b)
  local d,ta,tb,a1,b1;
  d:=myGcd(a,b);
  if Degree(d)=0 then
    return [d,a,b];
  fi;
  if Degree(b)<=Degree(a) then
    if QuotientRemainder(a,b)[2]=0*b then
      return [b,a,b^0];
    else
      ta:=Quotient(a,d);
      tb:=Quotient(b,d);
      b1:=myGcd(tb^Degree(b),b);
      a1:=ta*Quotient(b,b1);
      return [d,a1,b1];
    fi;
  else
    return GcdCoprimeSplit(b,a){[1,3,2]};
  fi;
end;

##########################################################################
##
#F  PolynomialToMatVec( <A>, <pol>, <v> ) . . apply polynomial to a matrix
##  . . . . . . . . . . . . . . . . . . . . . . . . . and then to a vector
##
##  'PolynomialToMatVec' returns  the row vector  obtained  by multiplying
##  the row vector <v> with the matrix <pol>(<A>), where <pol> is the list
##  of coefficients of a polynomial.
##
##  Example:
##     gap> A:=([ [ 0, 1, 0, 1 ],
##     gap>       [ 0, 0, 0, 0 ],
##     gap>       [ 0, 1, 0, 1 ],
##     gap>       [ 1, 1, 1, 1 ] ]);;
##     gap> f:=x^6-6*x^5+12*x^4-10*x^3+3*x^2;;
##     gap> v:=[ 1, 1, 1, 1];;
##     gap> l:=myCoeffsPol(f);
##     gap> [ 0, 0, 3, -10, 12, -6, 1 ]
##     gap> PolynomialToMat(A,last,v);
##     [ 8, -16, 8, -16 ]
##
PolynomialToMatVec:=function(mat,pol,vec)
  local A,v,n,v1,i,k;
  k:=DefaultFieldOfMatrix(mat);
  v:=ImmutableVector(k,vec);
  A:=ImmutableMatrix(k,mat);
  n:=Length(pol);
  v1:=pol[n]*v;
  for i in Reversed([1..n-1]) do
    if v1<>0*v1 then
      v1:=v1*A;
    fi;
    if pol[i]<>0*pol[i] then
      v1:=v1+pol[i]*v;
    fi;
  od;
  return v1;
end;

##########################################################################
##
#F  LcmMaximalVectorMat( <A>, <v1>, <v2>, <pol1>, <pol2> ) . . compute lcm
##  . . .  . . . . . . of two minimal polynomials and corresponding vector
##
##  'LcmPolynomialToMatVec' returns,  given  a matrix  <A>,  vectors <v1>,
##  <v2> with minimal polynomials <pol1>, <pol2>,  a new pair [<v>,<pol>],
##  where <v> has minimal polynomial <pol>, and <pol> is the least common
##  multiple of <pol1> and <pol2>.
##  This crucially relies on  'GcdCoprimeSplit' to avoid  factorisation of
##  polynomials.
##
LcmMaximalVectorMat:=function(A,v1,v2,pol1,pol2)
  local d,k,v;
  k:=DefaultFieldOfMatrix(A);
  if QuotientRemainder(pol1,pol2)=0*pol1 then
    return [v1,pol1];
  elif QuotientRemainder(pol2,pol1)=0*pol2 then
    return [v2,pol2];
  else
    # wende lemma 44 an
    d:=GcdCoprimeSplit(pol1,pol2);
    if Degree(d[1])=0 then
      return [v1+v2,pol1*pol2];
    else
    #Print("!\c");
      v:=PolynomialToMatVec(A,myCoeffsPol(Quotient(pol1,d[2])),v1)+
             PolynomialToMatVec(A,myCoeffsPol(Quotient(pol2,d[3])),v2);
      return [v,d[2]*d[3]];
    fi;
  fi;
end;

##########################################################################
##
#F  MatCyclicChainBasis( <A> ) . . . . . . . . . .  compute complete chain
##  . . . . . . . . . . . . . . . . . . . . . of relative cyclic subspaces
##
##  'MatCyclicChainBasis'  repeatedly applies  a relative version  of  the
##  spinning algorithm to compute a chain of cyclic subspaces.  The output
##  is a pair [res, sp]  where <res> specifies the vectors in the standard
##  base which have to be spinned up, and  <sp> specifies the sizes of the
##  relative blocks. See also the related function 'RatFormCyclicChain'.
##
MatCyclicChainBasis:=function(mat)
  local A,A1,p1,k,t,idm,sp,lb,li,rest,i,n,d;
  k:=DefaultFieldOfMatrix(mat);
  A:=ImmutableMatrix(k,mat);
  n:=Length(A);
  if IsLowerTriangularMat(A) then
    return [[1..n],[1..n]];
  fi;
  idm:=A^0;
  sp:=SpinMatVector1(A,idm[1]);
  d:=Length(sp[1]);
  lb:=[1];
  li:=[1];
  if d<n then
    t:=sp[2];
    #p1:=Filtered([1..n],i->not (i in sp[4]));
    p1:=Difference([1..n],sp[4]);
    Append(t,idm{p1});
    t:=ImmutableMatrix(k,t);
    A1:=t*A*t^(-1);
    rest:=MatCyclicChainBasis(A1{[d+1..n]}{[d+1..n]});
    Append(li,p1{rest[1]});
    for i in rest[2] do
      Add(lb,i+d);
    od;
  fi;
  return [li,lb];
end;

# different version where no conjugation of matrices is used
# (depending on mat, the performance of the two versions can differ).
MatCyclicChainBasis1:=function(mat)
  local A,v,idm,k,d,i,j,res,bahn,bahn1,nv,nv1,piv,sp,np,koeff,weiter;
  k:=DefaultFieldOfMatrix(mat);
  A:=ImmutableMatrix(k,mat);
  idm:=A^0;
  bahn1:=[];
  bahn:=[];
  res:=[];
  piv:=[];
  d:=0;
  sp:=[];
  while d<Length(A) do
    weiter:=true;
    # define new vector
    i:=1;
    while i in piv do
      i:=i+1;
    od;
    Add(bahn,idm[i]);
    Add(bahn1,idm[i]);
    Add(res,i);
    Add(piv,i);
    d:=d+1;
    Add(sp,d);
    while weiter do
      nv1:=bahn[d]*A;
      nv:=ShallowCopy(nv1);
      for j in [1..d] do
        koeff:=nv[piv[j]];
        if koeff<>0*koeff then
          AddRowVector(nv,bahn1[j],-bahn1[j][piv[j]]^-1);
          #nv:=nv-(bahn1[j][piv[j]]^-1*koeff)*bahn1[j];
        fi;
      od;
      if nv=0*nv then
        weiter:=false;
      else
        Add(bahn,nv1);
        i:=1;
        while nv[i]=0*nv[i] do
          i:=i+1;
        od;
        Add(bahn1,nv);
        Add(piv,i);
        d:=d+1;
      fi;
    od;
  od;
  #Print("\n");
  bahn:=ImmutableMatrix(k,bahn);
  return [res,sp,bahn,bahn1,bahn*A*bahn^-1];
end;

##########################################################################
##
#F  NPCleanAndExtend( <cY>, <v> ) . . . . . . . . . clean and extend as in
##  . . . . . . . . . . . . . . . . . . . Neunhoeffer-Praeger, Algorithm 1
##
##  'NPCleanAndExtendMat'
##
NPCleanAndExtend:=function(cY,v)
  local Y,S,T,T1,l,tt,a,w,m,i,koeff,zero;
  zero:=0*v[1];
  Y:=cY[1];
  S:=cY[2];
  T:=cY[3];
  l:=cY[4];
  w:=ShallowCopy(v);
  a:=[];
  m:=Length(l);
  for i in [1..m] do
    koeff:=w[l[i]];
    if koeff<>zero then
      w:=w-koeff*S[i];
    fi;
    Add(a,koeff);
  od;
  if w=0*w then
    return [true,cY,a];
  else
    i:=1;
    while w[i]=zero do
      i:=i+1;
    od;
    Add(a,w[i]);
    Add(l,i);
    Add(Y,v);
    if w[i]=w[i]^0 then
      Add(S,w);
    else
      Add(S,w[i]^-1*w);
    fi;
    for i in [1..m] do
      Add(T[i],zero);
      if w[i]=w[i]^0 then
        tt:=-a*T;
        Add(tt,w[i]);
      else
        tt:=-w[i]^-1*a*T;
        Add(tt,w[i]^-1);
      fi;
    od;
    return [false,[Y,S,T,l],a];
  fi;
end;

##########################################################################
##
#F  NPMaximalVectorMat( <A> ) . . . . . . . . . . . compute maximal vector
##
##  'NPMaximalVectorMat'  returns a maximal vector of the matrix <A>, that
##  is, a vector whose minimal polynomial is that of <A>.  This is done by
##  first invoking the Neunhoeffer-Praeger algorithm to compute the latter
##  (for this purpose, the package 'cvec' is loaded),  and then repeatedly
##  spinning up vectors until a maximal one is found. This in turn is done
##  by running through the same procedure as in 'MatCyclicChainBasis' (but
##  immediately  stopping  this  procedure  once a cyclic  subspace of the
##  correct degree is found).
##
##  Example:
##   gap> A:=[ [ 0, 1, 0, 1 ],
##   gap>      [ 0, 0, 0, 0 ],
##   gap>      [ 0, 1, 0, 1 ],
##   gap>      [ 1, 1, 1, 1 ] ];;
##   NPMaximalVectorMat(A);
##   #I Degree of minimal polynomial is 3
##   [ [ 1, 0, 0, 0 ], x^3-x^2-2*x ]
##
##  If one does  not want  to rely  on the  Neunhoeffer-Praeger algorithm,
##  then one can also use the function 'MaximalVectorMat' which implements
##  this directly, but is slower (about 5 times for larger matrices).
##
NPMaximalVectorMat:=function(mat)
  local A,v,idm,k,d,minpol,t,x,i,j,bahn,bahn1,zero,one,
                      nv,nv1,piv,p1,p2,v1,v2,np,koeff,weiter;
  if VERSION[1]<>'4' then
    Print("#I sorry, not available in GAP3\n");
    return false;
  fi;
  k:=DefaultFieldOfMatrix(mat);
  A:=ImmutableMatrix(k,mat);
  one:=A[1][1]^0;
  zero:=0*A[1][1];
  idm:=A^0;
  if IsFinite(k) then
    np:=MinimalPolynomial(CMat(A));
  else
    np:=MinimalPolynomial(A);
  fi;
  Print("#I Degree of minimal polynomial is ",Degree(np)," \c");
  if Length(A)=1 then
    Print("\n");
    return [idm[1],np];
  fi;
  if IsLowerTriangularMat(A) then
    v1:=idm[Length(A)];
  else
    v1:=idm[1];
  fi;
  t:=SpinMatVector1(A,v1);
  if Degree(np)=Length(t[1]) then
    Print("\n");
    return [v1,np];
  fi;
  bahn1:=t[1];
  bahn:=t[2];
  piv:=t[4];
  minpol:=SolutionMat(bahn,t[3]);
  Add(minpol,-one);
  p1:=myPolynomial(k,-minpol);
  d:=Length(bahn1);
  Print("(\c");
  while Degree(p1)<Degree(np) do
    Print(Degree(p1),",\c");
    weiter:=true;
    # define new vector
    i:=1;
    while i in piv do
      i:=i+1;
    od;
    v2:=idm[i];
    Add(bahn,v2);
    Add(bahn1,v2);
    p2:=myPolynomial(k,SpinMatVector(A,v2)[3]);
    Print(Degree(p2),",\c");
    v:=LcmMaximalVectorMat(A,v1,v2,p1,p2);
    v1:=v[1];
    p1:=v[2];
    if Degree(p1)<Degree(np) then
      Add(piv,i);
      d:=d+1;
      while weiter do
        nv1:=bahn[Length(bahn)]*A;
        nv:=ShallowCopy(nv1);
        for j in [1..d] do
          koeff:=nv[piv[j]];
          if koeff<>zero then
            AddRowVector(nv,bahn1[j],-koeff);
            #nv:=nv-koeff*bahn1[j];
          fi;
        od;
        if nv=0*nv then
          weiter:=false;
        else
          Add(bahn,nv1);
          i:=1;
          while nv[i]=zero do
            i:=i+1;
          od;
          if nv[i]=one then
            Add(bahn1,nv);
          else
            Add(bahn1,nv[i]^(-1)*nv);
          fi;
          Add(piv,i);
          d:=d+1;
        fi;
      od;
    fi;
  od;
  if np<>p1 then
    Error("mist_pol",[np,p1]);
  fi;
  Print(")\n");
  return [v1,p1];
end;

##########################################################################
##
#F  RatFormStep1( <A>, <v> ) . . . . . . . .  compute cyclic subspaces and
##  . . . . . . . . . . . . . . . . . . . . . . . . . . perform base chain
#F  RatFormStep1J( <A>, <v> ) . . . . .  same but using Jacob's complement
#F  RatFormStep1Js( <A>, <v> ) . . . . . . strong version where complement
##  . . . . . . . . . . . . . . . . . . . . . . . . . . . . . is invariant
##
##  'RatFormStep1' spins up a  vector  <v> under a  matrix  <A>,  computes
##  a complementary subspace  (by extending with  standard basis vectors),
##  and performs the base change. In the second form, Jacob's construction
##  of a  complementary  subspace is used  (which may not be  invariant in
##  general).  In the third version, 'RatFormStep1J' is applied repeatedly
##  until the complement is invariant.
##
RatFormStep1:=function(mat,vec)
  local A,A1,v,sp,t,i,k,d,idm,minp;
  k:=DefaultFieldOfMatrix(mat);
  v:=ImmutableVector(k,vec);
  A:=ImmutableMatrix(k,mat);
  idm:=A^0;
  sp:=SpinMatVector1(A,v);
  t:=sp[2];
  d:=Length(t);
  #Append(t,idm{Filtered([1..Length(A)],i->not (i in sp[4]))});
  Append(t,idm{Difference([1..Length(A)],sp[4])});
  t:=ImmutableMatrix(k,t);
  A1:=t*A*t^(-1);
  minp:=ShallowCopy(A1[d]{[1..d]});
  Add(minp,-minp[1]^0);
  return [A1,t,-minp];
end;

##########################################################################
##
#F  JacobMatComplement( <T>, <d> ) . . . . . .  compute Jacob's complement
##  . . . . . . . . . . . . . . . . . . . . . . . . . to a cyclic subspace
##
##  'JacobMatComplement' modifies an already given  complementary subspace
##  to the  complementary subspace defined by  Jacob;  concretely, this is
##  realized by assuming that  <T>  is a matrix in block triangular shape,
##  where the upper left diagonal block is a companion matrix (as returned
##  by 'RatFormStep1'; the variable <d> gives the size of that block.
##  (If <T> gives a  maximal cyclic subspace,  then  Jacob's complement is
##  also  <T>-invariant;  but even if not,  it appears  to be  very useful
##  because it produces many zeroes.)
##
JacobMatComplementOld:=function(T,d)
  local base,idm,i,k,F,tF,tT;
  k:=DefaultFieldOfMatrix(T);
  idm:=T^0;
  base:=idm{[1..d]};
  tT:=TransposedMat(ImmutableMatrix(k,T));
  F:=[idm[d]];
  for i in [2..d] do
    Add(F,F[i-1]*tT);
  od;
  tF:=TransposedMat(ImmutableMatrix(k,F));
  Append(base,NullspaceMat(tF));
  base:=ImmutableMatrix(k,base);
  return base;
end;

# we need matrix in reduced row echelon form
# but NullspaceMat does not guarantee this
JacobMatComplement:=function(T,d)
  local base,i,j,k,F,tF,tT;
  k:=DefaultFieldOfMatrix(T);
  base:=IdentityMat(Length(T),k);
  tT:=TransposedMat(ImmutableMatrix(k,T));
  F:=[base[d]];
  for i in [2..d] do
    Add(F,F[i-1]*tT);
  od;
  TriangulizeMat(F);
  for i in [1..Length(T)-d] do
    for j in [1..d] do
      base[d+i][j]:=-F[j][d+i];
    od;
  od;
  base:=ImmutableMatrix(k,base);
  #if base<>JacobMatComplementOld(T,d) then
  #  Error("mist Jacob");
  #fi;
  return base;
end;

# output [a,b,c,d] where a=new matrix, b=base change,
# c=minpol (as list of coeffs), d=split or not
RatFormStep1J:=function(mat,vec)
  local A,v,k,t,t1,i,j,d,n,str;
  k:=DefaultFieldOfMatrix(mat);
  A:=ImmutableMatrix(k,mat);
  v:=ImmutableVector(k,vec);
  t:=RatFormStep1(A,v);
  t1:=t[1];
  n:=Length(A);
  d:=Length(t[3])-1;
  if d=n or t1{[d+1..n]}{[1..d]}=NullMat(n-d,d,k) then
    return [t[1],t[2],t[3],"split"];
  fi;
  j:=ImmutableMatrix(k,JacobMatComplement(t[1],d));
  t1:=j*t[1]*j^-1;
  i:=d+1;
  while i<=n and t1[i][1]=0*t1[i][1] do
    i:=i+1;
  od;
  if i<=n then
    str:="not";
  else
    str:="split";
  fi;
  if str="split" and d<n and t1{[d+1..n]}{[1..d]}<>NullMat(n-d,d,k) then
    str:="not";
  fi;
  return [t1,j*t[2],t[3],str];
end;

# strong version, repeat until cyclic blocks splits off, same output
# as RatFormStep1J but with 4th component equal to split.
RatFormStep1Js:=function(mat,vec)
  local A,bt,k,i,j,d,r,n,v1,zero,weiter;
  k:=DefaultFieldOfMatrix(mat);
  A:=ImmutableMatrix(k,mat);
  v1:=ImmutableVector(k,vec);
  n:=Length(A);
  zero:=0*A[1][1];
  r:=RatFormStep1J(A,v1);
  bt:=r[2];
  while r[4]="not" do
    d:=Length(r[3]);
    weiter:=true;
    j:=1;
    while weiter do
      i:=n;
      while i>=d and r[1][i][j]=zero do
        i:=i-1;
      od;
      if i>=d then
        weiter:=false;
      else
        j:=j+1;
      fi;
    od;
    v1:=ShallowCopy(0*v1);
    v1[i]:=v1[1]^0;
    r:=RatFormStep1J(r[1],v1);
    bt:=r[2]*bt;
  od;
  #if bt*A*bt^-1<>r[1] then
  #  Error("mist neumax");
  #fi;
  return [r[1],bt,r[3],"split"];
end;

# how to choose vector to spin up?

ChooseSpinVector:=function(A)
  local idm,i,n;
  n:=Length(A);
  i:=1;
  while i<=n and A[i]=0*A[i] do
    i:=i+1;
  od;
  if i>n then
    return false;
  else
    idm:=A^0;
    return idm[i];
  fi;
end;

# random version
#ChooseSpinVector:=function(A)
#  return RandomMat(1,Length(A),DefaultField(A[1][1]))[1];
#end;

# andere Version: Find last row which is non-zero

ChooseSpinVector1:=function(A)
  local v,i,n;
  n:=Length(A);
  v:=List([1..n],i->A[1][1]^0);
  i:=1;
  while i<=n and v*A=0*v do
    v[i]:=0*v[i];
    i:=i+1;
  od;
  if i>n then
    return false;
  else
    return v;
  fi;
end;

#ChooseSpinVector:=function(A)
#  local v,i,n;
#  n:=Length(A);
#  v:=List([1..n],i->0*A[1][1]);
#  v[1]:=v[1]^0;
#  return v;
#end;

BuildBlockDiagonalMat:=function(A,B)
  local d,neu,n,k;
  k:=DefaultFieldOfMatrix(B);
  d:=Length(A);
  n:=Length(A)+Length(B);
  neu:=NullMat(n,n,k);
  neu{[1..d]}{[1..d]}:=A;
  neu{[d+1..n]}{[d+1..n]}:=B;
  return ImmutableMatrix(k,neu);
end;

##########################################################################
##
#F  RatFormCyclicChain( <A> ) . . . . . compute complete chain of relative
##  . . . . . . . . . . . . cyclic subspaces (with additional information)
##
##  'RatFormCyclicChain'  repeatedly applies  'RatFormStep1J' to compute a
##  chain of cyclic subspaces. The output is a triple [A1,P,piv]  where A1
##  is in block triangular shape (where each diagonal block is a companion
##  matrix), P is a base change matrix (such that  PAP^(-1) = A1), and piv
##  contains the minimal polynomials of the blocks. The function checks if
##  <A> is the zero or a scalar matrix, where the result is obvious.
##
##  Example:
##   gap> A:=[ [ 0, 1, 0, 1 ],
##   gap>      [ 0, 0, 1, 0 ],
##   gap>      [ 0, 1, 0, 1 ],
##   gap>      [ 1, 1, 1, 1 ] ]);;
##   gap> PrintArray(RatFormCyclicChain(A)[1]);
##   [ [    0,     1,     0,     0 ],    There are 2 diagonal blocks
##     [    0,     0,     1,     0 ],    but (because of the entry 1/2)
##     [    0,     3,     1,     0 ],    the extension is not split.
##     [  1/2,     0,     0,     0 ] ]
##   (Compare with 'FrobeniusNormalForm(A)[1]' which has just one block.)
##
RatFormCyclicChain:=function(mat)
  local A,A1,P,P1,i,step1,rest,v,d,k,idm;
  k:=DefaultFieldOfMatrix(mat);
  A:=ImmutableMatrix(k,mat);
  if A=0*A then
    v:=A[1][1]^0;
    return [A,A^0,List([1..Length(A)],i->[i,[0*v,v]])];
  fi;
  if IsDiagonalMat(A) then
    v:=A[1][1]^0;
    return [A,A^0,List([1..Length(A)],i->[i,[-A[i][i],v]])];
  fi;
  idm:=A^0;
  if IsLowerTriangularMat(A) then
    step1:=RatFormStep1J(A,idm[Length(A)]);
  else
    step1:=RatFormStep1J(A,idm[1]);
  fi;
  A1:=ImmutableMatrix(k,step1[1]);
  P1:=ImmutableMatrix(k,step1[2]);
  d:=Length(step1[3])-1;
  if d<Length(A) then
    rest:=RatFormCyclicChain(A1{[d+1..Length(A)]}{[d+1..Length(A)]});
    P:=BuildBlockDiagonalMat(idm{[1..d]}{[1..d]},rest[2]);
    return [P*A1*P^(-1),P*P1,
       Concatenation([[1,step1[3]]],List(rest[3],i->[i[1]+d,i[2]]))];
  else
    return [step1[1],step1[2],[[1,step1[3]]]];
  fi;
end;

# strong form: obtain block diagonal shape
RatFormCyclicBlocks:=function(mat)
  local A,A1,P,P1,i,step1,rest,v,d,k,idm;
  k:=DefaultFieldOfMatrix(mat);
  A:=ImmutableMatrix(k,mat);
  if A=0*A then
    v:=A[1][1]^0;
    return [A,A^0,List([1..Length(A)],i->[i,[0*v,v]])];
  fi;
  if IsDiagonalMat(A) then
    v:=A[1][1]^0;
    return [A,A^0,List([1..Length(A)],i->[i,[-A[i][i],v]])];
  fi;
  idm:=A^0;
  if IsLowerTriangularMat(A) then
    step1:=RatFormStep1Js(A,idm[Length(A)]);
  else
    step1:=RatFormStep1Js(A,idm[1]);
  fi;
  A1:=ImmutableMatrix(k,step1[1]);
  P1:=ImmutableMatrix(k,step1[2]);
  d:=Length(step1[3])-1;
  if d<Length(A) then
    rest:=RatFormCyclicBlocks(A1{[d+1..Length(A)]}{[d+1..Length(A)]});
    P:=BuildBlockDiagonalMat(idm{[1..d]}{[1..d]},rest[2]);
    return [P*A1*P^(-1),P*P1,
       Concatenation([[1,step1[3]]],List(rest[3],i->[i[1]+d,i[2]]))];
  else
    return [step1[1],step1[2],[[1,step1[3]]]];
  fi;
end;

RatFormCyclicChain1:=function(mat)
  local A,A1,P,P1,i,step1,rest,v,d,k,idm;
  k:=DefaultFieldOfMatrix(mat);
  A:=ImmutableMatrix(k,mat);
  if A=0*A then
    v:=A[1][1]^0;
    return [A,A^0,List([1..Length(A)],i->[i,[0*v,v]])];
  fi;
  if IsLowerTriangularMat(A) then
    v:=A[1][1]^0;
    return [A,A^0,List([1..Length(A)],i->[i,[-A[i][i],v]])];
  fi;
  idm:=A^0;
  step1:=RatFormStep1(A,idm[1]);
  A1:=ImmutableMatrix(k,step1[1]);
  P1:=ImmutableMatrix(k,step1[2]);
  d:=Length(step1[3])-1;
  if d<Length(A) then
    rest:=RatFormCyclicChain1(A1{[d+1..Length(A)]}{[d+1..Length(A)]});
    P:=BuildBlockDiagonalMat(idm{[1..d]}{[1..d]},rest[2]);
    return [P*A1*P^(-1),P*P1,
       Concatenation([[1,step1[3]]],List(rest[3],i->[i[1]+d,i[2]]))];
  else
    return [step1[1],step1[2],[[1,step1[3]]]];
  fi;
end;

##########################################################################
##
#F  CharPolyMat( <A> ) . . . . . .  computes the characteristic polynomial
##
##  'CharPolyMat' returns the characteristic polynomial of the matrix <A>,
##  using a chain of relative cyclic subspaces.
##
##  Example:
##     gap> CharPolyMat([ [ 0, 1, 0, 1 ],
##     gap>               [ 0, 0, 0, 0 ],
##     gap>               [ 0, 1, 0, 1 ],
##     gap>               [ 1, 1, 1, 1 ] ]);
##     x^4-x^3-2*x^2
##
CharPolyMat:=function(mat)
  local A,A1,d,k,t,p1,idm,sp,i,n,cp;
  k:=DefaultFieldOfMatrix(mat);
  A:=ImmutableMatrix(k,mat);
  n:=Length(A);
  cp:=myPolynomial(k,[A[1][1]^0]);
  if IsLowerTriangularMat(A) then
    cp:=myPolynomial(k,[-A[1][1],A[1][1]^0]);
    for i in [2..n] do
      cp:=myPolynomial(k,[-A[i][i],A[1][1]^0])*cp;
    od;
    if n mod 2=0 then
      return cp;
    else
      return -cp;
    fi;
  fi;
  idm:=A^0;
  sp:=SpinMatVector(A,idm[1]);
  cp:=myPolynomial(k,sp[3]);
  d:=Length(sp[1]);
  if d=n then
    if n mod 2=0 then
      return cp;
    else
      return -cp;
    fi;
  else
    t:=sp[2];
    #p1:=Filtered([1..n],i->not (i in sp[4]));
    p1:=Difference([1..n],sp[4]);
    Append(t,idm{p1});
    t:=ImmutableMatrix(k,t);
    A1:=t*A*t^(-1);
    cp:=cp*CharPolyMat(A1{[d+1..n]}{[d+1..n]});
    if n mod 2=0 then
      return cp;
    else
      return -cp;
    fi;
  fi;
end;

#CharPolyMatOld:=function(A)
#  local f,i,p,l;
#  f:=DefaultField(A[1][1]);
#  if A=0*A then
#    p:=X(f)^Length(A);
#  else
#    p:=X(f)^0;
#    for i in RatFormCyclicChain(A)[3] do
#      p:=p*myPolynomial(f,i[2]);
#    od;
#  fi;
#  if Length(A) mod 2=0 then
#    return p;
#  else
#    return -p;
#  fi;
#end;

##########################################################################
##
#F  MaximalVectorMat( <A> ) . . . . . .  computes a maximal vector and its
##  . . . . . . . . . . . . . . . . . . . . . . . . . . minimal polynomial
##
##  'MaximalVectorMat ' returns a  maximal vector of a matrix  <A> and its
##  minimal polynomial.  (This  is the  first  step  in  constructing  the
##  rational canonical form;  it uses the output of 'RatFormCyclicChain'.)
##  The function checks if  <A> is the zero  or a scalar matrix, where the
##  result is obvious.
##
##  Example:
##     gap> MaximalVectorMat([ [ 0, 1, 0, 1 ],
##     gap>                    [ 0, 0, 0, 0 ],
##     gap>                    [ 0, 1, 0, 1 ],
##     gap>                    [ 1, 1, 1, 1 ] ]);
##     [ [ 1, 0, 0, 0 ], x^3-x^2-2*x ]
##     So v=[1, 0, 0, 0] is a maximal vector,
##     with minimal polynomial mu(A,v)=-2x-x^2+x^3
##
##  See also 'NPMaximalVectorMat'.
##
MaximalVectorMat:=function(mat)
  local A,k,d,idm,ch,v,v2,vp,pol,pol2,i;
  k:=DefaultFieldOfMatrix(mat);
  A:=ImmutableMatrix(k,mat);
  if A=0*A then
    #Print("#I Zero matrix\n");
    v:=ShallowCopy(A[1]);
    v[1]:=v[1]^0;
    return [v,myPolynomial(k,[0*v[1],v[1]])];
  fi;
  if IsDiagonalMat(A) and ForAll([2..Length(A)],i->A[i][i]=A[1][1]) then
    #Print("#I Scalar matrix \n");
    v:=ShallowCopy(A[1]);
    v[1]:=v[1]^0;
    return [v,[-A[1][1],v[1]]];
  fi;
  ch:=RatFormCyclicChain(A);
  Print("#I chain complete \n");
  if Length(ch[3])=1 then
    Print("#I Matrix is cyclic\n");
    return [ch[2][1],myPolynomial(k,ch[3][1][2])];
  else
    #Print("#I There are ",Length(ch[3])-1, " cyclic subspaces to consider \c");
    idm:=ch[1]^0;
    vp:=[ShallowCopy(idm[1]),myPolynomial(k,ch[3][1][2])];
    vp:=[idm[1],myPolynomial(k,ch[3][1][2])];
    for i in [2..Length(ch[3])] do
      v2:=idm[ch[3][i][1]];
      pol2:=myPolynomial(k,SpinMatVector(ch[1],v2)[3]);
      if QuotientRemainder(vp[2],pol2)[2]<>0*pol2 then
        vp:=LcmMaximalVectorMat(ch[1],vp[1],v2,vp[2],pol2);
      fi;
    od;
    #Print("\n");
    return [vp[1]*ch[2],vp[2]];
  fi;
end;

# this is still experimental: split off companion matrix
MaximalVectorMatStep1:=function(mat)
  local A,bt,k,i,j,d,r,n,v1,zero,weiter;
  k:=DefaultFieldOfMatrix(mat);
  A:=ImmutableMatrix(k,mat);
  n:=Length(A);
  zero:=0*A[1][1];
  Print("#I Degree: \c");
  v1:=ShallowCopy(0*A[1]);
  if IsLowerTriangularMat(A)=true then
    r:=v1[1]^0;
    for i in [1..n] do
      v1[i]:=r;
    od;
  else
    v1[1]:=v1[1]^0;
  fi;
  r:=RatFormStep1J(A,v1);
  bt:=r[2];
  while r[4]="not" do
    d:=Length(r[3]);
    Print(d-1," \c");
    weiter:=true;
    j:=1;
    while weiter do
      i:=n;
      while i>=d and r[1][i][j]=zero do
        i:=i-1;
      od;
      if i>=d then
        weiter:=false;
      else
        j:=j+1;
      fi;
    od;
#    v2:=r[2][i];
#    sp:=SpinMatVector(A,v2);
#    p2:=myPolynomial(k,sp[3]);
#    v:=LcmMaximalVectorMat(A,v1,v2,p1,p2);
#    v1:=v[1];
#    p1:=v[2];
#    r:=RatFormStep1J(A,v1);
#    v1:=r[2][i];
#    r:=RatFormStep1J(A,r[2][i]);
#    p1:=myPolynomial(k,r[3]);
    v1:=ShallowCopy(0*A[1]);
    v1[i]:=v1[1]^0;
# contains old subspace so work with relative version???
    r:=RatFormStep1J(r[1],v1);
    bt:=r[2]*bt;
  od;
  Print(Length(r[3])-1," \n");
  #if bt*A*bt^-1<>r[1] then
  #  Error("mist neumax");
  #fi;
  return [bt[1],myPolynomial(k,r[3]),r[1],bt];
end;

# obtain block diagonal shape
MaximalVectorMatStep2:=function(mat)
  local A,A1,A2,P,i,k,idm,step1,rest,d,piv;
  k:=DefaultFieldOfMatrix(mat);
  A:=ImmutableMatrix(k,mat);
  idm:=A^0;
  if IsDiagonalMat(A) then
    return [A,idm,List([1..Length(A)],i->i)];
  fi;
  step1:=MaximalVectorMatStep1(mat);
  A1:=step1[3];
  d:=Degree(step1[2]);
  if d<Length(A) then
    piv:=[1];
    rest:=MaximalVectorMatStep2(A1{[d+1..Length(A)]}{[d+1..Length(A)]});
    P:=BuildBlockDiagonalMat(IdentityMat(d,k),rest[2]);
    A2:=BuildBlockDiagonalMat(A1{[1..d]}{[1..d]},rest[1]);
    for i in rest[3] do
      Add(piv,i+d);
    od;
    return [A2,P*step1[4],piv];
  else
    return [A1,step1[4],[1]];
  fi;
end;

NeuMaximalVectorMatStep1:=function(mat)
  local A,bt,k,i,j,d,r,n,v1,weiter;
  k:=DefaultFieldOfMatrix(mat);
  A:=ImmutableMatrix(k,mat);
  n:=Length(A);
  Print("#I Degree: \c");
  v1:=ShallowCopy(0*A[1]);
  if IsLowerTriangularMat(A)=true then
    v1[n]:=v1[1]^0;
  else
    v1[1]:=v1[1]^0;
  fi;
  r:=RatFormStep1J(A,v1);
  while r[4]="not" do
    d:=Length(r[3]);
    Print(d-1," \c");
    weiter:=true;
    j:=1;
    while weiter do
      i:=n;
      while i>=d and r[1][i][j]=0*r[1][i][j] do
        i:=i-1;
      od;
      if i>=d then
        weiter:=false;
      else
        j:=j+1;
      fi;
    od;
    v1:=ShallowCopy(0*A[1]);
    v1[i]:=v1[1]^0;
    r:=RatFormStep1J(r[1],v1);
  od;
  Print(Length(r[3])-1," \n");
  #if bt*A*bt^-1<>r[1] then
  #  Error("mist neumax");
  #fi;
  return [myPolynomial(k,r[3]),r[1]];
end;

NeuMaximalVectorMatStep2:=function(mat)
  local A,A1,k,idm,null,st1,i,d,r1,res,n;
  k:=DefaultFieldOfMatrix(mat);
  A:=ImmutableMatrix(k,mat);
  n:=Length(A);
  if IsDiagonalMat(A) then
    res:=Set(List([1..n],i->A[i][i]));
    return Product(List(res,i->myPolynomial(k,[-i,i^0])));
  fi;
  st1:=NeuMaximalVectorMatStep1(mat);
  d:=Degree(st1[1]);
  if d=n then
    return st1[1];
  else
    A1:=st1[2];
    r1:=NeuMaximalVectorMatStep2(A1{[d+1..n]}{[d+1..n]});
    return myLcm(st1[1],r1);
  fi;
end;

NeuMaximalVectorMat:=function(mat)
  local A,A1,st1,st2,d,k,n,v;
  k:=DefaultFieldOfMatrix(mat);
  A:=ImmutableMatrix(k,mat);
  n:=Length(A);
  if IsDiagonalMat(A) and ForAll([2..n],i->A[i][i]=A[1][1]) then
    v:=ShallowCopy(0*A[1]);
    v[1]:=v[1]^0;
    return [v,myPolynomial(k,[-A[1][1],A[1][1]^0])];
  fi;
  st1:=MaximalVectorMatStep1(A);
  d:=Degree(st1[2]);
  if d=n then
    return [st1[1],st1[2]];
  else
    A1:=st1[3];
    st2:=NeuMaximalVectorMat(A1{[d+1..n]}{[d+1..n]});
    if QuotientRemainder(st1[2],st2[2])=0*st2[2] then
      return [st1[1],st1[2]];
    else
      v:=(0*A[1][1])*[1..d];
      v[1]:=v[1]^0;
      Append(v,st2[1]);
      return [v*st1[4],myLcm(st1[2],st2[2])];
    fi;
  fi;
end;

NeuMaximalVectorMat1:=function(mat)
  local A,A1,k,m,idm,i,r,v1,p1,p2,nr,nv;
  k:=DefaultFieldOfMatrix(mat);
  A:=ImmutableMatrix(k,mat);
  Print("#I \c");
  m:=MatCyclicChainBasis(A)[1];
  idm:=A^0;
  i:=1;
  Print(m[i]," \c");
  v1:=idm[m[i]];
  r:=RatFormStep1J(A,v1);
  p1:=myPolynomial(k,r[3]);
  while r[4]="not" do
    i:=i+1;
    Print(m[i]," \c");
    nr:=SpinMatVector(A,idm[m[i]]);
    nv:=LcmMaximalVectorMat(A,v1,idm[m[i]],p1,myPolynomial(k,nr[3]));
    if Degree(nv[2])>Degree(p1) then
      v1:=nv[1];
      p1:=nv[2];
      r:=RatFormStep1J(A,v1);
    fi;
  od;
  Print("-> ",Degree(p1),"\n");
  return [v1,p1,r];
end;

##########################################################################
##
#F  FrobeniusNormalForm( <A> ) . . . . compute the rational canonical form
#F  NPFrobeniusNormalForm( <A> ) . . . compute the rational canonical form
##
##  'FrobeniusNormalForm' returns the rational canonical form  of a matrix
##  <A> and an invertible matrix P  performing the base change  (PAP^(-1)=
##  normal). It is first checked if <A> is zero or a scalar matrix,  where
##  the result is obvious.  Then  the function determines a maximal vector
##  and its minimal polynomial; after that, a recursion is applied. In the
##  second form,  the function uses the function 'NPMaximalVectorMat'.
##
##  Example:
##     gap> mat:=[ [ 0, 1, 0, 1 ],
##                 [ 0, 0, 0, 0 ],
##                 [ 0, 1, 0, 1 ],
##                 [ 1, 1, 1, 1 ] ]);;
##     gap> f:=FrobeniusNormalForm(mat);;
##     gap> PrintArray(f[1]);
##     [ [  0,  1,  0,  0 ],        This is the Frobenius normal form;
##       [  0,  0,  1,  0 ],        there are 2 diagonal blocks,
##       [  0,  2,  1,  0 ],        one of size 3 and one of size 1
##       [  0,  0,  0,  0 ] ]
##     gap> PrintAarray(f[2]);
##     [ [     2,     1,     0,     1 ],      The base change matrix
##       [     1,     3,     1,     3 ],      such that
##       [     3,     5,     3,     5 ],      f[2]*mat*f[2]^-1=f[1]
##       [   1/2,    -1,  -1/2,     0 ] ]
##
FrobeniusNormalForm:=function(mat)
  local A,A1,A2,P,i,k,step1,rest,d,piv;
  k:=DefaultFieldOfMatrix(mat);
  A:=ImmutableMatrix(k,mat);
  if A=0*A then
    #Print("#I Zero matrix\n");
    return [A,A^0,List([1..Length(A)],i->i)];
  fi;
  if IsDiagonalMat(A) and ForAll([2..Length(A)],i->A[i][i]=A[1][1]) then
    #Print("#I Scalar matrix \n");
    return [A,A^0,List([1..Length(A)],i->i)];
  fi;
  step1:=RatFormStep1J(A,MaximalVectorMat(A)[1]);
  A1:=step1[1];
  d:=Length(step1[3])-1;
  if d<Length(A) then
    piv:=[1];
    rest:=FrobeniusNormalForm(A1{[d+1..Length(A)]}{[d+1..Length(A)]});
    P:=BuildBlockDiagonalMat(IdentityMat(d,k),rest[2]);
    A2:=BuildBlockDiagonalMat(A1{[1..d]}{[1..d]},rest[1]);
    for i in rest[3] do
      Add(piv,i+d);
    od;
    return [A2,P*step1[2],piv];
  else
    return [A1,step1[2],[1]];
  fi;
end;

NPFrobeniusNormalForm:=function(mat)
  local A,A1,A2,P,i,k,step1,rest,d,piv;
  if VERSION[1]<>'4' then
    Print("#I sorry, not available in GAP3\n");
    return false;
  fi;
  k:=DefaultFieldOfMatrix(mat);
  A:=ImmutableMatrix(k,mat);
  if A=0*A then
    #Print("#I Zero matrix\n");
    return [A,A^0,List([1..Length(A)],i->i)];
  fi;
  if IsDiagonalMat(A) and ForAll([2..Length(A)],i->A[i][i]=A[1][1]) then
    #Print("#I Scalar matrix \n");
    return [A,A^0,List([1..Length(A)],i->i)];
  fi;
  step1:=RatFormStep1J(A,NPMaximalVectorMat(A)[1]);
  A1:=step1[1];
  d:=Length(step1[3])-1;
  if d<Length(A) then
    piv:=[1];
    rest:=NPFrobeniusNormalForm(A1{[d+1..Length(A)]}{[d+1..Length(A)]});
    P:=BuildBlockDiagonalMat(IdentityMat(d,k),rest[2]);
    A2:=BuildBlockDiagonalMat(A1{[1..d]}{[1..d]},rest[1]);
    for i in rest[3] do
      Add(piv,i+d);
    od;
    return [A2,P*step1[2],piv];
  else
    return [A1,step1[2],[1]];
  fi;
end;

##########################################################################
##
#F  InvariantFactorsMat( <A> ) . . . . . . . compute the invariant factors
#F  NPInvariantFactorsMat( <A> ) . . . . . . compute the invariant factors
##
##  'InvariantFactorsMat' returns the invariant factors of the matrix <A>,
##  i.e.,  the minimal polynomials of the  diagonal blocks in the rational
##  canonical form  of <A>. Thus, 'InvariantFactorsMat' also specifies the
##  rational canonical form of <A>, but without computing the base change.
##
NPInvariantFactorsMat:=function(mat)
  local A,A1,i,d,np,k,f,n,p;
  if VERSION[1]<>'4' then
    Print("#I sorry, not available in GAP3\n");
    return false;
  fi;
  k:=DefaultFieldOfMatrix(mat);
  A:=ImmutableMatrix(k,mat);
  n:=Length(A);
  if A=0*A then
    return List([1..n],i->myPolynomial(k,[-0*A[1][1],A[1][1]^0]));
  fi;
  if IsDiagonalMat(A) and ForAll([2..n],i->A[i][i]=A[1][1]) then
    p:=myPolynomial(k,[-A[1][1],A[1][1]^0]);
    return List([1..n],i->p);
  fi;
  np:=NPMaximalVectorMat(A);
  d:=Degree(np[2]);
  f:=[np[2]];
  if d=n then
    return f;
  else
    A1:=RatFormStep1(A,np[1])[1];
    Append(f,NPInvariantFactorsMat(A1{[d+1..n]}{[d+1..n]}));
    return f;
  fi;
end;

InvariantFactorsMat:=function(mat)
  local A,A1,i,d,np,k,f,n,p;
  k:=DefaultFieldOfMatrix(mat);
  A:=ImmutableMatrix(k,mat);
  n:=Length(A);
  if A=0*A then
    return List([1..n],i->myPolynomial(k,[-0*A[1][1],A[1][1]^0]));
  fi;
  if IsDiagonalMat(A) and ForAll([2..n],i->A[i][i]=A[1][1]) then
    p:=myPolynomial(k,[-A[1][1],A[1][1]^0]);
    return List([1..n],i->p);
  fi;
  np:=MaximalVectorMat(A);
  d:=Degree(np[2]);
  f:=[np[2]];
  if d=n then
    return f;
  else
    A1:=RatFormStep1(A,np[1])[1];
    Append(f,InvariantFactorsMat(A1{[d+1..n]}{[d+1..n]}));
    return f;
  fi;
end;

CheckFrobForm:=function(A,F)
  local P,k,i,pols,l,p1,p2,np;
  k:=DefaultFieldOfMatrix(A);
  P:=F[2];
  if P*A*P^(-1)<>F[1] then
    Error("base change not ok!");
  fi;
  if Length(F[3])>1 then
    pols:=[];
    Add(F[3],Length(A)+1);
    for i in [1..Length(F[3])-1] do
      p1:=F[3][i];
      p2:=F[3][i+1]-1;
      l:=ShallowCopy(F[1][p2]{[p1..p2]});
      Add(l,-l[1]^0);
      np:=myPolynomial(k,-l);
      if i>1 and QuotientRemainder(pols[i-1],np)[2]<>0*np then
        Error("divisibility not ok!");
      fi;
      Add(pols,np);
    od;
  else
    l:=ShallowCopy(F[1][Length(A)]);
    Add(l,-l[1]^0);
    pols:=[myPolynomial(k,-l)];
  fi;
  return pols;
end;

## Some test matrices; see also
##  A. Steel,  A new algorithm for the computation of  canonical forms of
##               matrices over fields, J. Symb. Comp. 24 (1997), 409-432.
##

A:=[[0,0,2,2,0,2],[2,4,2,6,0,4],[3,6,0,6,1,4]];;

bev:=TransposedMat(
[[2,0,0,0,0,0,0], [2,4,1,-1,-7,-2,-1], [0,0,1,0,0,0,0], [1,0,0,1,0,0,0],
[0,0,0,0,1,0,0], [2,1,1,-1,-5,1,-1], [1,0,1,0,0,0,1]]);

steel:=
[[-23,19,-9,-75,34,9,56,15,-34,-9], [-2,2,-1,-6,3,1,4,2,-3,0],
[4,-4,3,10,-5,-1,-6,-4,5,1], [-2,2,-1,-5,3,1,3,2,-3,0],
[0,0,0,0,2,0,0,0,0,0], [12,-12,6,33,-18,-4,-18,-12,18,0],
[-1,-3,0,2,1,0,1,1,2,1], [-26,22,-10,-83,36,10,61,18,-39,-10],
[-1,-3,0,1,1,0,2,1,2,0], [8,-12,4,27,-12,-4,-12,-7,15,0]];;

low:=Z(19)^0 *[[16,0,0,0,0,0,0,0,0,0],[5,2,0,0,0,0,0,0,0,0],
[9,6,7,0,0,0,0,0,0,0],[15,9,1,2,0,0,0,0,0,0],[7,14,8,2,9,0,0,0,0,0],
[12,3,17,5,1,12,0,0,0,0],[7,11,0,4,6,9,10,0,0,0],[8,3,15,16,17,18,18,12,0,0],
[6,3,7,12,1,12,11,14,10,0],[18,14,7,17,16,15,13,13,3,8]];;

#a:=(RandomLowerTriangularMat(1000,1000,GF(4)));;
#nma:=NeuMaximalVectorMat(a);;time;
#Degree(nma[2])=Length(SpinMatVector(a,nma[1])[2]);
#nma[2]=MinimalPolynomial(a);

myCompanionMat:=function(f)
  local n,i,mat;
  n:=Length(f)-1;
  mat:=(0*f[1])*IdentityMat(n);
  for i in [1..n-1] do
    mat[i+1][i]:=f[1]^0;
    mat[i][n]:=-f[i];
  od;
  mat[n][n]:=-f[n];
  return mat;
end;

myJordanBlock:=function(n,c)
  local a,i;
  a:=IdentityMat(n,DefaultField(c));
  for i in [1..n-1] do
    a[i][i]:=c;
    a[i+1][i]:=c^0;
  od;
  a[n][n]:=c;
  return a;
end;

NPmatrixM3:=function(n)
  local a,b,c,i;
  if n=600 then
    a:=BuildBlockDiagonalMat(myJordanBlock(300,Z(5)),
                             Z(5)*IdentityMat(300,GF(5)));
    b:=Random(GL(600,GF(5)));
    return b*a*b^-1;
  elif n=1200 then
    a:=myJordanBlock(2,Z(3));
    c:=myJordanBlock(2,Z(3));
    for i in [2..400] do
      c:=BuildBlockDiagonalMat(c,a);
    od;
    c:=BuildBlockDiagonalMat(c,Z(3)*IdentityMat(400,GF(3)));
    b:=Random(GL(1200,GF(3)));
    return b*c*b^-1;
  fi;
end;

mat1:=function(mat)
  local a,a1,b,i;
  a1:=TransposedMat(Concatenation(mat,mat));
  a:=[];
  for i in [1..Length(a1)-1] do
    Add(a,a1[i]);
  od;
  Add(a,0*a1[1]);
  b:=TransposedMat(Concatenation(TransposedMat(mat),TransposedMat(mat)));
  return Concatenation(a,b);
end;

diagmat:=function(l)
  local m,i;
  m:=l[1]*IdentityMat(Length(l));
  for i in [2..Length(l)] do
    m[i][i]:=l[i];
  od;
 return m;
end;

ddd:=diagmat([1,2,-1,0,4,3,3,4,5,6,7,-1,5,4,0,0,3,2,1]);

# Tests
test:=function(a1)
  local a;
  a:=RatFormStep1(a1,ChooseSpinVector(a1));
  a:=RatFormStep1J(a1,ChooseSpinVector(a1));
  a:=RatFormStep1Js(a1,ChooseSpinVector(a1));
  #a:=MinPolyMatLcmList(a1);
  a:=MatCyclicChainBasis(a1);
  a:=RatFormCyclicChain(a1);
  a:=CharPolyMat(a1);
  a:=InvariantFactorsMat(a1);
  a:=FrobeniusNormalForm(a1);
  a:=CheckFrobForm(a1,a);
  a:=NPFrobeniusNormalForm(a1);
  if a<>false then
    a:=CheckFrobForm(a1,a);
    a:=NPInvariantFactorsMat(a1);
  fi;
#  Print(" --> tests OK !\n");
end;

FrobTest:=function()
  local f;
  test(steel); test(bev); test(ddd);
  test(Z(4)^0*steel); test(Z(4)^0*bev); test(Z(4)^0*ddd);
  test(mat1(steel)); test(Z(29)*mat1(steel));
  test(RandomMat(15,15,Integers));
  test(RandomMat(20,20,GF(49)));
  test(RandomLowerTriangularMat(10,10,Integers));
  #test(RandomLowerTriangularMat(10,10,GF(19)));
  Print("\n--> tests OK !\n\n");
  Print("The following example is taken from Ballester-Bolinches et al.\n");
  Print("mat:=\n");
  PrintArray(bev);
  Print("MaximalVectorMat(mat);\n");
  Print(MaximalVectorMat(bev),"\n\n");
  Print("Thus, the vector [0,0,7,0,1,0,0] is maximal with\n");
  Print("minimal polynomial 6-17x+17x^2-7x^3+x^4\n\n");
  Print("CharPolyMat(mat);\n");
  Print(CharPolyMat(bev),"\n\n");
  Print("f:=FrobeniusNormalForm(mat);; PrintArray(f[1]);\n");
  f:=FrobeniusNormalForm(bev);
  PrintArray(f[1]);
  Print("Thus, f[1] is the Frobenius normal form and\n");
  Print("you can check that f[2]*matrix*f[2]^(-1)=f[1]\n\n");
  if VERSION[1]='4' then
    Print("The Neunhoeffer-Paeger test matrix M2 is obtained as follows:\n");
    Print("  LoadPackage(\"AtlasRep\");; g:=AtlasGroup(\"B\",1);");
    Print(" M2:=g.1+g.2+g.1*g.2;\n\n");
    Print("(Use NPMaximalVectorMat and NPFrobeniusNormalForm\n");
    Print(" for large matrices; these load the 'cvec' package.)\n");
  else
    Print("A further test matrix from Steel:\n");
    PrintArray(steel);
  fi;
end;

FrobHelp:=function(f)
  local i,l,s1,s2,s2a,s3,s4,s5,s5a,s6,s7,s7a,s8,s9,s10,s11,s12,s13,s14,s15,
        s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30;
  if f=MaximalVectorMat or f=NPMaximalVectorMat then
s1:="";
s2:="NPMaximalVectorMat( <A> ) . . . . . . . . . . . compute maximal vector";
s3:="MaximalVectorMat( <A> ) . . . . . . . . . . . . compute maximal vector";
s4:="'NPMaximalVectorMat'  returns a maximal vector of the matrix <A>, that";
s5:="is, a vector whose minimal polynomial is that of <A>.  This is done by";
s6:="first invoking the Neunhoeffer-Praeger algorithm to compute the latter";
s7:="(for this purpose, the package 'cvec' is loaded),  and then repeatedly";
s8:="spinning up vectors until a maximal one is found. This in turn is done";
s9:="by running through a similar procedure as in 'RatFormCyclicChain' (but";
s10:="immediately  stopping  this  procedure  once a cyclic  subspace of the";
s11:="correct degree is found).";
s12:="";
s13:="Example:  ";
s14:=" gap> A:=[ [ 0, 1, 0, 1 ],";
s15:=" gap>      [ 0, 0, 0, 0 ],";
s16:=" gap>      [ 0, 1, 0, 1 ],";
s17:=" gap>      [ 1, 1, 1, 1 ] ];;";
s18:=" NPMaximalVectorMat(A);";
s19:=" #I Degree of minimal polynomial is 3 ";
s20:=" [ [ 1, 0, 0, 0 ], x^3-x^2-2*x ]";
s21:="";
s22:="If one does  not want  to rely  on the  Neunhoeffer-Praeger algorithm,";
s23:="then one can also use the function 'MaximalVectorMat' which implements";
s24:="this directly, but is slower (about 5 times for larger matrices).";
    l:=[s1,s2,s3,s1,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,
        s19,s20,s21,s22,s23,s24,s1];
    for i in l do Print(i,"\n");od;
  elif f=FrobeniusNormalForm or f=NPFrobeniusNormalForm then
s1:="";
s2:="FrobeniusNormalForm( <A> ) . . . . compute the rational canonical form";
s3:="NPFrobeniusNormalForm( <A> ) . . . compute the rational canonical form";
s4:="";
s5:="'FrobeniusNormalForm' returns the rational canonical form  of a matrix";
s6:="<A> and an invertible matrix P  performing the base change  (PAP^(-1)=";
s7:="normal form).  It is first checked if  <A> is zero or a scalar matrix,";
s8:="where the result  is obvious.  Then  a maximal vector  and its minimal";
s9:="polynomial are determined;  after that, a recursion is applied. In the";
s11:="second form,  the function uses the function 'NPMaximalVectorMat'.";
s12:="";
s13:="Example:";
s14:="   gap> mat:=[ [ 0, 1, 0, 1 ],";
s15:="               [ 0, 0, 0, 0 ],";
s16:="               [ 0, 1, 0, 1 ],";
s17:="               [ 1, 1, 1, 1 ] ];;";
s18:="   gap> f:=FrobeniusNormalForm(mat);;";
s19:="   gap> PrintArray(f[1]);";
s20:="   [ [  0,  1,  0,  0 ],        This is the Frobenius normal form;";
s21:="     [  0,  0,  1,  0 ],        there are 2 diagonal blocks,";
s22:="     [  0,  2,  1,  0 ],        one of size 3 and one of size 1";
s23:="     [  0,  0,  0,  0 ] ]";
s24:="   gap> PrintAarray(f[2]);";
s25:="   [ [     2,     1,     0,     1 ],      The base change matrix";
s26:="     [     1,     3,     1,     3 ],      such that";
s27:="     [     3,     5,     3,     5 ],      f[2]*mat*f[2]^-1=f[1]";
s28:="     [   1/2,    -1,  -1/2,     0 ] ]";
s29:="";
    l:=[s1,s2,s3,s4,s5,s6,s7,s8,s9,s11,s12,s13,s14,s15,s16,s17,s18,s19,
        s20,s21,s22,s23,s24,s25,s26,s27,s28,s29];
    for i in l do Print(i,"\n");od;
elif f=SpinMatVector then
s1:="";
s2:="SpinMatVector( <A>, <v> ) . . . . . .  spin up a vector under a matrix";
s3:="'SpinMatVector' computes  the  smallest subspace containing the vector";
s4:="<v>  and invariant under the matrix  <A>.  The  output is a quadruple.";
s5:="The first component contains a  basis in row echelon form,  the second";
s6:="the  matrix  with  rows v, Av, A^2v, ..., A^(d-1)v, the third  one the";
s7:="coefficients of the minimal polynomial of <v>  (of degree d),  and the";
s8:="last one the positions of the pivots of the first component.";
s9:="";
s10:="Examples:";
s11:="   gap>  A:=[[2,0,0],[0,-1,0],[0,0,1]];";
s12:="   gap>  v:=[1,1,0];";
s13:="   gap>  SpinMatVector(A,v);";
s14:="   [ [ [ 1, 0, 0 ], [ 0, 1, 0 ] ], ";
s15:="     [ [ 1, 1, 0 ], [ 2, -1, 0 ] ], ";
s16:="     [ -2, -1, 1 ], [ 1, 2 ] ]    So v has minimal polynomial x^2-x-2.";
s17:="   gap>  SpinMatVector(A,[1,1,1]);";
s18:="   [ [ [ 1, 0, 0 ], [ 0, 1, 0 ], [ 0, 0, 1 ] ], ";
s19:="     [ [ 1, 1, 1 ], [ 2, -1, 1 ], [ 4, 1, 1 ] ], ";
s20:="     [ 2, -1, -2, 1 ], [ 1, 2, 3 ] ]  minimal polynomial x^3-2x^2-x+2.";
    l:=[s1,s2,s1,s3,s4,s5,s6,s7,s8,s9,s11,s12,s13,s14,s15,s16,s17,s18,s19,
        s20,s1];
    for i in l do Print(i,"\n");od;
elif f=RatFormCyclicChain then
s1:="";
s2:="RatFormCyclicChain( <A> ) . . . . . compute complete chain of relative";
s3:=". . . . . . . . . . . . cyclic subspaces (with additional information)";
s4:="";
s5:="'RatFormCyclicChain'  repeatedly applies  'RatFormStep1J' to compute a";
s6:="chain of cyclic subspaces. The output is a triple [A1,P,piv]  where A1";
s7:="is in block triangular shape (where each diagonal block is a companion";
s8:="matrix), P is a base change matrix (such that  PAP^(-1) = A1), and piv";
s9:="contains the minimal polynomials of the blocks. The function checks if";
s10:="<A> is the zero or a scalar matrix, where the result is obvious.";
s11:="";
s12:="Example:";
s13:=" gap> A:=[ [ 0, 1, 0, 1 ],";
s14:=" gap>      [ 0, 0, 1, 0 ],";
s15:=" gap>      [ 0, 1, 0, 1 ],";
s16:=" gap>      [ 1, 1, 1, 1 ] ];;";
s17:=" gap> PrintArray(RatFormCyclicChain(A)[1])";
s18:=" [ [     0,     1,     0,     0 ],    There are 2 diagonal blocks";
s19:="   [     0,     0,     1,     0 ],    but (because of the entry 1/2)";
s20:="   [     0,     3,     1,     0 ],    the extension is not split.";
s21:="   [   1/2,     0,     0,     0 ] ]   ";
s22:=" (Compare with 'FrobeniusNormalForm(A)[1]', with blocks of size 3,1.)";
    l:=[s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,
        s20,s21,s22,s1];
    for i in l do Print(i,"\n");od;
elif f=CharPolyMat then
s1:="";
s2:="CharPolyMat( <A> ) . . . . . .  computes the characteristic polynomial";
s3:="";
s4:="'CharPolyMat' returns the characteristic polynomial of the matrix <A>,";
s5:="using a chain of  relative cyclic subspaces.   (This is an alternative";
s5a:="to the standard GAP function 'CharacteristicPolynomial'.)";
s6:="";
s7:="Example:";
s8:="   gap> CharPolyMat([ [ 2,  2, 0, 1, 0,  2, 1 ],";
s9:="                      [ 0,  4, 0, 0, 0,  1, 0 ],";
s10:="                      [ 0,  1, 1, 0, 0,  1, 1 ],";
s11:="                      [ 0, -1, 0, 1, 0, -1, 0 ],";
s12:="                      [ 0, -7, 0, 0, 1, -5, 0 ],";
s13:="                      [ 0, -2, 0, 0, 0,  1, 0 ],";
s14:="                      [ 0, -1, 0, 0, 0, -1, 1 ] ]);";
s15:="   -x^7+11*x^6-50*x^5+122*x^4-173*x^3+143*x^2-64*x+12";
    l:=[s1,s2,s3,s4,s5,s5a,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s1];
    for i in l do Print(i,"\n");od;
elif f=GcdCoprimeSplit then
s1:="";
s2:="GcdCoprimeSplit( <a>, <b> ) . . . . . . . coprime factorisation of lcm";
s3:="'GcdCoprimeSplit' computes a divisor <a1> of the polynomial <a>  and a ";
s4:="divisor <b1> of the polynomial <b> such that <a1> and <b1> are coprime ";
s5:="and the lcm of <a>, <b> is <a1>*<b1>.  This is based on Lemma 5 in ";
s6:="";
s7:="K. Bongartz,  A direct approach to the rational normal form,  preprint";
s8:="available at arXiv:1410.1683.";
s9:="";
s10:="(Note that it does not use the prime factorisation of polynomials  but ";
s11:="only gcd computations.)  ";
s12:="";
s13:="Example:  ";
s14:="  gap> a:=x^2*(x-1)^3*(x-2)*(x-3);";
s15:="  x^7-8*x^6+24*x^5-34*x^4+23*x^3-6*x^2";
s16:="  gap> b:=x^2*(x-1)^2*(x-2)^4*(x-4);";
s17:="  x^9-14*x^8+81*x^7-252*x^6+456*x^5-480*x^4+272*x^3-64*x^2";
s18:="  gap> GcdCoprimeSplit(a,b);";
s19:="  [ x^5-4*x^4+5*x^3-2*x^2,                    # the (monic) gcd";
s20:="    x^6-6*x^5+12*x^4-10*x^3+3*x^2,            # a1";
s21:="    x^5-12*x^4+56*x^3-128*x^2+144*x-64 ]      # b1";
    l:=[s1,s2,s1,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,
        s18,s19,s20,s21,s1];
    for i in l do Print(i,"\n");od;
  elif f=RatFormStep1J or f=RatFormStep1 then
s1:="";
s2:="RatFormStep1J( <A>, <v> ) . . . . . . . . compute cyclic subspaces and";
s3:=". . . . . . . . . . . . . . . . . . . . . . . . . . perform base chain";
s2a:="RatFormStep1Js( <A>, <v> ) . . . strong form with invariant complement";
s4:="";
s5:="'RatFormStep1J' spins up a vector  <v> under a  matrix  <A>,  computes";
s6:="a complementary subspace  (using  Jacob's construction),  and performs";
s7:="the base change. The output is a quadruple  [A1,P,pol,str] where A1 is";
s7a:="the new matrix,  P is the base change,  pol is  the minimal polynomial";
s8:="and str is either 'split' or 'not', according to whether the extension";
s9:="is split or not. The second form repeatedly applies 'RatFormStep1J' in";
s10:="order to obtain an invariant complement.";
s11:="Example:";
s12:=" gap> v:=[ 1, 1, 1, 1 ];;";
s13:=" gap> A:=[ [ 0, 1, 0, 1 ],";
s14:=" gap>      [ 0, 0, 1, 0 ],";
s15:=" gap>      [ 0, 1, 0, 1 ],";
s16:=" gap>      [ 1, 1, 1, 1 ] ];;";
s17:=" gap> PrintArray(RatFormStep1J(A,v)[1])";
s18:=" [ [  0,  1,  0,  0 ],    There are 2 diagonal blocks but";
s19:="   [  0,  0,  1,  0 ],    (because of the (4,1)-entry 1)";
s20:="   [  0,  3,  1,  0 ],    the extension is not split.";
s21:="   [  1,  0,  0,  0 ] ]   ";
s22:=" gap> PrintArray(RatFormStep1Js(A,v)[1])";
s23:=" [ [  0,  1,  0,  0 ],    Now we actually see that";
s24:="   [  0,  0,  1,  0 ],    the matrix is cyclic.";
s25:="   [  0,  0,  0,  1 ],    ";
s26:="   [  0,  0,  3,  1 ] ]   ";
    l:=[s1,s2,s3,s2a,s4,s5,s6,s7,s7a,s8,s9,s10,s1,s11,s12,s13,s14,s15,s16,
                              s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s1];
    for i in l do Print(i,"\n");od;
elif f=InvariantFactorsMat or f=NPInvariantFactorsMat then
s1:="";
s2:="InvariantFactorsMat( <A> ) . . . . . . . compute the invariant factors ";
s3:="NPInvariantFactorsMat( <A> ) . . . . . . compute the invariant factors";
s4:="'InvariantFactorsMat' returns the invariant factors of the matrix <A>,";
s5:="i.e.,  the minimal polynomials of the  diagonal blocks in the rational ";
s6:="canonical form  of <A>. Thus, 'InvariantFactorsMat' also specifies the";
s7:="rational canonical form of <A>, but without computing the base change.";
s8:="The second version uses the Neunhoeffer-Praeger algorithm.";
s9:="Example:";
s10:="   gap> NPInvariantFactorsMat([ [ 2,  2, 0, 1, 0,  2, 1 ],";
s11:="                                [ 0,  4, 0, 0, 0,  1, 0 ],";
s12:="                                [ 0,  1, 1, 0, 0,  1, 1 ],";
s13:="                                [ 0, -1, 0, 1, 0, -1, 0 ],";
s14:="                                [ 0, -7, 0, 0, 1, -5, 0 ],";
s15:="                                [ 0, -2, 0, 0, 0,  1, 0 ],";
s16:="                                [ 0, -1, 0, 0, 0, -1, 1 ] ]);";
s17:="   #I Degree of minimal polynomial is 4 (2,2,3,3,)";
s18:="   #I Degree of minimal polynomial is 2 ";
s19:="   [ x^4-7*x^3+17*x^2-17*x+6, x^2-3*x+2, x-1 ]";
    l:=[s1,s2,s3,s1,s4,s5,s6,s7,s8,s1,s9,s10,s11,s12,s13,s14,
                                        s15,s16,s17,s18,s19,s1];
    for i in l do Print(i,"\n");od;
  else
   Print("sorry help not available\n");
  fi;
end;
