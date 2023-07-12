needsPackage "MonodromySolver";

--R: coeffs to be a list of coefficients of the taylor series, m to be degree of numerator, n to be degree of denominator
--M: none
--E: returns a list (p(t), q(t)) that is the Pade approximation

convertToPade=(coeffs, m, n)->{
    assert(n+m<=length(coeffs));
    print coeffs;
    print m;
    print n;
    --alright, so problem is if power series doesn't have high enough terms, 
    --then bottomMat is just the zero matrix
    bottomMat=map(CC^n, CC^(n+1), (i,j)-> sub(coeffs_(m+1+i-j),CC));
    denomQ=flatten(entries(transpose(gens(kernel(bottomMat)))));
    
    topMat=map(CC^(m+1), CC^(n+1), (i,j)->
        (if (i<j) then return 0 else return sub(coeffs_(i-j), CC);)
    );

    numP=flatten(entries((topMat*vector(denomQ))));

    return {numP, denomQ};
};

--R: F a polysystem in C[t,\vec(x)], t0 a CC and sol a list such that F_t(x)=0, ord is degree of expansion
--M: none
--E: returns a list of power series for F around t, x

getPSApprox=(F, t0, sol, ord)->{
    curOrd=0;
    curPower=sol;    
    
    --run this algo until have a polynomial of degree ord
    while curOrd<ord do(
    
        --set up bold(A) and bold(-F(z))
        A=evaluate(jacobian(F), point{curPower});
        b=-1*evaluate(F, point{curPower});
    
        
        if A==0 or b==0 then break;
        
        apow=0;
        bpow=0;
        
        --gets rid of trivial parts of system
        while A%t ==0 do(
            A=A//t;
            apow=apow+1;
        );
        
        while b%t==0 do(
            b=b//t;
            bpow=bpow+1;
        );
        
        
        --want to iterate until get a t^{curMaxOrder+1}
        --M2 returns a degree of a constant to be -infinity for some reason
        iterateUntil;
        
        --if max(degree(matrix{curPower}))<0 then iterateUntil=0 else iterateUntil=max(degree(matrix{curPower}));
        iterateUntil=curOrd;
        
        --sets the starting power of x_0
        bmina=bpow-apow;
        assert(bmina>=0);
        
        
        indexer=0;
        aList={};
        xList={};
        
        print indexer;
        print (iterateUntil+1);
        while bmina<=(iterateUntil+1) do (
            aList=append(aList, A%t);
            A=A//t;
            
            nextb=b%t;
            b=b//t;
            print("here");
            rhsStuff=nextb;
            for i from 1 to indexer do rhsStuff=rhsStuff-(aList_indexer)*(xList_(indexer-i));
          
            nextX=solve(sub(aList_0,CC), sub(rhsStuff,CC), MaximalRank=>true);
            xList=append(xList,nextX);
            
            curPower=curPower+apply(flatten(toList(entries(nextX))), i->i*t^bmina);
            bmina=bmina+1;
            indexer=indexer+1;
        );
         curOrd=iterateUntil+1;
         --print curOrd;
         --print curPower;
    
    );
    return curPower;
};

--R: a portal CC ti=listPortals_i and a solution (list) xi to the system F_xi, F a polySystem
--M: none
--E: returns an L/M Pade approximation that approximates F near (xi,ti)

getApprox=(F, xi, i, listOfPortals)->{
    ti = (listOfPortals_i)_CC;
    
    psApprox=getPSApprox(F, ti, xi, L+M);
    
    --refine the psApproximation, yes indeed does something
    for times from 0 to 0 do psApprox=getPSApprox(F, ti, psApprox, L+M);
    
    
    -*
    --turns list of polynomials into list of coefficients
    coeffs={};
    psApprox=matrix{psApprox};
    for k from 0 to L+M do (
        for indexer from 0 to 
    
        coeffs=append(coeffs, entries(transpose(psApprox%t)));
        psApprox=psApprox//t;
    
    );
    no, this is very annoying to iterate through 
    *-
    
    temp=1;
    for k from 1 to L+M do temp=temp+t^k;
    psApprox=append(psApprox, temp);
    coeffMatrix=(coefficients(matrix{psApprox}))_1;
    --coeffMatrix is a matrix whose columns give coefficients of the power series approximations
    --needed to add temp to ensure that zero coefficients show up in the matrix
    --only "bad" things is that bottom of column gives constant term, so when grab a column, need to reverse it
    
    listOfPades={};
    
    for k from 0 to F.NumberOfPolys-1 do (
        listOfPades=append(listOfPades, convertToPade(reverse(coeffMatrix_k), L, M));
    
    );
    
};
L=2;
M=1;


CC[t][x,y];
F=polySystem({2*t^2+t*x-y+1, x^3-4*t^2+t*y+2*t-1});
psApprox=getPSApprox(F,  0, {1+0*t,1+0*t}, 3)








