needsPackage "MonodromySolver";

--R: Pade is a list of pairs {num, denom}; basePt is the t value the approx is supposed to be centered around, 
    --newT is the value to plug into the approximation
--M: none
--E: returns a list of evaluations

evaluateAt=(Pade, basePt, newT)->{
    evals={};
    for poly in Pade do (
        topEval=0;
        indexer=0;
        for nums in poly_0 do(
            topEval=topEval+nums*(newT-basePt)^indexer;
            indexer=indexer+1;
        ); 
        bottomEval=0;
        indexer=0;
        for denoms in poly_1 do(
            bottomEval=bottomEval+denoms*(newT-basePt)^indexer;
            indexer=indexer+1;
        ); 
        evals=append(evals, 1.0*topEval/bottomEval);
    );
    return evals;

};

--R: coeffs to be a list of coefficients of the taylor series, m to be degree of numerator, n to be degree of denominator
--M: none
--E: returns a list (p(t), q(t)) that is the Pade approximation

convertToPade=(coeffs, m, n)->{
    assert(n+m<=length(coeffs));
    --alright, so problem is if power series doesn't have high enough terms, 
    --then bottomMat is just the zero matrix
    bottomMat=map(CC^n, CC^(n+1), (i,j)-> sub(coeffs_(m+1+i-j),CC));
    denomQ=(entries(transpose(gens(kernel(bottomMat)))))_0;
    
    --print("bottom map is", bottomMat);
    --print("entire kernel is", entries(gens(kernel(bottomMat))));
    --print("denomQ is thus ", denomQ);
    
    topMat=map(CC^(m+1), CC^(n+1), (i,j)->
        (if (i<j) then return 0 else return sub(coeffs_(i-j), CC);)
    );

    --print("topMat is ",topMat);
    --print("numP is ", numP);
    
    numP=flatten(entries((topMat*vector(denomQ))));

    print("Pade is ", {numP, denomQ});
    return {numP, denomQ};
};

--R: F a polysystem in C[t,\vec(x)], t0 a CC and sol a list such that F_t(x)=0, ord is degree of expansion
--M: none
--E: returns a list of power series for F around t, x
--:note: the t's that show up in curPower are really t+t0 's

getPSApprox=(F, t0, sol, ord)->{
    --shift PS approx so that family is centered around t0
    --while not stricly necessary, does indeed provide better approximations
    newF={};
    for func in entries(F.PolyMap) do (
        newF=append(newF, sub((func_0), {t=>t+t0}));
    );
    newF=polySystem(newF);
    
    curOrd=0;
    curPower=sol;    
    
    --run this algo until have a polynomial of degree ord
    while curOrd<ord do(
    
        --set up bold(A) and bold(-F(z))
        A=evaluate(jacobian(newF), point{curPower});
        b=-1*evaluate(newF, point{curPower});
        --print("start:");
        --print(curPower);
        --print(A);
        --print(b);
        
        if A==0 or b==0 then break;
        
        apow=0;
        bpow=0;
        
        --gets rid of trivial parts of system
        while A%t ==0 do(
            A=A//t;
            apow=apow+1;
            if A==0 then break;
        );
        
        while b%t==0 do(
            b=b//t;
            bpow=bpow+1;
            if b==0 then break;
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
        
        while bmina<=(curOrd+1) do (
            aList=append(aList, A%t);
            A=A//t;
            
            nextb=b%t;
            b=b//t;
            rhsStuff=nextb;
            for i from 1 to indexer do rhsStuff=rhsStuff-(aList_indexer)*(xList_(indexer-i));
          
            --assert(determinant(sub(aList_0,CC))!=0);
            nextX=solve(sub(aList_0,CC), sub(rhsStuff,CC), Invertible=>true, MaximalRank=>true);
            --print("nextX is ", nextX);
            xList=append(xList,nextX);
            
            curPower=curPower+apply(flatten(toList(entries(nextX))), i->i*t^bmina);
            bmina=bmina+1;
            indexer=indexer+1;
            
            --print curPower;
        );
         --curOrd=iterateUntil+1;
         curOrd=curOrd+1;
    
    );
    print curPower;
    return curPower;
};

--R: a portal CC ti=listPortals_i and a solution (list) xi to the system F_xi, F a polySystem
--M: none
--E: returns an L/M Pade approximation that approximates F near (xi,ti)

getApprox=(F, xi, i, listOfPortals)->{
    ti = (listOfPortals_i)_CC;
    
    psApprox=getPSApprox(F, ti, xi, L+M);
    
    --refine the psApproximation, yes indeed does something
    for times from 0 to -1 do psApprox=getPSApprox(F, ti, psApprox, L+M);
    
    
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
        listOfPades=append(listOfPades, convertToPade(reverse(entries(coeffMatrix_k)), L, M));
    
    );
    return listOfPades;
    
};

-*
L=4;
M=3;


CC[t][x,y];
F=polySystem({x^2+y^2-t,x^3-y^2+x});
--getApprox=(F, xi, i, listOfPortals)
padeApprox=getApprox(F, {0.544,0.839+0*t}, 0, {1})


evaluateAt(padeApprox, 1,1)
*-

-*
L=4;
M=1;


CC[t][x];
--F=polySystem({x^3-3*x-t});
F=polySystem({x^3-3*x-(t+18)});
--getApprox=(F, xi, i, listOfPortals)
padeApprox=getApprox(F, {3+0*t}, 0, {0});


evaluateAt(padeApprox, 18,18)
*-

-*
L=2;
M=1;


CC[t][x];
--F=polySystem({x^3-3*x-t});
F=polySystem({x^3-3*x-t});
--getApprox=(F, xi, i, listOfPortals)
padeApprox=getApprox(F, {3+0*t}, 0, {18});


evaluateAt(padeApprox, 18,18)
*-

-*
L=5;
M=1;


CC[t][x];
F=polySystem({x^3-3*x-t});
--getApprox=(F, xi, i, listOfPortals)
padeApprox=getApprox(F, {-1*sqrt(3)+0*t}, 0, {0});


evaluateAt(padeApprox, 0,0)

*-



-*
L=2;
M=1;


CC[t][x,y];
F=polySystem({2*t^2+t*x-y+1, x^3-4*t^2+t*y+2*t-1});
--getApprox=(F, xi, i, listOfPortals)
padeApprox=getApprox(F, {1+0*t,1+0*t}, 0, {0});


evaluateAt(padeApprox, 0,0)
*-

-*
L=2;
M=1;


CC[t][x,y];
F=polySystem({x^2+y^2-t,x^3-y^2+t*x});
--getApprox=(F, xi, i, listOfPortals)
padeApprox=getApprox(F, {0.544,0.839+0*t}, 0, {1})


evaluateAt(padeApprox, 1,1)
*-





