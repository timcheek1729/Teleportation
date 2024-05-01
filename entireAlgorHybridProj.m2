--works for multivariate, multiparameter systems of functions
--has assertion check to ensure seed solution pair is correct
--does forward error check as well, although prob not needed
--now takes random portals
--does variation of complete graph implementation-ish from Duff paper
--now have portals drawn from unit circle centered at 0.5 to make edges more symmetric
--now does [L/M] Pade approximation
--cut dfs off, i.e., can only ever jump once for a given (sol, t0) pair
--no, just break if a jump to a portal finds an old solution 
    --(still move toward enpoint by only considering jumping to points that decrease distance to endpoint
--finally actually only track solutions that haven't been tracked yet
--now if can't jump all the way to the end (not enough portals), just straight line homotopy to the destination
--tree is not yet implemented (and won't be, is too much prepocessing)(now prune list we check each jump)
--cyclic 3 roots now takes only around 20 seconds to run
--if a point "fails" (i.e., can't jump forward from it), is thrown out (speeds up later path trackings over same line reduction)
--now has function that finds one initial solution to your desired system


needsPackage "NumericalAlgebraicGeometry";
needsPackage "MonodromySolver";
--contains list of vertices, ''pointers'' to triangles in it
--.Vertices is list of vertices 
--AT, BT, CT, nT pointers to 4 smaller triangles (sharing vertices with old A, B, C, and none)
Triangle=new Type of MutableHashTable;

--contains a triple (which is its xyz coordinates), as well as a ''valid'' boolean (to denote if thrown out or not)
--now also cobtain their index
Vertex=new Type of MutableHashTable;

--Macualay2 doesn't have amortizes O(1) push back, so I implement it myself *sigh*
--contains .theLength for USED length, and .theCnts for its contents
--used @ instead of [], _, or # to grab its elements
cppVector=new Type of MutableHashTable;

------------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------------
--BELOW IS A COLLECTION OF ASSORTED METHODS
------------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------------

--taken from MonodromySolver
old'random'Type = lookup(random,Type)
random Type := o -> R -> (
    if class R === ComplexField then (
	exp(2 * pi * random RR * ii)
	) 
    else (old'random'Type o) R
    ) 

--rounds list of complex numbers to n decimal places
--used for storing approx zeroes/params in hashtable w/o unnecessary overlap
--ERROR: one of n, a is a NotANumber
rounds=method();
rounds:=(n,listL)->{
    if length(listL)<=0 then (print("n is", n, "the list is", listL); assert(false););
    r={};
    for num in listL do(
        a=realPart(num);
        b=imaginaryPart(num);
        a=sub(a,RR);
        b=sub(b,RR);
        r=append(r, round(n, a)+round(n, b)*ii);
    );
    
    return r;
};

--R: to lists of complex numbers
--M: none
--E: returns norm of their difference

getNorm=(list1, list2)->{
    s:=0;
    for x in (list1-list2) do (
        s=s+(realPart(x))^2+(imaginaryPart(x))^2;
    );
    return sqrt(s);
};

--given a vertex, turns it into a complex number via steroegraph projection sigma_(0:1)
--potentially just want to store this in its own table? to avoid much repeated computation
getC=method();
getC(Vertex):=(v)->{
    if v.Points == {0,0,1} then (
        --return (1,0);
        return ((2*0.149)/ (1-0.99))+ ((2*0.005)/(1-0.99))*ii;--is a point near the top
    ) else (
        --steroegraphic projection down to plane tangest to south pth
        x:= (v.Points)#0;
        y:= (v.Points)#1;
        z:= (v.Points)#2;
        return ((2*x)/ (1-z))+ ((2*y)/(1-z))*ii;
        --very much need first coordinate to be greater than 1 at some point, which does happen near the top
    );
};

--R: need x^2+y^2+z^2=1, where triple=(x,y,z)
--M: none
--E: returns the angle betwen the z axis and the xy-plane (NOT from the plane up to the z-axis, but DOWN from the axis to the plane)
arccos=(triple)->{
    x:=triple_0;
    y:=triple_1;
    z:=triple_2;
    if z==0 then (
        return pi/2;
    ) else (
        return atan2(sqrt(x*x+y*y),z);
    );
};

------------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------------
--BELOW is all of the Pade, power series stuff 
------------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------------
--R: pade a list of pairs (numPade, denomPade)
--M: none
--E: returns distance to the nearest pole
--note: denomPade must be linear!! otherwise finding its zeroes (i.e., poles of Pade) becomes nontrivial

getD=(pade)->{
    --circle is of radius 1, so is largest raidus of convergence we neet to consider anyway
    minD=1;
    for func in pade do (
        denom=func_1;
        --checks to make sure denom is indeed linear
        assert(length(denom)==2);
        
        --if coefficient on t is basically 0, then no pole
        if norm(denom_1)<0.01 then (
            minD=1;
            break;
        ) else (
            dfromCenter=norm((-1.0*denom_0)/(denom_1));
            if dfromCenter<minD then minD=dfromCenter;
        );
    );
    return minD;
};

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
    
    if M==1 then(
        --just manually find trivial kernel, should be fast
        denomQ={sub(coeffs_(m+1-1), CC), sub(-1*coeffs_(m+1),CC)};
    ) else (
        bottomMat=map(CC^n, CC^(n+1), (i,j)-> sub(coeffs_(m+1+i-j),CC));
        --denomQ=(entries(transpose(gens(kernel(bottomMat)))))_0;
        --below is hopefully faster
        denomQ= flatten(entries(transpose((numericalKernel(bottomMat), Tolerance => 1e-3))#0));
    );
    
    topMat=map(CC^(m+1), CC^(n+1), (i,j)->
        (if (i<j) then return 0 else return sub(coeffs_(i-j), CC);)
    );

    --print("topMat is ",topMat);
    --print("numP is ", numP);
    
    numP=flatten(entries((topMat*vector(denomQ))));

    --print("Pade is ", {numP, denomQ});
    return {numP, denomQ};
};

--R: F a polysystem in C[t,\vec(x)], t0 a CC and sol a list such that F_t(x)=0, ord is degree of expansion
--M: none
--E: returns a list of power series for F around t, x
--:note: the t's that show up in curPower are really t+t0 's

getPSApprox=(F, t0, sol, ord)->{
    --shift PS approx so that family is centered around t0
    --while not stricly necessary, does indeed provide better approximations
    newF:={};
    t:=(parameters(F))_0;
    for func in entries(F.PolyMap) do (
        --just subs in t+t0 in for t
        --newF=append(newF, sub((func_0), {((parameters(F))_0) => (((parameters(F))_0)+t0)}));
        newF=append(newF, sub((func_0), {t=>t+t0}));
    );
    newF=polySystem(newF);
    
    curOrd:=0;
    --to ensure elements of sol lie in CC[t]
    curPower:=apply(sol, i-> i+0*t);
    
    --run this algo until have a polynomial of degree ord
    while curOrd<ord do(
    
        --set up bold(A) and bold(-F(z))
        A=evaluate(jacobian(newF), point{curPower});
        b=-1*evaluate(newF, point{curPower});
        
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
            nextX=solve(sub(aList_0,CC), sub(rhsStuff,CC), ClosestFit=>true);
            xList=append(xList,nextX);
            
            curPower=curPower+apply(flatten(toList(entries(nextX))), i->i*t^bmina);
            bmina=bmina+1;
            indexer=indexer+1;
        );
         curOrd=curOrd+1;
    
    );
    return curPower;
};

------------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------------
--BELOW are functions that run locally at a point
------------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------------

--R: a portal CC ti=listPortals_i and a solution (list) xi to the system F_xi, F a polySystem
--M: none
--E: returns an L/M Pade approximation that approximates F near (xi,ti)
--NOTE: FINISH HERE: assumes that (z:1)\mapsto z and sigma_(0:1)\comp \psi: CP\ra C coincide (or are close)

getApprox:=(F, xi, i, ti)->{
    m;
    one;
    --so not at north pole
    try( m=max(abs(ti),1);
    ) then (
        ti= ti/m; 
        one= 1/m;
    ) else (
        ti=1; 
        one=0;
    );
    
    newF:={};
    --t:=(parameters(F))_0;--don't think I need this here anymore
    for func in entries(F.PolyMap) do (
        --CHECK HERE: am NOT doing any reshifting of t are anything, which I did before
        --SOLVED: I actually am reshifting t, it is just that this is happenind (as before) in the getPSApprox function
        newF=append(newF, sub((func_0), {s=>one}));
        --ERROR: sometimes have "error: baseName: no base name available". should be solved, previous function was accidently overwriting s with a number
    );

    newF=polySystem(newF);
    --print ("this is newF", peek newF, ring(newF));
    
    --scaling should NOT change solution set, since are multiplying through by the scalar 1/m
    psApprox:=getPSApprox(newF, ti, xi, L+M);
    use ring(psApprox_0);--CHECK: this is new to avoid errors below! may break something later??
    
    --refine the psApproximation, yes indeed does something
    for times from 1 to numGauss do psApprox=getPSApprox(F, ti, psApprox, L+M);
    
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
    
    --print("here is list of ps approx",psApprox);
    --for x in psApprox do print hash ring(x);
    
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

--R: a function fti approximating around xi0, ti0; and a new parameter value tj=listOfPortals_j; polySystem F
   --ti is a CC, xi is a list
   --index=(a,b) such that listOfPortals=tableLOP_a_b, and (tableSols_(index_0)_(index_1))=portals
   --NOPE, not i0, j are actual C coords corr points on sphere
--M: if f approximates F_tj well, then appends Q_tj with new solution to F_tj 
--E: returns (bool, CC) pair.
    --if f does approximates F_tj well and finds a newSolution, then returns (true, newSolution)
    --otherwise false, with an integer indicator for whether newton errors, f a bad approx, or sol already known
--note: indeed checks how far xj is from initGuess as you keep doing Newton's, and also checks fwdError at end
--note: slight discrepancies between this and what's written in the paper, need to edit

inRGA=(F, fti, i0, j, indexP)-> {
    --tj=tableVertexIndexList#(indexP_0)#(indexP_1))@j;
    --ti=tableVertexIndexList#(indexP_0)#(indexP_1))@i0;
    ti:=i0;
    tj:=getC((tableVertexIndexList#(indexP_0)#(indexP_1))@j);
    
    m;
    one;
    --so not at north pole
    try( m=max(abs(tj),1);
    ) then (
        ti= tj/m; 
        one= 1/m;
    ) else (
        ti=1; 
        one=0;
    );
    
    specF=specializeSystem(point{{tj, one}}, F);
    
    --initGuess=flatten(toList(entries(evaluate(fti,point{{tj}}))));
    initGuess=evaluateAt(fti, ti, tj);
    xj=point{initGuess};
    try(
        
        for i from 1 to numNewton do (
            xj=newton(polySystem(specF),xj);
            if getNorm(initGuess, xj.Coordinates) >= epsilon then (
                --print("jump failed--newton bounced");
                return (false,1);
            );
        
        );
    ) then (
        --ERROR: sometimes have error here, in that "encounted values for 2 variables, but expected 3". Should be solved now, added ", one"
        fwdError=norm(flatten(toList(entries(evaluate(polySystem(specializeSystem(point{{tj, one}}, F)), xj)))));
        --print fwdError;
        if (getNorm(initGuess, xj.Coordinates) < epsilon) and (fwdError<fwdErrB) then (
        
            newSol=rounds(roundTo,xj.Coordinates);
            try(--because when adding smaller triangles, tableSols isn't automatically extended
                if member(newSol, (tableSols_(indexP_0)_(indexP_1))#j) then ( return (false, -1); );
            ) else (
                (tableSols_(indexP_0)_(indexP_1))#j=set{};
            );
            (tableSols_(indexP_0)_(indexP_1))#j=(tableSols_(indexP_0)_(indexP_1))#j +set{newSol}; --adds xi solution to ti
            return (true, newSol);
        
        ) else (
            print("jump failed--fwd error too big");
            return (false, 1);
        );
        
    ) else (
        return (false,0);
    );
};


  
--R: an (xi,listOfPortals_i) solution pair to the family/polySystem F. xi is a list listOfPortals_i is a CC
   --index=(a,b) such that tableLOP_a_b=listOfPortals is the correct list of portals
    --endIndex is 0 or 1, denoting the position of the end portal within listOfPortals. Once get here, return
--M: calls functions that add solutions to portals. also if a t value fails (can't jump anywhere), overwrites it with far away t (throws it out)
--E: performs MODIFIED dfs on directed graph (that it creates) until all avenues have been exhasted, or until stoppingCrit met
    --stopping crit is now reaching "the end of the path"
    --MODIFIED: i.e., not really dfs anymore, since once you at each (sol, t0) pair, you can only jump once now
--NOTE: indeed checks how far one could jump in theory
--FINISH HERE: do not ever createLower triangle yet

iterateOnce=(F, xi, i, indexP, endIndex)->{

    iterateOnceHelper=(F, xi, i, indexP, endIndex, curTriangleIndex)->{
        c:=getC((tableVertexIndexList#(indexP_0)#(indexP_1))@i); --is the C coordinate of vertex at indexP
        
        pades:=getApprox(F, xi,i, c);
        rad:=getD(pades);
        minD:=B1*rad;
        maxD:=B2*rad;
        
        --now get next point for here, if it's too big compared to maxD then go over to next triangle
        --otherwise then triangulate (either triangle we're currently in,
            --what about triangles that we don't yet know we're in, but are actually in? parent vertex might have more info here on vertexTC
        --at some point stop triangulating, just homotopy continue over
        
        --get distance on z-coords
        --curDToEnd:= getNorm( {((((tableVertexIndexList#(indexP_0)#(indexP_1)))@i).Points)#2, ((((tableVertexIndexList#(indexP_0)#(indexP_1)))@endIndex).Points)#2} );
        z1:=((((tableVertexIndexList#(indexP_0)#(indexP_1)))@i).Points)#2;
        
        --gets how many triangles this vertex is currently known to be in
        --ERROR: we have an error here, after a mini woohoo. basically @ throws an error here. fixed, needed createrLowerTriangle to add empty cppVectors to tableVertexTC
        theIterator:= ((tableVertexTC#(indexP_0)#(indexP_1))@i).theLength -1;
        --since this vertex is currently in a triangle that we know 
        if theIterator==-1 then (
            assert(false== (class(curTriangleIndex)===class(null)));--only should be null for north/south pole
            getNextPt(indexP, i, curTriangleIndex);--adds in current triangle
            theIterator=0;
        );
        
        while theIterator>=0 do (
            --print peek (((tableVertexTC#(indexP_0)#(indexP_1))@i)@theIterator);
            --ERROR: the @ error happens in the following line, after a mini woohoo happens. do this is now fixed (changed to >= in line above, =0 in line before)
            potNextTriangleIndex:= getNextPt(indexP, i, (((tableVertexTC#(indexP_0)#(indexP_1))@i)@theIterator).Index );
            potNextTriangle:= (tableTriangleList#(indexP_0)#(indexP_1))@potNextTriangleIndex;
            
            for potNextVertex in 0..2 do(
                potNextPoint:= (potNextTriangle.Vertices)#potNextVertex;
                --potDToEnd:=getNorm( {(potNextPoint.Points)#2, ((((tableVertexIndexList#(indexP_0)#(indexP_1)))@endIndex).Points)#2} );
                
                j:=potNextPoint.Index;
                c2:=getC((tableVertexIndexList#(indexP_0)#(indexP_1))@j);
                z2:=((((tableVertexIndexList#(indexP_0)#(indexP_1)))@j).Points)#2;
                
                --if closer to desired pole, and within pade range, and is valid
                --note that the <,> condition prevents you from calling inRGA on i==j
                if ((endIndex==0 and z1>z2) or (endIndex==1 and z1<z2)) and abs(c-c2)<maxD and ((tableVertexIndexList#(indexP_0)#(indexP_1))@j).valid==true then (
                    potentialZero:=inRGA(F, pades, c, j, indexP);
                    
                    if potentialZero_0==false and potentialZero_1==-1 then (print ("jumped to known place"); return {};);
                    if potentialZero_0 then (
                        --if reached then end, return the new zero that was found
                        if j==endIndex then (print("INDEED REACHED END PORTAL"); return potentialZero_1) ;

                        --if found newSol and should keep going, then calls on new solution pair
                        if verbose then print("mini woohoo");
                        --ERROR: have an "error: array index 1 out of bounds 0 .. 0" error that throws right after mini woohoo prints for the first time (muh other stuff run, printed before this)
                          --this gets thrown on using the @ operator
                          --is now fixed, see error comment in this while loop at the top
                        return iterateOnceHelper(F, potentialZero_1, j, indexP, endIndex, potNextTriangleIndex);

                        --above return: breaks dfs, i.e., only ever jump once for a given (sol, t0) pair
                    );--if
                );--if
            );--for
            --so did not successfully jump to any of the vertices in this triangle, for whatever reason, so we triangulate it here (only effects next run)
            --print("we have created a lower triangle now");
            createLowerTriangle(indexP, potNextTriangleIndex);
             
            theIterator=theIterator-1;
        );--while
        
        --overwrites t for being bad, now will never jump here, unless is start or end
        if i!=0 and i!=1 then ((tableVertexIndexList#(indexP_0)#(indexP_1))@i).valid=false;
        return homCtn(F, xi, i, indexP, endIndex);
    };

    return iterateOnceHelper(F, xi, i, indexP, endIndex,null);
};

------------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------------
--BELOW is homotopy continuation step
------------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------------

--homotopy continuation add on for proj stuff:
--R: Pade must be implemented (b/c uses a priori step size). Has same requirements as iteranteOnce
  --:also, F is of the form tA+(1-t)B
--M: none
--E: returns solution found at end of hom ctn

homCtn=(F, xi, i, indexP, endIndex)->{
    curT:=getC((tableVertexIndexList#(indexP_0)#(indexP_1))@i); --is the C coordinate of vertex at indexP
    curX:=point{xi};
    
    if verbose==true then print("have entered hom ctn, we have that curT is", curT, "curX is ", curX, "and then endIndex is", endIndex);
    
    --gets argument of curT
    --angle:=atan2(imaginaryPart(curT), realPart(curT)); 
    --NOTE: the arccos function measures the angle DOWN from the z-axis, rather than UP from the plane
    angle:=(pi/2)-arccos((((tableVertexIndexList#(indexP_0)#(indexP_1)))@i).Points);
    curT:=sin(angle)+ii*cos(angle);
    
    
    --ERROR: something eack going on here, we go from angle 0 to angle 1 in a single step (shouldn't be running homctn in the first place then)
      --bigger problem is that the sometime we just skip this else block (i.e., there is no "running homctn stepx" print statement, but there is a "indeed reached end portal via hom ctn")
      --should be solved now, was an issue with angle being taken wrt to xz-plane, instead of xy-plane
      
    --so moving up the sphere
    if endIndex==1 then (
        while (pi/2)-angle >epsilon do (
            --print("running homctn step1", angle);
            pades:=getApprox(F, curX.Coordinates,i, curT);
            rad:=getD(pades);
            minD:=max(B3*rad, epsilon/2);
            --print(curT, minD);
        
            --minD approximately arc length, and then arc length is equal to angle on unit circle
            angle=min(pi/2, angle+minD);
            
            curX=point{evaluateAt(pades, curT, sin(angle)+ii*cos(angle))};--may need to change how pades works, FINISH HERE
            curT=sin(angle)+ii*cos(angle);
            
            --print peek F;
            --print curT;
            specF=specializeSystem(point{{realPart(curT), imaginaryPart(curT)}}, F);
            for i from 1 to numNewton do (
                curX=newton(polySystem(specF),curX);
            );
        );
    --so moving down the sphere
    ) else (
        while angle>epsilon do (
            --print("running homctn step2", angle);
            pades:=getApprox(F, curX.Coordinates,i, curT);
            rad:=getD(pades);
            minD:=max(B3*rad, epsilon/2);
            --print(curT, minD);
            
            --minD approximately arc length, and then arc length is equal to angle on unit circle
            angle=max(0, angle-minD);
        
            curX=point{evaluateAt(pades, curT, sin(angle)+ii*cos(angle))};--may need to change how pades works, FINISH HERE
            curT=sin(angle)+ii*cos(angle);
            
            specF=specializeSystem(point{{realPart(curT), imaginaryPart(curT)}}, F);
            for i from 1 to numNewton do (
                curX=newton(polySystem(specF),curX);
            );
        );
    );

    timesCor=0;
    while(norm evaluate(polySystem(specF), curX)>0.00001 or timesCor<10) do ( curX=newton(polySystem(specF), curX); timesCor=timesCor+1);
    assert (norm evaluate(polySystem(specF), curX)<epsilon);--somehow this assertion is passing

    newSol=rounds(roundTo,curX.Coordinates);
    (tableSols#(indexP_0)#(indexP_1))#endIndex=(tableSols#(indexP_0)#(indexP_1))#endIndex +set{newSol};
    if verbose then print("INDEED REACHED END PORTAL (via hom ctn), sol is ",newSol);
    return newSol;
};

--homotopy continuation add on for find seed ONLY:
--R: Pade must be implemented (b/c uses a priori step size). Has same requirements as iteranteOnce
  --: if indexP==(-1,-1), is flag that endIndex is actually goalT (this flag is only used in finding seed)
  --:also, F is of the form tA+(1-t)B
--M: none
--E: returns solution found at end of hom ctn
--FINISH here: am not conviced this actually works, do need to check (is of lowest priority, though)

homCtnfs=(F, xi, curT, indexP, endIndex)->{
    --no longer pass in index of curT b/c want to throw that index out for failing
    --curT=(tableLOP#(indexP_0)#(indexP_1))#i;
    --print curT;
    
    if indexP==(-1,-1) then goalT=endIndex else goalT=(tableLOP#(indexP_0)#(indexP_1))#endIndex;
    
    curX=point{xi};
    
    --so moving left to right
    if curT<goalT then (
        while getNorm({curT},{goalT})>0.01 do (
            pades:=getApprox(F, curX.Coordinates,0, {curT});
            rad:=getD(pades);
            minD:=B3*rad;
            --print(curT, minD);
        
            curX=point{evaluateAt(pades, curT, min(curT+minD, goalT))};
            curT=min(curT+minD, goalT);
            
            specF=specializeSystem(point{{curT}}, F);
            for i from 1 to numNewton do (
                curX=newton(polySystem(specF),curX);
            );
        );
    --so moving right to left
    ) else (
        while getNorm({curT},{goalT})>0.01 do (
            pades:=getApprox(F, curX.Coordinates,0, {curT});
            rad:=getD(pades);
            minD:=B3*rad;
            --print(curT, minD);
        
            curX=point{evaluateAt(pades, curT, max(curT-minD, goalT))};
            curT=max(curT-minD, goalT);
            
            specF=specializeSystem(point{{curT}}, F);
            for i from 1 to numNewton do (
                curX=newton(polySystem(specF),curX);
            );
        );
    );

    timesCor=0;
    while(norm evaluate(polySystem(specF), curX)>0.00001 or timesCor<10) do ( curX=newton(polySystem(specF), curX); timesCor=timesCor+1);

    newSol=rounds(roundTo,curX.Coordinates);
    if indexP!=(-1,-1) then (tableSols#(indexP_0)#(indexP_1))#endIndex=(tableSols#(indexP_0)#(indexP_1))#endIndex +set{newSol};
    if verbose then print("INDEED REACHED END PORTAL (via hom ctn), sol is ",newSol);
    return newSol;
};

------------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------------
--BELOW IS triangulation stuff
------------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------------
--R: a cppVector arr and any element x
--M: the cppVector arr, both theCnts and theLength
--E: in amortized O(1) time, adds in element to end, returns index where element was added
--pushBack=method();
--pushBack(cppVector, Triangle):=(arr, x)->{
pushBack:=(arr, x)->{
    if arr.theLength < #(arr.theCnts) then (
        (arr.theCnts)#(arr.theLength)=x;
        a:=arr.theLength;
        arr.theLength=a+1;
    ) else (
       arr.theCnts= join(arr.theCnts, (arr.theLength: null));
       (arr.theCnts)#(arr.theLength)=x;
       a:=arr.theLength;
       arr.theLength=a+1;
    );

    return (arr.theLength)-1;
}
--makes it easier to grab elements from the vector
cppVector @ ZZ:=(arr,i)-> {
    if i>=arr.theLength then (for x in arr.theCnts do print peek x; print("i is ", i); print("the length is ",arr.theLength); assert(false);
    ) else ( return (arr.theCnts)#i;
    );
};
--debugging below
--arr1=new cppVector from {theCnts=>new MutableList, theLength=>0};
--print peek arr1;
--pushBack(arr1,{1});
--print peek arr1;

--R: nothing
--M: nothing
--E: returns a random point on the unit sphere in R^3
randomS2point=()->{
    a:=(-1)^(lift(mod(random(ZZ),2),ZZ)) *random(RR);
    b:=(-1)^(lift(mod(random(ZZ),2),ZZ)) *random(RR);
    c:=(-1)^(lift(mod(random(ZZ),2),ZZ)) *random(RR);
    d:=1.0/sqrt(a*a+b*b+c*c);
    --assert(a*a*d*d+b*b*d*d+c*c*d*d -1< 0.001);
    return {a*d, b*d, c*d};
};

--returns valid vertex that is midpoint of two vertices, with NULL index
--is normalized
Vertex + Vertex:=(x,y)-> new Vertex from {
    Points=>doMidpointCalc(x.Points#0,x.Points#1,x.Points#2,y.Points#0,y.Points#1,y.Points#2),
    valid=>true, 
    Index=>null
};

--R: list of 6 real numbers, in order of first triangle xyz, second triangle xyz
--M: none
--E: returns triple of xyz that represents midpoint between them, but raised to be on unit sphere in R^3
doMidpointCalc=(x0,x1,x2,y0,y1,y2)->{
    x:=0.5*(x0+y0);
    y:=0.5*(x1+y1);
    z:=0.5*(x2+y2);
    d:=1.0/sqrt(x*x+y*y+z*z);
    return {x*d, y*d, z*d};
};

--projects them down to xy axis, returns them in order so that they bound a regular polygon
  --i.e., the polygon does not intersect itself
--R: 4 points of type Vertex, sorted by x-coordinate (!)
--M: none
--E: returns 4 points sorted so that they bound a regular polygon
sortSquare=method();
sortSquare(Vertex, Vertex, Vertex, Vertex):=(a,b,c,d)->{
    assert(a.Points#0<= b.Points#0 and b.Points#0<= c.Points#0 and c.Points#0<= d.Points#0);
    s:=new MutableList from {a};
    e:=new MutableList from {d};
    
    --see if b, c lie above the line connecting ad
    --compute cross product of (ab,bd); (ac, cd); in 2d projection
    --if cross product is positive, then is below; negative then is above
    v:=[(d.Points#0)-(a.Points#0),(d.Points#1)-(a.Points#1)];
    vForB:=[(d.Points#0)-(b.Points#0), (d.Points#1)- (b.Points#1)];
    vForC:=[(d.Points#0)-(c.Points#0), (d.Points#1)- (c.Points#1)];
    
    if v_0 * vForB_1 - v_1 * vForB_0 < 0 then (--so b is below the line
        s=append(s, b);
    ) else (
        e=append(e, b);
    );
    
    if v_0 * vForC_1 - v_1* vForC_0 < 0 then (--so b is below the line
        s=append(s, c);
    ) else (
        e=append(e, c);
    );

    --now need to sort s (resp. e) be x-coordingate in increasing (resp. decreasing) order
    --do not need to sort s if it has 2 elements, since (s_0).Points#0 is least number, so already will be in inc order
    if #s>2 then (--just swap last 2 vertices if needed
        if (s#1).Points#0 > (s#2).Points#0 then (
            temp=s#1;
            s#1 =s#2;
            s#2 =temp;
        );
    );

    --now for e, this needs to be sorted in decreasing order 
    --(d was put at the beginning so again, only need to look at last 2 elements if #e>2
    if #e>2 then (--just swap last 2 vertices if needed
        if (e#1).Points#0 < (e#2).Points#0 then (
            temp=e#1;
            e#1 =e#2;
            e#2 =temp;
        );
    );
        
    return(toSequence(join(s,e)));
};

--creates initial 6 vertices (8 level zero triangles); puts them in levels
--R: none
--M: none
--E: returns mutable list of levels (a list of list of triangles), list of vertices, and
     --hashtable w/ key =index of vertice from the list, value= triangles the vertex lies in
initializeLevelZero=method();
initializeLevelZero(cppVector, cppVector, cppVector):=(triangleList, vertexIndexList, vertexTC)->{
    basePT:= new Vertex from {Points=> {0,0,-1} , valid=> true, Index=>0};
    pushBack(vertexIndexList,basePT);
    
    topPT:= new Vertex from {Points=> {0,0,1}, valid=> true, Index=>1}; 
    pushBack(vertexIndexList, topPT);
    
    a;b;c;d;
    --other 4 points which make up our initial triangulation
    pt1:=new Vertex from {Points=> randomS2point(), valid=> true, Index=>2}; 
    pushBack(vertexIndexList, pt1);
    
    pt2:=new Vertex from {Points=> randomS2point(), valid=> true, Index=>3}; 
    pushBack(vertexIndexList, pt2);
    
    --projecting down to xy-axis, have a be the left point and b be the right point
    if (pt1.Points)#0 < (pt2.Points)#0 then (a=pt1.Index; b=pt2.Index;) else (a=pt2.Index; b=pt1.Index;);
    
    pt3:=new Vertex from {Points=> randomS2point(), valid=> true, Index=>4}; 
    pushBack(vertexIndexList,pt3);
    if (pt3.Points)#0 < ((vertexIndexList@a).Points)#0 then (
        c=b; b=a; a=pt3.Index;
    ) else if pt3.Points#0<((vertexIndexList@b).Points)#0 then (
        c=b; b=4;
    ) else (
       c=4;
    );
    
    pt4:=new Vertex from {Points=> randomS2point(), valid=> true, Index=>5}; 
    pushBack(vertexIndexList, pt4);
    if pt4.Points#0 < ((vertexIndexList@c).Points)#0 then (
        d=c;
        if pt4.Points#0< ((vertexIndexList@b).Points)#0 then (
            c=b;
            if pt4.Points#0< ((vertexIndexList@a).Points)#0 then (
                b=a; a=pt4.Index;
            ) else (
                b=pt4.Index;
            );
        ) else (
            c=pt4.Index;
        );
    ) else (--is NOT left of c, so is right of c
      d=pt4.Index;
    );
    --now a,b,c,d are points sorted by their x coordinates
    
    --sorts these points so that their projection bounds a regular (non self intersecting polygon)
    {a,b,c,d}=sortSquare(vertexIndexList@a,vertexIndexList@b,vertexIndexList@c,vertexIndexList@d);
    
    t1:=new Triangle from {Vertices=> {basePT, a, b}, AT=>null, BT=>null, CT=>null, nT=>null, Index=>0};
    t2:=new Triangle from {Vertices=> {basePT, b, c}, AT=>null, BT=>null, CT=>null, nT=>null, Index=>1};
    t3:=new Triangle from {Vertices=> {basePT, c, d}, AT=>null, BT=>null, CT=>null, nT=>null, Index=>2};
    t4:=new Triangle from {Vertices=> {basePT, d, a}, AT=>null, BT=>null, CT=>null, nT=>null, Index=>3};
    t5:=new Triangle from {Vertices=> {topPT, a, b}, AT=>null, BT=>null, CT=>null, nT=>null, Index=>4};
    t6:=new Triangle from {Vertices=> {topPT, b, c}, AT=>null, BT=>null, CT=>null, nT=>null, Index=>5};
    t7:=new Triangle from {Vertices=> {topPT, c, d}, AT=>null, BT=>null, CT=>null, nT=>null, Index=>6};
    t8:=new Triangle from {Vertices=> {topPT, d, a}, AT=>null, BT=>null, CT=>null, nT=>null, Index=>7};
    
    --associate triangles to vertices by inclusion
    for i in 0..7 do (pushBack(vertexTC, new cppVector from {theCnts=> new MutableList from {}, theLength=> 0}));
    
    pushBack((vertexTC@0), t1);
    pushBack((vertexTC@0), t2);
    pushBack((vertexTC@0), t3);
    pushBack((vertexTC@0), t4);    
    
    pushBack((vertexTC@1), t5);
    pushBack((vertexTC@1), t6);
    pushBack((vertexTC@1), t7);
    pushBack((vertexTC@1), t8);
    --is very much a partial list of triangle containment
    --point is that we should only dynamically check where a point is, if we actually need to jump from that point
    
    --these 8 triangles make up the level 0 triangulation
    pushBack(triangleList, t1);
    pushBack(triangleList, t2);
    pushBack(triangleList, t3);
    pushBack(triangleList, t4);
    pushBack(triangleList, t5);
    pushBack(triangleList, t6);
    pushBack(triangleList, t7);
    pushBack(triangleList, t8);    
};

--R: triangleList@index is the triangle to be midpointed, that has NOT already been midpointed
--M: triangleList (adds in 4 new triangles), vertexIndexList (adds in 4 new vertexes)
   --: and triangle that's been midpointed (adds in pointers to children)
   --:adds 4 empty cpp vectors into tableVertexTC
--E: midpoints the given triangle, adding the 4 news ones to triangleList
createLowerTriangle=(indexP, i)->{
    assert(((tableTriangleList#(indexP_0)#(indexP_1))@i).AT==null);
    
    --get vertices of the triangle
    a:=((tableTriangleList#(indexP_0)#(indexP_1))@i).Vertices#0;
    b:=((tableTriangleList#(indexP_0)#(indexP_1))@i).Vertices#1;
    c:=((tableTriangleList#(indexP_0)#(indexP_1))@i).Vertices#2;
    
    --new* is labeled as opposite from vertex *
    newA:=b+c;
    newB:=a+c;
    newC:=a+b;
    
    curIndex=tableVertexIndexList#(indexP_0)#(indexP_1).theLength;
    newA.Index=curIndex;
    newB.Index=curIndex+1;
    newC.Index=curIndex+2;
    
    --adds these new vertices to the index list
    pushBack(tableVertexIndexList#(indexP_0)#(indexP_1), newA);
    pushBack(tableVertexIndexList#(indexP_0)#(indexP_1), newB);
    pushBack(tableVertexIndexList#(indexP_0)#(indexP_1), newC);
    
    
    --creates new triangles and adds them to the triangeList
    lastEntry=(tableTriangleList#(indexP_0)#(indexP_1)).theLength;
    
    --order is VERY IMPORTANT of how vertices get added in below
    --FIXED index issue below (next entry gets put in at lastEntry index, NOT lastEntry+1)
    t1:= new Triangle from {Vertices=> {a, newB, newC}, AT=>null, BT=>null, CT=>null, nT=>null, Index=>lastEntry};
    t2:= new Triangle from {Vertices=> {b, newB, newA}, AT=>null, BT=>null, CT=>null, nT=>null, Index=>lastEntry+1};
    t3:= new Triangle from {Vertices=> {c, newC, newA}, AT=>null, BT=>null, CT=>null, nT=>null, Index=>lastEntry+2};
    t4:= new Triangle from {Vertices=> {newA, newB, newC}, AT=>null, BT=>null, CT=>null, nT=>null, Index=>lastEntry+3};
    
    pushBack(tableTriangleList#(indexP_0)#(indexP_1), t1);
    pushBack(tableTriangleList#(indexP_0)#(indexP_1), t2);
    pushBack(tableTriangleList#(indexP_0)#(indexP_1), t3);
    pushBack(tableTriangleList#(indexP_0)#(indexP_1), t4);
    
    --links ''children'' triangles to ''parent'' triangle
    ((tableTriangleList#(indexP_0)#(indexP_1))@i).AT=t1;
    ((tableTriangleList#(indexP_0)#(indexP_1))@i).BT=t2;
    ((tableTriangleList#(indexP_0)#(indexP_1))@i).CT=t3;
    ((tableTriangleList#(indexP_0)#(indexP_1))@i).nT=t4;
    
    --adds 4 empty cpp vectors into tableVertexTC
    for i in 0..3 do (pushBack(tableVertexTC#(indexP_0)#(indexP_1), new cppVector from {theCnts=> new MutableList from {}, theLength=> 0}));
};


--CHECK: need something to update triangles that the point is in
--UPDATE (as in, has already been updated): adds in modified vertexTC if it is empty
  --: also, if not empty, adds in smallest triangle point is in (which includes overriding parent triangle)
--R: k gets correct row from table, i is index of point in vertexIndexList, j is index of triangle in triangleList
--M: adds smaller triangles to vertexTC@i
--E: updates vertexTC with up to numLevel-many triangles EDIT: only adds in smallest one now
--does like a DPS search but stops when hits a child node, returns index of that triangle
--point is to have O(numLevel) lookup once, and then O(1) afterward (until next triangulation)
  --will be iterating packwards through triangleTC at a given point, to find next point to (try to) jump to
  --smallest triangles will niavely be added at the back of the list
getNextPt=(indexP, i, j)->{
--formerly blank, i, j
--getNextPt(ZZ,ZZ,ZZ):=(a, b, i)->{
    --if this vertex is not yet known to be part of any triangle, push this triangle that it's a part of
    if ((tableVertexTC#(indexP_0)#(indexP_1))@i).theLength==0 then pushBack(((tableVertexTC#(indexP_0)#(indexP_1))@i), ((tableTriangleList#(indexP_0)#(indexP_1))@j));
    
    --as a bug check, make sure that vertex is actually in this triangle
    assert( ((((tableTriangleList#(indexP_0)#(indexP_1))@j).Vertices)#0).Index ==i or ((((tableTriangleList#(indexP_0)#(indexP_1))@j).Vertices)#1).Index ==i or ((((tableTriangleList#(indexP_0)#(indexP_1))@j).Vertices)#2).Index ==i);
    
    --if this triangle has no children, then we're done
    if class(((tableTriangleList#(indexP_0)#(indexP_1))@j).AT) === class(null) then return j;
    initialJ:=j;
    
    --observation to be made is that given a point in a triangulation,
    --there's only on possible triangle (AT, BT, CT) this point can EVER be in, in the sucessive triangulations
    orient:=null;
    if ((tableTriangleList#(indexP_0)#(indexP_1))@j).Vertices#0 === (tableVertexIndexList#(indexP_0)#(indexP_1))@i then (orient=1;
    ) else if ((tableTriangleList#(indexP_0)#(indexP_1))@j).Vertices#1 === (tableVertexIndexList#(indexP_0)#(indexP_1))@i then (orient=2;
    ) else if ((tableTriangleList#(indexP_0)#(indexP_1))@j).Vertices#2 === (tableVertexIndexList#(indexP_0)#(indexP_1))@i then (orient=3;
    ) else (
        print("error");
        print(i, j);
        print("The vertex we are at is", peek ((tableVertexIndexList#(indexP_0)#(indexP_1))@i));
        print("Triangle we're supposed to be in is", peek ((tableTriangleList#(indexP_0)#(indexP_1))@j).Vertices);
        assert(false);
    );
    
  --should be vertexTC@i, NOT vertexTC@0, right???
  while not(class(((tableTriangleList#(indexP_0)#(indexP_1))@j).AT) === class(null)) do(
      if orient==1 then (
         --pushBack((vertexTC@i), (triangleList@j).AT);
         j=(((tableTriangleList#(indexP_0)#(indexP_1))@j).AT).Index;
      ) else if orient ==2 then (
         --pushBack((vertexTC@i), (triangleList@j).BT);
         j=(((tableTriangleList#(indexP_0)#(indexP_1))@j).BT).Index;
      ) else (
         --pushBack((vertexTC@i), (triangleList@j).CT);
         j=(((tableTriangleList#(indexP_0)#(indexP_1))@j).CT).Index;
      );
  );

  --overrides parent if applicable, otherwise pushes smallest triangle point is in
  indexOfLastPushBack:= (((tableVertexTC#(indexP_0)#(indexP_1))@i).theLength)-1;
  if (((tableVertexTC#(indexP_0)#(indexP_1))@i)@(indexOfLastPushBack)).Index ==initialJ then (
      --has been checked, and works as it should, i.e., does NOT override the underlying class object
      (((tableVertexTC#(indexP_0)#(indexP_1))@i).theCnts)#indexOfLastPushBack= (tableTriangleList#(indexP_0)#(indexP_1))@j;
  ) else (
      pushBack(((tableVertexTC#(indexP_0)#(indexP_1))@i), ((tableTriangleList#(indexP_0)#(indexP_1))@j));
  );
  
  assert( ((((tableTriangleList#(indexP_0)#(indexP_1))@j).Vertices)#0).Index ==i or ((((tableTriangleList#(indexP_0)#(indexP_1))@j).Vertices)#1).Index ==i or ((((tableTriangleList#(indexP_0)#(indexP_1))@j).Vertices)#2).Index ==i);
  return j;
};


------------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------------
--BELOW is initial setup stuff
------------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------------

parametrizeFamily=(F, p0, p1)->{
    listOfVariables:=gens(ring(F));
    listOfParams:=parameters(F);
    combinedListOfVariables:=append(listOfVariables, "t"); 
    combinedListOfVariables=append(combinedListOfVariables, "s"); 
    everythingList:=join(listOfParams, combinedListOfVariables);
    everythingRing:=CC[everythingList];
    use everythingRing;
    --print everythingRing;
    tempF=sub(F, everythingRing);
    --print peek tempF;
   
    --now, create the actual parametrization
    
    newPolyList=new MutableList from equations(tempF);
    
    count=0;
    for gen in gens(everythingRing) do (
        if count< #listOfParams then (
            for k from 0 to #newPolyList-1 do (
                --print peek newPolyList#k;
                newPolyList#k = s*(sub(newPolyList#k, {gen=>p0_count}))+t*(sub(newPolyList#k, {gen=>p1_count}));
            );
             count=count+1;
        );
    );

    spec:=polySystem(toList(newPolyList));
    spec=sub(spec, CC[t,s][listOfVariables]);
    --print peek polySystem(spec);
    return polySystem(spec);
};

--R: m to be the dimension of the (multi)parameter space, m>0
--M: none
--E: returns a point on (S^1)^m
getRandomMegaPortal=(m)->{
    assert (m>0);
    megaPortal={};
    for i from 1 to m do megaPortal=append(megaPortal, exp(2*pi*ii*random(RR)));
    return megaPortal;
};

--R: n is number of portals, n>=3
--M: none
--E: returns list of CC, i.e., single parameter portals on the unit disk
   --first element is 1, b/c H(1)=p0, the system we want to find solutions to
   --also include 0, b/c H(0)=p1, the other system we care about
getRandomListOfPortals=(n)->{
    assert (n>=3);
    lop={1, 0};
    if (onDisk) then (
           for i from 2 to n do lop=append(lop, 0.5+sqrt(random(RR))*exp(2*pi*ii*random(RR)));
        ) else (
           for i from 2 to n do lop=append(lop, 0.5+exp(2*pi*ii*random(RR)));
        
        );
    
    return lop;  
};

--R: t0 to be initial portal (list), x0 to be inital solution (list). F the overall family
--M: megaLOP, megaSols, tableLOP, tableSOls, parametrizations
--E: initializes the above data structures to be ready for algorithm

initializeDataStructs=(F, x0, t0)->{

    --deal with global mega portals
    megaLOP={t0};
    --start from 2 b/c initial portal is the first one
    for indexer from 2 to numMega do (
        megaLOP=append(megaLOP, getRandomMegaPortal(#t0));
    );
    --if using custom, predeterminted megaLOP for debugging, PUT IT HERE (below)

    megaSols#0=set{rounds(roundTo,x0)};
    for i from 1 to numMega-1 do (
        megaSols#i=set {}; --initial empty set
    );
    
    
    --below has been changed since last algorithm
    
    tableTriangleList=table(numMega, numMega, (i,j)->
        (if i<j then (
            return new cppVector from {theCnts=>new MutableList from {}, theLength=>0}; 
        ) else (
            return 0;
        );)
    );
    

    tableVertexIndexList=table(numMega, numMega, (i,j)->
        (if i<j then (
            return new cppVector from {theCnts=>new MutableList from {}, theLength=>0};
        ) else (
            return 0;
        );)
    );

    tableVertexTC=table(numMega, numMega, (i,j)->
        (if i<j then (
            return new cppVector from {theCnts=>new MutableList from {}, theLength=>0}; 
        ) else (
            return 0;
        );)
    );

    for i in 0..(numMega-1) do(
        for j in 0..(numMega-1) do (
            if i<j then initializeLevelZero(tableTriangleList#i#j, tableVertexIndexList#i#j, tableVertexTC#i#j );--okay, so
        );
    );

    --above has been changed since last algorithm
 
    --for valid entries of the table, is a solutions hashTable corresponding to that "edge" (complex line)
    --for edges connecting to base portal, already have one solution to that system, so is added
    tableSols=table(numMega, numMega, (i,j)->
        (if i<j then (
            portals=new MutableHashTable;
            if i==0 then (
                portals#0=set{rounds(roundTo,x0)};
                for i from 1 to numMini-1 do (
                    portals#i=set {}; --initial empty set
                );
            
            ) else (
                for i from 0 to numMini-1 do (
                    portals#i=set {}; --initial empty set
                );
            
            );
            return portals;
        ) else (
            return 0;
        );)    
    );
    
    solsNotTracked=table(numMega, numMega, (i,j)->
        (if i<j or j<i then (
            if i==0 then return set{rounds(roundTo,x0)} else return set{};
        
        ) else (
            return 0;
        );)
    );

    --to make it mutable
    solsNotTracked=new MutableList from solsNotTracked;
    for k from 0 to numMega-1 do solsNotTracked#k=new MutableList from solsNotTracked#k;
    
    
     solsTracked=table(numMega, numMega, (i,j)->
        (if i<j or j<i then (
            return set{};
        
        ) else (
            return 0;
        );)
    );

    --to make it mutable
    solsTracked=new MutableList from solsTracked;
    for k from 0 to numMega-1 do solsTracked#k=new MutableList from solsTracked#k;  
    
    parametrizations=table(numMega, numMega, (i,j)->
        (if i<j then (
            return parametrizeFamily(F, megaLOP_i, megaLOP_j);
        ) else (
            return 0;
        );)    
    );
    
    
    if (verbose) then (
        print ("The list of parameters in the multiparameter space are ", megaLOP);
    );
    
    return;
};

------------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------------
--BELOW is running the entire algorithm
------------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------------


--R: F is a polySystem; megaPortals_i is index of vertex we're currently at
--M: nothing outside
--E: runs search algorithm (DFS search) on megaPortals

searchOuter=(F, i)->{
    
    for j from 0 to numMega-1 do(
        if i!=j then (
        
            --basically, parametrizations always happen from min(i,j) to max(i,j)
            --but they're bijective, so can go either way in them
            --so can go from portal_i to portal_j even if i>>j
            --just need to update portals correctly
            
            parametrizedF=parametrizations_(min(i,j))_(max(i,j));
            
            if verbose then (
                print("Running edge algo ", megaLOP_i, " to ", megaLOP_j, " via ", peek parametrizedF);
                print("Current sols to ", megaLOP_i, " are ", megaSols#i);
                print("Current sols to ", megaLOP_j, " are ", megaSols#j);
            );
            
            --going from i to j
            endIndex;
            if (i==min(i,j)) then endIndex=1 else endIndex=0;
            
            
            --runs edge algorithm on each solution to F_(portal_i) that hasn't been tracked yet
            partialSols=toList(solsNotTracked#i#j);
            print ("will be tracking ",toList(solsNotTracked#i#j));
            
            for x0 in partialSols do (
                --for x in solsNotTracked do print peek x;


                if verbose then print("Tracking ", x0, "from", megaLOP_i, "to", megaLOP_j);
                numTracked=numTracked+1;
            
                doReturn=false;
                newSol;
                if i==min(i,j) then (newSol=time iterateOnce(parametrizedF, x0, 0, (min(i,j),max(i,j)), endIndex);
                ) else (newSol=time iterateOnce(parametrizedF, x0, 1, (min(i,j),max(i,j)), endIndex););
                
                --x0 has now been tracked from ti to tj, so can remove from not tracked
                solsNotTracked#i#j=solsNotTracked#i#j -set{x0};
                solsTracked#i#j=solsTracked#i#j+set{x0};
                
                --if newSol hasn't been tracked before, then add it to be tracked
                for edges from 0 to numMega-1 do(
                    if j!=edges and newSol!={} and not(member(newSol, solsTracked#j#edges)) then solsNotTracked#j#edges =solsNotTracked#j#edges +set{newSol};
                );
            
                --for x in solsNotTracked do print peek x;

            );
            
            prevCount:=#(megaSols#j);
            
            --the min of i, j, is the one held in slot 0 of the edge solution hashtable
            megaSols#(min(i,j))=(megaSols#(min(i,j)))+(tableSols_(min(i,j))_(max(i,j)))#0;
            megaSols#(max(i,j))=(megaSols#(max(i,j)))+(tableSols_(min(i,j))_(max(i,j)))#1;
            
            if verbose then (
                print("Edge algorithm from has finished.");
                print("Current sols to ", megaLOP_i, " are now ", megaSols#i);
                print("Current sols to ", megaLOP_j, " are now ", megaSols#j);
            );
            
            --CHANGE ONCE HAVE OUTER STOPPINGCRIT
            --if (prevCount<  #(megaSols#j)) and not(stoppingCrit()) then (
            if (prevCount<  #(megaSols#j)) then (
                if verbose then (
                    print("Since solutions to ", megaLOP_j, " have increased, we now search from this portal onto the next edge");
                );
                searchOuter(F, j);
            );
        );
    ); 


};

--R: F is a polySystem; x0, t0 are lists such that F(x0,t0)=0
--M: nothing outside
--E: returns a list of sols (lists) that satisfy F(sols, t0)=0

solveAll=(F, x0, t0)->{
    --makes sure that the seed solutions pair is indeed legitimate
    assert (norm(flatten(toList(entries(evaluate(polySystem(specializeSystem(point{t0}, F)), point{x0})))))<epsilon);

    time initializeDataStructs(F,x0,t0);
    searchOuter(F, 0);
    print("Paths tracked is", numTracked);
    return megaSols#0;
    
};
tableTriangleList=table;
tableVertexIndexList=table;
tableVertexTC=table;
megaLOP={};
megaSols=new MutableHashTable;
parametrizations=table;
solsNotTracked;
solsTracked;
doReturn=false;
numTracked=0;

--R: F is a polysystem and p0 a parameter (list) s.t. F(x,p0)=0 is the system you want to find a solution to
  --:p\in C^m, x\in C^n, and m>=n (otherwise error)
  --: needs parametrizeFamiy and homCtn implemented
--M: nothing
--E: returns a solution x' to F(x,p0)=0
--note: first half it taken from Duff's algorithm

findSeed=(F, p0)->{
    n:=F.NumberOfVariables;
    m:=length(parameters(F));
    N:=F.NumberOfPolys;
    assert(m>=n);
    x0:=point{random(CC^1,CC^n)};
    I:=id_(CC^m);
    X:=random(CC^N,CC^0);
    b:=evaluate(F, point{matrix 0_(CC^m)}, x0);
    
    --creates X
    scan(m, i -> X = X | evaluate(F, point I_{i}, x0) - b);

    xp:=solve(X, -b, ClosestFit => true);
    K:=numericalKernel(X, Tolerance => 1e-5);
    xh:=K*random(CC^(numcols K), CC^1);
    p1:=point(xh+xp);
    
    assert(norm(evaluate(F, p1, x0))<0.01);
    
    --now homotopy continuation this solution over to F_p
    reducedF=parametrizeFamily(F, p1.Coordinates, p0);
    
    return homCtnfs(reducedF, x0.Coordinates, 1, (-1,-1), 0);

};

------------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------------
--BELOW are the variables and other stuff any user has access too
------------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------------

verbose=false;
numNewton=3; --max number of times to runs Newtons for
roundTo=2; --determines how many digits to round solutions to
epsilon=0.1; --main function is to how far away zeroGuesses and trueZeroes can be to stay in rga (and hom ctn closeness)
fwdErrB=0.1; --determines max fwdErr
numMini=100; --number of points to be in complex line rga case
numMega=3; --number of multiparameter points to sample from
onDisk=true;--if true then sample miniPortals from unit disk, otherwise sample from unit circle
numGauss=0; --number of times to correct power series approx, if <0 then don't correct (usually don't need to correct anyway)
L=1; --order of numerator in Pade
M=1; --order of denominator in Pade
B1=0; --lower bound scalar for jump zone annulus
B2=0.8; --upper bound scalar for jump zone annulus
B3=2;--jump size in hom ctn
    

-*
R=CC[a,b,c,d][x,y]
   inputSystem = {a*x+b*y, c*x*y+d};
root = {ii_CC, -1*ii_CC};
seed ={1,1,1,-1};
mo=solveAll(polySystem(inputSystem), root, seed);
print peek megaSols;
*-
 
 --the below system has 6 solutions
 
cyclicRoots = (n,kk) -> (
     R := kk[vars(0..n-1)];
     ideal apply(1..n-1, d-> sum(0..n-1, i -> product(d, k -> R_((i+k)%n)))) 
       + ideal(product gens R - 1))

parametrizedCyclic = n -> (
	S := gens cyclicRoots(n,CC);
	R := ring S;
	polys := flatten entries S;
	ind := flatten apply(#polys,i-> -- indices for parameters
		apply(exponents polys#i, t->(i,t))
		);
	AR := CC[apply(ind,i->A_i)][gens R];
	polysP := for i to #polys-1 list -- system with parameteric coefficients and same support 
	sum(exponents polys#i, t->A_(i,t)*AR_(t));
        print polys;
        print ind;
        print AR;
	polySystem transpose matrix {polysP}
);

polys = parametrizedCyclic 3;

time mo=solveAll(polys, {1, -0.5*ii*(-ii+sqrt(3)), 0.5*ii*(ii+sqrt(3))}, {1,1,1,1,1,1,1,-1});

--param=(#(parameters(polys))-1:1);
--param=toList(append(param, -1));

--oneSol=findSeed(polys, param);
--time mo=solveAll(polys, oneSol, param);


print length(toList(mo));
print peek megaSols;



-*
R=CC[p][x];
f=(x^3-3*x-p);
x0={0};
t0={0};
time mo=solveAll(polySystem{f}, x0, t0);
print peek megaSols;
--ERROR: have same solution set for too many systems. Seemed to have solved this after editing the homctn function (redid the anlge part)
*-

-*
needsPackage "PHCpack";
print time track(specializeSystem(point{{1,1,1,1,1,1,1,-1}}, polys), specializeSystem(point{{0.1,0.1,0.1,0.1,0.1,0.1,0.1,-0.1}}, polys), {(1, -0.5*ii*(-ii+sqrt(3)), 0.5*ii*(ii+sqrt(3)))});

*-
