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
rounds=method();
rounds:=(n,listL)->{
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
    newF={};
    t=(parameters(F))_0;
    for func in entries(F.PolyMap) do (
        --just subs in t+t0 in for t
        --newF=append(newF, sub((func_0), {((parameters(F))_0) => (((parameters(F))_0)+t0)}));
        newF=append(newF, sub((func_0), {t=>t+t0}));
    );
    newF=polySystem(newF);
    
    curOrd=0;
    --to ensure elements of sol lie in CC[t]
    curPower=apply(sol, i-> i+0*t);    
    
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

--R: a portal CC ti=listPortals_i and a solution (list) xi to the system F_xi, F a polySystem
--M: none
--E: returns an L/M Pade approximation that approximates F near (xi,ti)

getApprox=(F, xi, i, listOfPortals)->{
    ti = (listOfPortals#i)_CC;
    
    psApprox=getPSApprox(F, ti, xi, L+M);
    
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

--R: to lists of complex numbers
--M: none
--E: returns norm of their difference

getNorm=(list1, list2)->{
    s=0;
    for x in (list1-list2) do (
        s=s+(realPart(x))^2+(imaginaryPart(x))^2;
    );
    return sqrt(s);
};

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

--R: a function fti approximating around xi0, ti0; and a new parameter value tj=listOfPortals_j; polySystem F
   --ti is a CC, xi is a list
   --index=(a,b) such that listOfPortals=tableLOP_a_b, and (tableSols_(index_0)_(index_1))=portals
--M: if f approximates F_tj well, then appends Q_tj with new solution to F_tj 
--E: returns (bool, CC) pair.
    --if f does approximates F_tj well and finds a newSolution, then returns (true, newSolution)
    --otherwise false, with an integer indicator for whether newton errors, f a bad approx, or sol already known
--note: indeed checks how far xj is from initGuess as you keep doing Newton's, and also checks fwdError at end
--note: slight discrepancies between this and what's written in the paper, need to edit

inRGA=(F, fti, i0, j, indexP)-> {
    tj=((tableLOP#(indexP_0)#(indexP_1))#j)_CC;
    ti=((tableLOP#(indexP_0)#(indexP_1))#i0)_CC;
    specF=specializeSystem(point{{tj}}, F);
    
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
        fwdError=norm(flatten(toList(entries(evaluate(polySystem(specializeSystem(point{{tj}}, F)), xj)))));
        --print fwdError;
        if (getNorm(initGuess, xj.Coordinates) < epsilon) and (fwdError<fwdErrB) then (
        
            newSol=rounds(roundTo,xj.Coordinates);
            if member(newSol, (tableSols_(indexP_0)_(indexP_1))#j) then ( return (false, -1) ) else (
                (tableSols_(indexP_0)_(indexP_1))#j=(tableSols_(indexP_0)_(indexP_1))#j +set{newSol}; --adds xi solution to ti
                return (true, newSol);
            
            );
        
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

iterateOnce=(F, xi, i, indexP, endIndex)->{

    --rather than considering all t values at every jump, we eliminate points we already know are "behind" us 
    iterateOnceHelper=(F, xi, i, indexP, endIndex, listOfIndices, lastIndex)->{
        --AHHHHH!!! ABSOLUTELY MUST DO := , NOT =
        --otherwise M2 overwrites g upon each recursive step
        pades:=getApprox(F, xi,i, tableLOP#(indexP_0)#(indexP_1));
        rad:=getD(pades);
        minD:=B1*rad;
        maxD:=B2*rad;

        distanceToEnd:=getNorm({(tableLOP#(indexP_0)#(indexP_1))#i}, {(tableLOP#(indexP_0)#(indexP_1))#endIndex});
        
        nextList:=new MutableList from (numMini:null);
        nextLastIndex:=0;

        for temp from 0 to lastIndex-1 do (
            j=listOfIndices#temp;
            --so if reachable, would want to jump, so is a candidate
            if j!=i and getNorm({(tableLOP#(indexP_0)#(indexP_1))#j}, {(tableLOP#(indexP_0)#(indexP_1))#endIndex})<distanceToEnd then (
                nextList#nextLastIndex=j;
                nextLastIndex=nextLastIndex+1;
                distanceBetween:=getNorm({(tableLOP#(indexP_0)#(indexP_1))#i}, {(tableLOP#(indexP_0)#(indexP_1))#j});
                
                --now see if actually reachable
                if minD<distanceBetween and distanceBetween<maxD then (
                    potentialZero:=inRGA(F, pades, i, j, indexP);
                    if potentialZero_0==false and potentialZero_1==-1 then (print ("jumped to known place"); return {};);
                    if potentialZero_0 then (
                        --if reached then end, return the new zero that was found
                        if j==endIndex then (print("INDEED REACHED END PORTAL"); return potentialZero_1) ;

                        --if found newSol and should keep going, then calls on new solution pair
                        if verbose then print("mini woohoo");
                        return iterateOnceHelper(F, potentialZero_1, j, indexP, endIndex, nextList, nextLastIndex);

                        --above return: breaks dfs, i.e., only ever jump once for a given (sol, t0) pair
                    );--if
                );--if
            );--if
        );--for
        
        start; if lastIndex==0 then start =0 else start=listOfIndices#(lastIndex-1)+1;
        
        for j from start to numMini-1 do(
            if j!=i and getNorm({(tableLOP#(indexP_0)#(indexP_1))#j}, {(tableLOP#(indexP_0)#(indexP_1))#endIndex})<distanceToEnd then (
                nextList#nextLastIndex=j;
                nextLastIndex=nextLastIndex+1;
                distanceBetween:=getNorm({(tableLOP#(indexP_0)#(indexP_1))#i}, {(tableLOP#(indexP_0)#(indexP_1))#j});

                if minD<distanceBetween and distanceBetween<maxD then (
                    potentialZero:=inRGA(F, pades, i, j, indexP);
                    if potentialZero_0==false and potentialZero_1==-1 then (print ("jumped to known place"); return {};);
                    if potentialZero_0 then (
                        if j==endIndex then (print("INDEED REACHED END PORTAL"); return potentialZero_1) ;
                        if verbose then print("mini woohoo");
                        return iterateOnceHelper(F, potentialZero_1, j, indexP, endIndex, nextList, nextLastIndex);
                    );--if
                    );--if
            );--if
        );--for
        --print((tableLOP#(indexP_0)#(indexP_1))#i, getNorm({(tableLOP#(indexP_0)#(indexP_1))#i}, {(tableLOP#(indexP_0)#(indexP_1))#endIndex}));
    
        --so didn't move
        curT:=(tableLOP#(indexP_0)#(indexP_1))#i;
        --overwrites t for being bad, now will never jump here, unless is start or end
        if i!=0 and i!=1 then (tableLOP#(indexP_0)#(indexP_1))#i=-10;
        return homCtn(F, xi, curT, indexP, endIndex);
        

    };

    return iterateOnceHelper(F, xi, i, indexP, endIndex, {},0);
};

--homotopy continuation add on:
--R: Pade must be implemented (b/c uses a priori step size). Has same requirements as iteranteOnce
  --: if indexP==(-1,-1), is flag that endIndex is actually goalT
  --:also, F is of the form tA+(1-t)B
--M: none
--E: returns solution found at end of hom ctn

homCtn=(F, xi, curT, indexP, endIndex)->{
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

--R: a polySystem F in \C[\vec{p}][\vec{x}], with start portal p0 and target portals p1, both lists
--M: none
--E: returns a polySystem in \C[t][\vec{x}], paameterized at t*p0+(1-t)*p1

parametrizeFamily=(F, p0, p1)->{

    listOfVariables=gens(ring(F));
    listOfParams=parameters(F);
    combinedListOfVariables=append(listOfVariables, "t"); 
    everythingList=join(listOfParams, combinedListOfVariables);
    everythingRing=CC[everythingList];
    use everythingRing;
   
    tempF=sub(F, everythingRing);
   
    --now, create the actual parametrization
    
    newPolyList=new MutableList from equations(tempF);
    
    count=0;
    for gen in gens(everythingRing) do (
        if count< #listOfParams then (
            for k from 0 to #newPolyList-1 do (
                newPolyList#k = sub(newPolyList#k, {gen => (t)*(p0_count)+(1-t)*(p1_count)});
            
            );
             count=count+1;
        );
    );

    spec=polySystem(toList(newPolyList));
    spec=sub(spec, CC[t][listOfVariables]);

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

    megaLOP={t0};
    --start from 2 b/c initial portal is the first one
    for indexer from 2 to numMega do (
        megaLOP=append(megaLOP, getRandomMegaPortal(#t0));
    );
    --if using cutom, predeterminted megaLOP for debugging, PUT IT HERE (below)

    megaSols#0=set{rounds(roundTo,x0)};
    for i from 1 to numMega-1 do (
        megaSols#i=set {}; --initial empty set
    );
    
    --for valid entries of the table, is a list of portals corresponding to that "edge" (complex line)
    tableLOP=table(numMega, numMega, (i,j)->
        (if i<j then (
            return getRandomListOfPortals(numMini);
        ) else (
            return 0;
        );)
    );

    --have to make everything mutable to throw out "bad" portals
    tableLOP=new MutableList from tableLOP;
    for k from 0 to numMega-1 do tableLOP#k=new MutableList from tableLOP#k;
    for i from 0 to numMega-1 do for j from 0 to numMega-1 do(
        if i<j then (
            (tableLOP#i)#j =new MutableList from (tableLOP#i)#j;
        );
    );

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
tableLOP=table;
tableSols=table;
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
    
    return homCtn(reducedF, x0.Coordinates, 1, (-1,-1), 0);

};

verbose=false;
numNewton=3; --max number of times to runs Newtons for
roundTo=2; --determines how many digits to round solutions to
epsilon=0.1; --main function is to how far away zeroGuesses and trueZeroes can be to stay in rga
fwdErrB=0.1; --determines max fwdErr
numMini=100; --number of points to be in complex line rga case
numMega=3; --number of multiparameter points to sample from
onDisk=true;--if true then sample miniPortals from unit disk, otherwise sample from unit circle
numGauss=0; --number of times to correct power series approx, if <0 then don't correct (usually don't need to correct anyway)
L=1; --order of numerator in Pade
M=1; --order of denominator in Pade
B1=0; --lower bound scalar for jump zone annulus
B2=0.8; --upper bound scalar for jump zone annulus
B3=0.7;--jump size in hom ctn
    

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

--time mo=solveAll(polys, {1, -0.5*ii*(-ii+sqrt(3)), 0.5*ii*(ii+sqrt(3))}, {1,1,1,1,1,1,1,-1});

param=(#(parameters(polys))-1:1);
param=toList(append(param, -1));

oneSol=findSeed(polys, param);
time mo=solveAll(polys, oneSol, param);
print length(toList(mo));
print peek megaSols;



-*
R=CC[p][x];
f=(x^3-3*x-p);
x0={0};
t0={0};
mo=solveAll(polySystem{f}, x0, t0);
print peek megaSols;

*-

-*
needsPackage "PHCpack";
print time track(specializeSystem(point{{1,1,1,1,1,1,1,-1}}, polys), specializeSystem(point{{0.1,0.1,0.1,0.1,0.1,0.1,0.1,-0.1}}, polys), {(1, -0.5*ii*(-ii+sqrt(3)), 0.5*ii*(ii+sqrt(3)))});

*-
