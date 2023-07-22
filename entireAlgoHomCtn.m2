--works for multivariate, multiparameter systems of functions
--has assertion check to ensure seed solution pair is correct
--does forward error check as well, although prob not needed
--now takes random portals
--does variation of complete graph implementation-ish from Duff paper
--now have portals drawn from unit circle centered at 0.5 to make edges more symmetric
--have stopping criterion for edges
--need overall stopping criterion
--working on ensuring each edge indeed "tracks" all the way
--now does [L/M] Pade approximation, but does not yet take into account radius of convergence or error estimate
--cut dfs off, i.e., can only ever jump once for a given (sol, t0) pair
--homotopy continuation all the way, using Pade (and yes, only tracks new solutions)

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
    --print curPower;
    return curPower;
};

--R: a portal CC ti=listPortals_i and a solution (list) xi to the system F_xi, F a polySystem
--M: none
--E: returns an L/M Pade approximation that approximates F near (xi,ti)

getApprox=(F, xi, i, listOfPortals)->{
    ti = (listOfPortals_i)_CC;
    
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
    --print listOfPades;
    --print getD(listOfPades);
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


--apparently overloaded functions are not a thing in Macualay2
getNorm2=(list1)->{
    s=0;
    for x in (list1) do (
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
        if getNorm2({denom_1})<0.01 then (
            minD=1;
            break;
        ) else (
            dfromCenter=getNorm2({(-1.0*denom_0)/(denom_1)});
            if dfromCenter<minD then minD=dfromCenter;
        );
        
    
    );

    return minD;
};
--R: a polySystem F in \C[\vec{p}][\vec{x}], with start portal p0 and target portals p1, both lists
--M: none
--E: returns a polySystem in \C[t][\vec{x}], paameterized at t*p0+(1-t)*p1

parametrizeFamily=(F, p0, p1)->{

    listOfVariables=gens(ring(F));
    listOfParams=parameters(F);
    combinedListOfVariables=append(listOfVariables, t); 
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

    --index=(a,b) such that tableLOP_a_b=listOfPortals is the correct list of portals
    --endIndex is 0 or 1, denoting the position of the end portal within listOfPortals. Once get here, return
--M: calls functions that add solutions to portals
--E: performs MODIFIED dfs on directed graph (that it creates) until all avenues have been exhasted, or until stoppingCrit met
    --stopping crit is now reaching "the end of the path"
    --MODIFIED: i.e., not really dfs anymore, since once you at each (sol, t0) pair, you can only jump once now
--NOTE: indeed checks how far one could jump in theory

iterateOnce=(F, xi, i, indexP, endIndex)->{
    curT=(tableLOP_(indexP_0)_(indexP_1))_i;
    goalT=(tableLOP_(indexP_0)_(indexP_1))_endIndex;
    
    curX=point{xi};
    
    --so moving left to right
    if curT<goalT then (
        while getNorm({curT},{goalT})>0.01 do (
            pades:=getApprox(F, curX.Coordinates,0, {curT});
            rad:=getD(pades);
            minD:=B1*rad;
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
            minD:=B1*rad;
            --print(curT, minD);
        
            curX=point{evaluateAt(pades, curT, max(curT-minD, goalT))};
            curT=max(curT-minD, goalT);
            
            specF=specializeSystem(point{{curT}}, F);
            for i from 1 to numNewton do (
                curX=newton(polySystem(specF),curX);
            );
        );
    );
    
    newSol=rounds(roundTo,curX.Coordinates);
    (tableSols_(indexP_0)_(indexP_1))#endIndex=(tableSols_(indexP_0)_(indexP_1))#endIndex +set{newSol};
    return newSol;
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
--note: now have disk/circle of DIAMETER 1, as is should be
getRandomListOfPortals=(n)->{
    assert (n>=2);
    lop={1, 0};
    if (onDisk) then (
           for i from 3 to n do lop=append(lop, 0.5+0.5*sqrt(random(RR))*exp(2*pi*ii*random(RR)));
        ) else (
           for i from 3 to n do lop=append(lop, 0.5+0.5*exp(2*pi*ii*random(RR)));
        
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
            if verbose then print ("will be tracking ",toList(solsNotTracked#i#j));
            
            for x0 in partialSols do (
                --for x in solsNotTracked do print peek x;


                if verbose then print("Tracking ", x0, "from", megaLOP_i, "to", megaLOP_j);
            
                doReturn=false;
                newSol;
                if i==min(i,j) then (newSol=iterateOnce(parametrizedF, x0, 0, (min(i,j),max(i,j)), endIndex);
                ) else (newSol=iterateOnce(parametrizedF, x0, 1, (min(i,j),max(i,j)), endIndex););
                
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
    assert (getNorm2(flatten(toList(entries(evaluate(polySystem(specializeSystem(point{t0}, F)), point{x0})))))<epsilon);

    initializeDataStructs(F,x0,t0);
    searchOuter(F, 0);
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

verbose=true;
numNewton=5; --max number of times to runs Newtons for
roundTo=2; --determines how many digits to round solutions to
epsilon=0.2; --main function is to how far away zeroGuesses and trueZeroes can be to stay in rga
fwdErrB=0.2; --determines max fwdErr
orderDeg=1; --determines the order of the funciton approximation
e=0.2; --how far away from seed to sample points in funcApprox
numMini=2; --number of points to be in complex line rga case
numMega=3; --number of multiparameter points to sample from
onDisk=true;--if true then sample miniPortals from unit disk, otherwise sample from unit circle
stopEarly=true; --if true then stopCrit if reach ednpoint, otherwise no stopCrit
numGauss=1; --number of times to correct power series approx, if <0 then don't correct (usually don't need to correct anyway)
L=2; --order of numerator in Pade
M=1; --order of denominator in Pade
B1=0.5; --lower bound scalar for jump zone annulus
B2=1.2; --uper bound scalar for jump zone annulus

numHoms=0; --number of straight-line "homotopies" to do between p0 and fixed p1
    --is useless now, b/c gamma trick is not applicable
 

-*
R=CC[a,b,c,d][x,y]
   inputSystem = {a*x+b*y, c*x*y+d};
root = {ii_CC, -1*ii_CC};
seed ={1,1,1,-1};
mo=solveAll(polySystem(inputSystem), root, seed);
print peek megaSols;
*-
 
 
-*
  R=CC[p][x,y]
   inputSystem = {x^2+y^2-p,x^3-y^2+x};
root = point {{0.544,0.839_CC}};
seed =1;
mo=solveAll(polySystem(inputSystem), {0.544,0.839_CC}, {seed});
print peek megaSols;
*-

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

mo=solveAll(polys, {1, -0.5*ii*(-ii+sqrt(3)), 0.5*ii*(ii+sqrt(3))}, {1,1,1,1,1,1,1,-1});
print peek megaSols;


mega
