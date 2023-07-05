--works for multivariate, multiparameter systems of functions
--has assertion check to ensure seed solution pair is correct
--does forward error check as well, although prob not needed
--now takes random portals
--working on doing complete graph implementation-ish from Duff paper
--probbaly need inner and outer stopping crits, do this later
--now have portals drawn from unit circle centered at 0.5 to make edges more symmetric

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
--R: a portal CC ti=listPortals_i and a solution (list) xi to the system F_xi, F a polySystem
    --orderDeg is the order of the approximation, and e is how far to sample
--M: none
--E: returns a function g(t) that approximates F near (xi,ti)
--NEEDS EDITS: take in epsilon or be global variable, also need to be able to change order of approximation

getApprox=(inputSystem, xi, i, orderDeg, e, listOfPortals)->{
    root=point{xi};
    --SHOULD BELOW BE i OR NOT. DO NOT THINK SO, think is good
    seed = (listOfPortals_i)_CC;
    
    numVar = inputSystem.NumberOfPolys;

    ParamSystem = new MutableList;
    generatedParam = new MutableList;
    generatedRoots = new MutableList;

    for i from 0 to orderDeg-1 do {
        newParam = seed + e*exp(2*pi*ii*i/orderDeg);
        generatedParam = append(generatedParam,newParam);
        ParamSystem = append(ParamSystem, polySystem(specializeSystem(point {{newParam}}, inputSystem)));
     };

    for i from 0 to orderDeg-1 do {
        generatedRoots = append(generatedRoots,newton(ParamSystem#i,root));
    };

    generatedParam = prepend(seed,generatedParam);
    generatedRoots = prepend(root,generatedRoots);

    -- "coordinates point" convert a point into list

    lagBasis = new MutableList;
    for i from 0 to orderDeg do {
        comp = 1;
        for j from 0 to orderDeg do {
            if i != j then {
                comp = comp * (t-generatedParam#j)/(generatedParam#i-generatedParam#j);
            }
        };
        lagBasis = append(lagBasis,comp);
    };

    lagBasis = matrix(vector toList lagBasis);

    L = for i from 0 to numVar-1 list for i from 0 to orderDeg list 1+ii;
    M = mutableMatrix L;

    for i from 0 to numVar-1 do {
        for j from 0 to orderDeg do {
            M_(i,j) = (coordinates (generatedRoots#j))_i;
        };
    };

    M = matrix M;

    interpolatedSys = polySystem(flatten(entries(M*lagBasis)));

    return interpolatedSys;

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



--R: a function fti approximating around xi, ti; and a new parameter value tj=listOfPortals_j; polySystem F
   --ti is a CC, xi is a list
   --index=(a,b) such that listOfPortals=tableLOP_a_b, and (tableSols_(index_0)_(index_1))=portals
--M: if f approximates F_tj well, then appends Q_tj with new solution to F_tj 
--E: returns (bool, CC) pair.
    --if f does approximates F_tj well and finds a newSolution, then returns (true, newSolution)
    --otherwise false, with an integer indicator for whether newton errors, f a bad approx, or sol already known
--note: later, will check how far xj is from initGuess as you keep doing Newton's

inRGA=(F, fti, j, index)-> {
    tj=((tableLOP_(index_0)_(index_1))_j)_CC;
    specF=specializeSystem(point{{tj}}, F);
    
    initGuess=flatten(toList(entries(evaluate(fti,point{{tj}}))));
    xj=point{initGuess};
    try(
        
        for i from 1 to numNewton do (
            xj=newton(polySystem(specF),xj);
            if getNorm(initGuess, xj.Coordinates) >= epsilon then ( return (false,1););
        
        );
    ) then (
        fwdError=getNorm2(flatten(toList(entries(evaluate(polySystem(specializeSystem(point{{tj}}, F)), xj)))));
        --print fwdError;
        if (getNorm(initGuess, xj.Coordinates) < epsilon) and (fwdError<fwdErrB) then (
        
            newSol=rounds(roundTo,xj.Coordinates);
            if member(newSol, (tableSols_(index_0)_(index_1))#j) then ( return (false, -1) ) else (
                (tableSols_(index_0)_(index_1))#j=(tableSols_(index_0)_(index_1))#j +set{newSol}; --adds xi solution to ti
                return (true, newSol);
            
            );
        
            
            
        ) else (
            return (false, 1);
        );
        
        
    ) else (
        return (false,0);
    );
};

--R: j is an index of the current miniportal, i is the index of the end portal within the edge
--M:
--E: a placeholder function for stopping criterion
--note: VERY MUCH NEEDS EDITING

stoppingCrit=(j,i)->{
    if (stopEarly) then (
          if (j==i) then doReturn=true;
          return (j==i);
    ) else (
         return false;
    );
    
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

--R: an (xi,listOfPortals_i) solution pair to the family/polySystem F. xi is a list listOfPortals_i is a CC
    --index=(a,b) such that tableLOP_a_b=listOfPortals is the correct list of portals
    --endIndex is 0 or 1, denoting the position of the end portal within listOfPortals. Once get here, return
--M: calls functions that add solutions to portals
--E: performs dfs on directed graph (that it creates) until all avenues have been exhasted, or until stoppingCrit met
    --stopping crit is now reaching "the end of the path"

iterateOnce=(F, xi, i, index, endIndex)->{
    --if stoppingCrit() then(print "yeee"; return; );
    --AHHHHH!!! ABSOLUTELY MUST DO := , NOT =
    --otherwise M2 overwrites g upon each recursive step
    g:=getApprox(F, xi,i, orderDeg, e, tableLOP_(index_0)_(index_1));
    
    
    moved:=false;
    for j from 0 to numMini-1 do (
        if j!=i and not(doReturn) and not(stoppingCrit(i, endIndex)) then ( --so are looking at different portals and want to continue
            potentialZero:=inRGA(F, g, j, index);
            
            if potentialZero_0 then (
            
                --if found newSol and should keep going, then calls on new solution pair
                moved:=true;
                if verbose then print("mini woohoo");
                iterateOnce(F, potentialZero_1, j, index, endIndex);
            );
        
        );
    );
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
    for index from 2 to numMega do (
        megaLOP=append(megaLOP, getRandomMegaPortal(#t0));
    );

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
            
            
            --runs edge algorithm on each solution to F_(portal_i)
            partialSols=toList(megaSols#i);
            for x0 in partialSols do (
                doReturn=false;
                if i==min(i,j) then (iterateOnce(parametrizedF, x0, 0, (min(i,j),max(i,j)), endIndex);
                ) else (iterateOnce(parametrizedF, x0, 1, (min(i,j),max(i,j)), endIndex););
                
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
doReturn=false;

verbose=true;
numNewton=10; --max number of times to runs Newtons for
roundTo=2; --determines how many digits to round solutions to
epsilon=0.2; --main function is to how far away zeroGuesses and trueZeroes can be to stay in rga
fwdErrB=0.2; --determines max fwdErr
orderDeg=1; --determines the order of the funciton approximation
e=0.2; --how far away from seed to sample points in funcApprox
numMini=40; --number of points to be in complex line rga case
numMega=6; --number of multiparameter points to sample from
onDisk=true;--if true then sample miniPortals from unit disk, otherwise sample from unit circle
stopEarly=true; --if true then stopCrit if reach ednpoint, otherwise no stopCrit

numHoms=1; --number of straight-line "homotopies" to do between p0 and fixed p1
    --is useless now, b/c gamma trick is not applicable
    
   R=CC[a,b,c,d][x,y]
   inputSystem = {a*x+b*y, c*x*y+d};
root = {ii_CC, -1*ii_CC};
seed ={1,1,1,-1};
mo=solveAll(polySystem(inputSystem), root, seed);
print peek megaSols;

