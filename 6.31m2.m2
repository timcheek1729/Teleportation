--works for multivariate, multiparameter systems of functions
--has assertion check to ensure seed solution pair is correct
--does forward error check as well, although prob not needed
--no longer does gamma trick, b/c messes up intermediate line/planar systems
  --actually, sols don't need to be conjugates b/c deal w/ complex functions
  --may introduce gamma trick later
--debugged, and now works for systems
installPackage "NumericalAlgebraicGeometry";
installPackage "MonodromySolver";

listOfPortals={};
portals=new MutableHashTable;

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

getApprox=(inputSystem, xi, i, orderDeg, e)->{
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
        s=s+realPart(x)^2+imaginaryPart(x)^2;
    );
    return sqrt(s);
    

};


--apparently overloaded functions are not a thing in Macualay2
getNorm2=(list1)->{
    s=0;
    for x in (list1) do (
        s=s+realPart(x)^2+imaginaryPart(x)^2;
    );
    return sqrt(s);
    

};

--R: a function fti approximating around xi, ti; and a new parameter value tj=listOfPortals_j; polySystem F
   --ti is a CC, xi is a list
--M: if f approximates F_tj well, then appends Q_tj with new solution to F_tj 
--E: returns (bool, CC) pair.
    --if f does approximates F_tj well and finds a newSolution, then returns (true, newSolution)
    --otherwise false, with an integer indicator for whether newton errors, f a bad approx, or sol already known
--note: later, will check how far xj is from initGuess as you keep doing Newton's

inRGA=(F, fti, j)-> {
    tj=(listOfPortals_j)_CC;
    specF=specializeSystem(point{{tj}}, F);
    
    initGuess=flatten(toList(entries(evaluate(fti,point{{tj}}))));
    xj=point{initGuess};
    try(
        
        for i from 1 to 10 do (
            xj=newton(polySystem(specF),xj);
            if getNorm(initGuess, xj.Coordinates) >= epsilon then ( return (false,1););
        
        );
    ) then (
        fwdError=getNorm2(flatten(toList(entries(evaluate(polySystem(specializeSystem(point{{tj}}, F)), xj)))));
        --print fwdError;
        if (getNorm(initGuess, xj.Coordinates) < epsilon) and (fwdError<epsilon) then (
        
            newSol=rounds(roundTo,xj.Coordinates);
            if member(newSol, portals#j) then ( return (false, -1) ) else (
                portals#j=portals#j +set{newSol}; --adds xi solution to ti
                return (true, newSol);
            
            );
        
            
            
        ) else (
            return (false, 1);
        );
        
        
    ) else (
        
        return (false,0);
    );
};

--R:
--M:
--E: a placeholder function for stopping criterion
--note: VERY MUCH NEEDS EDITING

stoppingCrit=()->{
    return #(portals#0)==3;
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
--M: calls functions that add solutions to portals
--E: performs dfs on directed graph (that it creates) until all avenues have been exhasted, or until stoppingCrit met

iterateOnce=(F, xi, i)->{
    --AHHHHH!!! ABSOLUTELY MUST DO := , NOT =
    --otherwise M2 overwrites g upon each recursive step
    g:=getApprox(F, xi,i, 1, 0.2);
    
    for j from 0 to #listOfPortals-1 do (
        if j!=i then ( --so are looking at different portals
            potentialZero=inRGA(F, g, j);
            
            if potentialZero_0 and not(stoppingCrit()) then (
            
                --if found newSol and should keep going, then calls on new solution pair
                
                print("woohoo");
                iterateOnce(F, potentialZero_1, j);
            );
        
        );
    );
};

--R: F is a polySystem; x0, t0 are lists such that F(x0,t0)=0
   --megaPortals is a list of portals (lists) in the multiparameter space
   --listOfPortals is list of CC, are the portals to be searched once reduce to a line
   --t0 must not be in megaPortals, 1 must be first element in listOfPortals
--M: nothing outside
--E: returns a list of sols (lists) that satisfy F(sols, t0)=0

solveAll=(F, x0, t0, listOfPortals, megaPortals)->{
    --makes sure that the seed solutions pair is indeed legitimate
    assert (getNorm2(flatten(toList(entries(evaluate(polySystem(specializeSystem(point{t0}, F)), point{x0})))))<epsilon);

    portals#0=set {};
    
    for multiparamPortals in megaPortals do (
        if(stoppingCrit()) then (
            break;
        );
    
        parametrizedF=parametrizeFamily(F, t0, multiparamPortals);
        --only the "base" system will remain fixed by the straight line "homotopy" after each iteration
        --thus, we clear out all other portals, but keep the first portal
        for i from 1 to #listOfPortals-1 do (
            portals#i=set {}; --initial empty set
        );
        iterateOnce(parametrizedF, x0, 0);
    );

    return portals#0;

};

roundTo=2;
epsilon=0.5;

l={1};
for i from 1 to 50 do (
    l=append(l, random(-4,4)*random(CC));
);


R=CC[p][x];
f=(x^3-3*x-p);
x0={0};
t0={0};

--listOfPortals={0, 0.5+0.5*ii, 1+ii, 1.5+1.5*ii};
--listOfPortals=l;
--listOfPortals={1, 0.5*ii, 1*ii, 0.5+1*ii, 1+ii, 1.5+ii, 2+ii, 2.5+ii, 3+ii, 3+0.5*ii, 3, 3.5,  3-0.5*ii, 3-ii, 2.5-ii, 2-ii, 1.5-ii, 1-ii, 0.5-ii, -ii, 0.5};
--listOfPortals={1, 0};
listOfPortals={1, 3, 0.5*ii, 1*ii, 0.5+1*ii, 1+ii, 1.5+ii, 2+ii, 2.5+ii, 3+ii, 3+0.5*ii, 3.5,  3-0.5*ii, 3-ii, 2.5-ii, 2-ii, 1.5-ii, 1-ii, 0.5-ii, -ii, 0.5};
mo=solveAll(polySystem{f}, x0,t0,listOfPortals, {{10*ii}});
print peek portals;




