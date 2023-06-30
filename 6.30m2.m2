
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

--rounds complex number to n decimal places
--used for storing approx zeroes/params in hashtable w/o unnecessary overlap
rounds=method();
rounds(ZZ,CC):=(n,c)->{
    a=realPart(c);
    b=imaginaryPart(c);
    a=sub(a,RR);
    b=sub(b,RR);
    return round(n, a)+round(n, b)*ii;
};

--R: a portal CC ti=listPortals_i and a solution (list) xi to the system F_xi, F a polySystem
--M: none
--E: returns a function g(t) that approximates F near (xi,ti)
--note: later, will do sampling
--WARNING: only works for a single polynomial, currently

getApprox=(F, xi, i)->{
    xi=xi_0;
    listF=equations(F);
    
    ti=listOfPortals_i;
    use ring listF_0;
    Fx=diff(x,listF_0);   --yes, standard form is diff(x,f) for differentiate f wrt x
    Ft=diff(t,listF_0);
    --yes, standard form is sub(F,{t=>2}), which works
    --also, need to do division in CC, otherwise get weird fraction field stuff
    
    if(sub(sub(Fx,{x=>xi,t=>ti}),CC)==0) then ( return xi+0*t;);
    g=xi-sub(sub(Ft,{x=>xi,t=>ti}),CC)/sub(sub(Fx,{x=>xi,t=>ti}),CC)*(t-ti); 
    
    return g;

};

--R: a function fti approximating around xi, ti; and a new parameter value tj=listOfPortals_j; polySystem F
   --ti is a CC, xi is a list
--M: if f approximates F_tj well, then appends Q_tj with new solution to F_tj 
--E: returns (bool, CC) pair.
    --if f does approximates F_tj well and finds a newSolution, then returns (true, newSolution)
    --otherwise false, with an integer indicator for whether newton errors, f a bad approx, or sol already known
--note: later, will check how far xj is from initGuess as you keep doing Newton's

inRGA=(F, fti, j)-> {
    tj=listOfPortals_j;
    specF=specializeSystem(point{{tj}}, F);
    
    --EVENTUALLY NEEDS CHANGING TO BE A POLYSYSTEM
    initGuess=sub(fti,{t=>tj});
    xj=point{{initGuess}};
    
    try(
        
        for i from 1 to 10 do (
            xj=newton(polySystem(specF),xj);
            if ((abs(abs(sub(initGuess,CC))-abs(sub(xj.Coordinates_0,CC))))) >= epsilon then return (false,1);
        
        );
    ) then (
    
        if ((abs(abs(sub(initGuess,CC))-abs(sub(xj.Coordinates_0,CC))))) < epsilon then (
        
            newSol={rounds(roundTo,(xj.Coordinates_0)_CC)};
            
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
                newPolyList#k = sub(newPolyList#k, {gen => (t)*(p0_k)+(1-t)*(p1_k)});
            
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
    g:=getApprox(F, xi,i);
    
    for j from 0 to #listOfPortals-1 do (
        if j!=i then ( --so are looking at different portals
            potentialZero=inRGA(F, g, j);
            
            if potentialZero_0 and not(stoppingCrit()) then (
            
                --if found newSol and should keep going, then calls on new solution pair
                
                --print("woohoo");
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
epsilon=0.2;

l={0};
--for i from 1 to 50 do (
--    l=append(l, random(-4,4)*random(CC));
--);

R=CC[p][x];
f=(x^3-3*x-p);
x0={0};
t0={0};
--listOfPortals={0, 0.5+0.5*ii, 1+ii, 1.5+1.5*ii};
--listOfPortals=l;
--listOfPortals={1, 0.5*ii, 1*ii, 0.5+1*ii, 1+ii, 1.5+ii, 2+ii, 2.5+ii, 3+ii, 3+0.5*ii, 3, 3.5,  3-0.5*ii, 3-ii, 2.5-ii, 2-ii, 1.5-ii, 1-ii, 0.5-ii, -ii, 0.5};
--listOfPortals={1, 0};

listOfPortals={1, 3, 0.5*ii, 1*ii, 0.5+1*ii, 1+ii, 1.5+ii, 2+ii, 2.5+ii, 3+ii, 3+0.5*ii, 3.5,  3-0.5*ii, 3-ii, 2.5-ii, 2-ii, 1.5-ii, 1-ii, 0.5-ii, -ii, 0.5};

mo=solveAll(polySystem{f}, x0,t0,listOfPortals, {{1}});
print peek portals;





