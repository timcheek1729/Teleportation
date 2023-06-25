installPackage "NumericalAlgebraicGeometry";

R=CC[t][x]
S=CC;       --the solution space
P=CC;       --the parameter space
use R;

roundTo=2;
epsilon=0.2;

listOfPortals={};
portals=new MutableHashTable;
F;

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

--R: a portal ti and a solution xi to the system F_xi
--M: none
--E: returns a function g(t) that approximates F near (xi,ti)
--note: later, will do sampling

getApprox=(xi, ti)->{
    Fx=diff(x_R,F);   --yes, standard form is diff(x,f) for differentiate f wrt x
    Ft=diff(t_R,F);
    
    --yes, standard form is sub(F,{t=>2}), which works
    --also, need to do division in CC, otherwise get weird fraction field stuff
    
    g=xi-sub(sub(Ft,{x_R=>xi,t=>ti}),CC)/sub(sub(Fx,{x_R=>xi,t=>ti}),CC)*(t-ti); 
    
    --print(g);
    
    return g;

};

--R: a function fti approximating around xi, ti; and a new parameter value tj; 
--M: if f approximates F_tj well, then appends Q_tj with new solution to F_tj 
--E: returns (bool, CC) pair.
    --if f does approximates F_tj well and finds a newSolution, then returns (true, newSolution)
    --otherwise false, with an integer indicator for whether newton errors, f a bad approx, or sol already known
--note: later, will check how far xj is from initGuess as you keep doing Newton's

inRGA=(fti, tj)-> {
    f=sub(sub(F,{t=>tj}), CC[x]);
    initGuess=sub(sub(fti,{t=>tj}),S);
    xj=point{{initGuess}};
    
    try(
        
        for i from 1 to 5 do (
            xj=newton(polySystem{f},xj);
            if ((abs(abs(sub(initGuess,CC))-abs(sub(xj.Coordinates_0,CC))))) >= epsilon then return (false,1);
        
        );
        
    ) then (
    
        roundedTj=rounds(roundTo, tj_CC);
        if ((abs(abs(sub(initGuess,CC))-abs(sub(xj.Coordinates_0,CC))))) < epsilon then (
        
            newSol=rounds(roundTo,(xj.Coordinates_0)_CC);
            if member(newSol, portals#roundedTj) then ( return (false, -1) ) else (
                portals#roundedTj=portals#roundedTj +set{newSol}; --adds xi solution to ti
                return (true, newSol);
            
            );
        
            
            
        ) else (
            return (false, 1);
        );
        
        
    ) else (
        
        return (false,0);
    );
};

---R:
--M:
--E: a placeholder function for stopping criterion

stoppingCrit=()->{
    return #(portals#roundedT0)==3;
};

--R: an (xi,ti) solution pair to the family F
--M: calls functions that add solutions to portals
--E: performs dfs on directed graph (that it creates) until all avenues have been exhasted, or until stoppingCrit met

iterateOnce=(xi, ti)->{
    g=getApprox(xi,ti);
    --print(g);
    --print(xi);
    --print(ti);
    for tj in listOfPortals do (
        if tj!=ti then (
        
            potentialZero=inRGA(g, tj);
            
            --print(potentialZero);
            
            if potentialZero_0 and not(stoppingCrit()) then (
                
                --if found newSol and should keep going, then calls on new solution pair
                
                --print("woohoo");
                iterateOnce(potentialZero_1, tj);
            );
        
        );
    );
};

--R
--M
--E

solveAll=(x0, t0, listOfPortals)->{
    roundedT0=rounds(roundTo, t0_CC);
    
    for pi in listOfPortals do (
        roundedPi=rounds(roundTo, pi_CC);
        portals#roundedPi= set {}; --initial empty set
    );

    iterateOnce(x0, t0);
    return portals#roundedT0;

};

l={0};
for i from 1 to 50 do (
    l=append(l, random(-4,4)*random(CC));
);


F=(x^3-3*x-t)_R;
x0=0;
t0=0;
--listOfPortals={0, 0.5+0.5*ii, 1+ii, 1.5+1.5*ii};
listOfPortals=l;
--listOfPortals={0, 0.5*ii, 1*ii, 0.5+1*ii, 1+ii, 1.5+ii, 2+ii, 2.5+ii, 3+ii, 3+0.5*ii, 3, 3-0.5*ii, 3-ii, 2.5-ii, 2-ii, 1.5-ii, 1-ii, 0.5-ii, -ii, 0.5};
solveAll(x0,t0,listOfPortals)

peek portals



